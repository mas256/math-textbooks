#!/usr/bin/env python3
"""Import the pinned browser engine without rebuilding or modifying its assets."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parents[2]
RECURRENCE = ROOT / "recurrence"
LOCK = json.loads((RECURRENCE / "engine-lock.json").read_text())


def prepare(engine_root: Path, write_entry: bool) -> None:
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=engine_root, text=True
    ).strip()
    if revision != LOCK["revision"]:
        raise ValueError(f"Engine revision mismatch: {revision}")
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Expected a complete engine commit SHA")
    version = tomllib.loads((engine_root / "Cargo.toml").read_text())["package"]["version"]
    if version != LOCK["version"]:
        raise ValueError(f"Engine version mismatch: {version}")
    source = engine_root / "browser"
    # A modified local checkout must not be published under a trusted commit ID.
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--", "browser", "Cargo.toml"],
                   cwd=engine_root, check=True, stdout=subprocess.DEVNULL)
    names = ["engine.js", "browser-runtime.js", "app.js", "style.css", "favicon.svg"]
    names += [str(p.relative_to(source)) for p in sorted((source / "vendor").rglob("*")) if p.is_file()]
    tracked = set(subprocess.check_output(
        ["git", "ls-files", "browser"], cwd=engine_root, text=True
    ).splitlines())
    if any("browser/" + name not in tracked for name in names):
        raise ValueError("Untracked files found in the engine assets")
    files = {name: hashlib.sha256((source / name).read_bytes()).hexdigest() for name in names}
    prefix = f"./engine/{revision}/"
    entry = (source / "index.html").read_text()
    entry = entry.replace('<meta charset="UTF-8">',
                          '<meta charset="UTF-8">\n  <script src="./lab-entry.js"></script>')
    entry = re.sub(r'((?:src|href)=")\./([^"\s]+)(")',
                   lambda m: m[1] + prefix + m[2] + m[3]
                   if m[2] not in ("index.html", "lab-entry.js") else m[0], entry)
    entry = entry.replace('<link rel="stylesheet" href="' + prefix + 'style.css">',
                          '<link rel="stylesheet" href="' + prefix + 'style.css">\n  <link rel="stylesheet" href="./lab-host.css">')
    entry = entry.replace('href="./index.html"', 'href="./"')
    entry = entry.replace('</head>',
        f'  <meta name="recurrence-engine-revision" content="{revision}">\n'
        f'  <meta name="recurrence-engine-version" content="{version}">\n</head>')
    entry = entry.replace('  <main class="page-shell">',
        '  <nav class="host-navigation" aria-label="教材への移動">'
        '<a href="../">数学書の本棚</a>'
        '<a href="./textbook.html">教材問題・Lv6・14問セット</a></nav>\n'
        '  <main class="page-shell">')
    target_entry = RECURRENCE / "index.html"
    if write_entry:
        target_entry.write_text(entry)
    elif target_entry.read_text() != entry:
        raise ValueError("index.html differs from the pinned engine; run prepare-lab.py --write-entry")
    engine = RECURRENCE / "engine"
    if engine.exists():
        shutil.rmtree(engine)
    target = engine / revision
    for name in names:
        destination = target / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / name, destination)
    manifest = {**LOCK, "assets": files,
                "source_entry_sha256": hashlib.sha256(entry.encode()).hexdigest(),
                "verification": "browser_finite_checks_not_lean"}
    (target / "provenance.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
    print(f"Prepared recurrence engine {version} @ {revision}: {len(files)} unchanged assets")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine-root", type=Path, required=True)
    parser.add_argument("--write-entry", action="store_true")
    args = parser.parse_args()
    prepare(args.engine_root.resolve(), args.write_entry)
