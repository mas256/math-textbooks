#!/usr/bin/env python3
"""Generate a new Lv1-5 problem bank with the locked Rust engine and Lean.

Each run draws a fresh seed, so the problems change on every regeneration.
The result replaces recurrence/bank/ only after the engine's own check passes.
"""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import secrets
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
BANK = ROOT / "recurrence" / "bank"
LOCK = json.loads((ROOT / "recurrence" / "engine-lock.json").read_text())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine-root", type=Path, required=True,
                        help="checkout of the locked engine commit")
    parser.add_argument("--bank-binary", type=Path, required=True,
                        help="built recurrence-bank executable")
    parser.add_argument("--per-level", type=int, default=30)
    parser.add_argument("--seed", type=int, help="reproduce a specific bank (default: random)")
    parser.add_argument("--jobs", type=int)
    args = parser.parse_args()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=args.engine_root, text=True).strip()
    if revision != LOCK["revision"]:
        raise SystemExit(f"Engine checkout {revision} differs from the lock {LOCK['revision']}")
    seed = args.seed if args.seed is not None else secrets.randbits(64)
    with tempfile.TemporaryDirectory() as temporary:
        out = Path(temporary) / "bank"
        command = [str(args.bank_binary), "generate", "--seed", str(seed), "--out", str(out),
                   "--per-level", str(args.per_level), "--lean-dir", str(args.engine_root / "lean")]
        if args.jobs:
            command += ["--jobs", str(args.jobs)]
        subprocess.run(command, check=True)
        manifest_path = out / "manifest.json"
        manifest = json.loads(manifest_path.read_text())
        if manifest["engine_version"] != LOCK["version"]:
            raise SystemExit("The engine version differs from the lock")
        manifest.update({
            "engine_repository": LOCK["repository"],
            "engine_revision": revision,
            "generated_at": datetime.now(timezone.utc).replace(microsecond=0).isoformat(),
            "run_id": os.environ.get("GITHUB_RUN_ID"),
        })
        manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
        subprocess.run([str(args.bank_binary), "check", "--bank", str(out)], check=True)
        if BANK.exists():
            shutil.rmtree(BANK)
        shutil.copytree(out, BANK)
    print(f"Replaced recurrence/bank with {manifest['count']} problems (seed {seed})")


if __name__ == "__main__":
    main()
