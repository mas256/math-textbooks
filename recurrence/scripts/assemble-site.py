#!/usr/bin/env python3
"""Assemble the same static files tested locally and uploaded to Pages."""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
# A regeneration run deploys the bank commit it created, not the dispatch commit.
revision = os.environ.get("SITE_REVISION") or os.environ.get("GITHUB_SHA") or subprocess.check_output(
    ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
).strip()
if not re.fullmatch(r"[0-9a-f]{40}", revision):
    raise ValueError("Expected a full site commit SHA")
source = ROOT / "recurrence"
lock = json.loads((source / "engine-lock.json").read_text())
manifest = json.loads((source / "bank" / "manifest.json").read_text())
if manifest.get("engine_revision") != lock["revision"] or manifest.get("engine_version") != lock["version"]:
    raise ValueError("The problem bank was not generated with the locked engine; regenerate it")
site = ROOT / "site"
if site.exists():
    shutil.rmtree(site)
site.mkdir()
for name in ("index.html", "styles.css", "app.js", "books.json"):
    shutil.copyfile(ROOT / name, site / name)
shutil.copytree(ROOT / "equashare", site / "equashare")
target = site / "recurrence"
target.mkdir()
for name in ("index.html", "textbook.html", "styles.css", "app.js", "model.mjs", "mathjax-config.js"):
    shutil.copyfile(source / name, target / name)
(target / "data").mkdir()
for name in ("problems.json", "manifest.json"):
    shutil.copyfile(source / "bank" / name, target / "data" / name)
shutil.copyfile(source / "authored/level6.json", target / "data/level6.json")
index = site / "index.html"
index.write_text(re.sub(r'((?:src|href)="(?:app\.js|styles\.css))(?:\?[^"\s]*)?"',
                       lambda m: m[1] + "?v=" + revision + '"', index.read_text()))
index = target / "index.html"
text = index.read_text()
for name in ("styles.css", "app.js", "mathjax-config.js"):
    text = text.replace('"' + name + '"', '"' + name + '?v=' + revision + '"')
text = text.replace('</head>', '<meta name="recurrence-site-revision" content="' + revision + '"></head>')
index.write_text(text)
app = target / "app.js"
app.write_text(app.read_text().replace("'./model.mjs'", "'./model.mjs?v=" + revision + "'"))
print(f"Assembled Pages site {revision} with problem bank seed {manifest['seed']}")
