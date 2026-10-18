#!/usr/bin/env python3
"""Assemble the same static files tested locally and uploaded to Pages."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
revision = os.environ.get("GITHUB_SHA") or subprocess.check_output(
    ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
).strip()
if not re.fullmatch(r"[0-9a-f]{40}", revision):
    raise ValueError("Expected a full site commit SHA")
source = ROOT / "recurrence"
lock = json.loads((source / "engine-lock.json").read_text())
provenance = json.loads((source / "engine" / lock["revision"] / "provenance.json").read_text())
if provenance["revision"] != lock["revision"] or provenance["version"] != lock["version"]:
    raise ValueError("The prepared browser engine differs from the lock")
if hashlib.sha256((source / "index.html").read_bytes()).hexdigest() != provenance["source_entry_sha256"]:
    raise ValueError("The browser entry page differs from the prepared engine")
site = ROOT / "site"
if site.exists():
    shutil.rmtree(site)
site.mkdir()
for name in ("index.html", "styles.css", "app.js", "books.json"):
    shutil.copyfile(ROOT / name, site / name)
shutil.copytree(ROOT / "equashare", site / "equashare")
target = site / "recurrence"
target.mkdir()
for name in ("index.html", "textbook.html", "styles.css", "app.js", "model.mjs",
             "mathjax-config.js", "lab-entry.js", "lab-host.css"):
    shutil.copyfile(source / name, target / name)
shutil.copytree(source / "engine", target / "engine")
(target / "data").mkdir()
for name in ("problems.json", "manifest.json", "quality-report.json"):
    shutil.copyfile(source / "build" / name, target / "data" / name)
shutil.copyfile(source / "authored/level6.json", target / "data/level6.json")
index = site / "index.html"
index.write_text(re.sub(r'((?:src|href)="(?:app\.js|styles\.css))(?:\?[^"\s]*)?"',
                       lambda m: m[1] + "?v=" + revision + '"', index.read_text()))
for filename in ("index.html", "textbook.html"):
    index = target / filename
    text = index.read_text()
    for name in ("styles.css", "app.js", "mathjax-config.js", "lab-entry.js", "lab-host.css"):
        for prefix in ("", "./"):
            text = text.replace('"' + prefix + name + '"', '"' + prefix + name + '?v=' + revision + '"')
    text = text.replace('</head>', '<meta name="recurrence-site-revision" content="' + revision + '"></head>')
    index.write_text(text)
app = target / "app.js"
app.write_text(app.read_text().replace("'./model.mjs'", "'./model.mjs?v=" + revision + "'"))
print(f"Assembled Pages site {revision} with browser engine {lock['revision']}")
