#!/usr/bin/env python3
"""Assemble the same static files tested locally and uploaded to Pages."""
import html
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
SHARED = ("shell.css", "shell.js", "lib.js", "styles.css", "app.js", "book.js")
for name in ("index.html", "books.json") + SHARED:
    shutil.copyfile(ROOT / name, site / name)
# All pages import the same versioned lib.js so they share one module instance.
for name in ("shell.js", "app.js", "book.js"):
    path = site / name
    path.write_text(path.read_text().replace('from "./lib.js"', f'from "./lib.js?v={revision}"'))
BOOK_PATH = '<meta name="bookshelf-book-path" content="books/{id}/">'


def versioned(text, prefix=""):
    names = "|".join(re.escape(prefix + name) for name in SHARED)
    return re.sub(r'((?:src|href)="(?:' + names + r'))(?:\?[^"\s]*)?"',
                  lambda m: m[1] + "?v=" + revision + '"', text)


books = json.loads((ROOT / "books.json").read_text(encoding="utf-8"))
template = (ROOT / "book.html").read_text(encoding="utf-8")
seen = set()
for book in books:
    book_id = book.get("id", "")
    if not re.fullmatch(r"[a-z0-9][a-z0-9-]*", book_id) or book_id in seen:
        raise ValueError(f"Invalid or duplicate book id: {book_id!r}")
    seen.add(book_id)
    title = html.escape(book["title"])
    page = template.replace('<meta charset="utf-8">', '<meta charset="utf-8">\n  <base href="../../">', 1)
    page = page.replace("<title>教科書 — 数学書の本棚</title>",
                        f"<title>{title} — 数学書の本棚</title>\n"
                        f'  <meta name="book-id" content="{html.escape(book_id)}">\n  {BOOK_PATH}', 1)
    page = page.replace('<h1 id="book-title">教科書</h1>', f'<h1 id="book-title">{title}</h1>', 1)
    page = page.replace('<span aria-current="page" id="crumb-title">…</span>',
                        f'<span aria-current="page" id="crumb-title">{title}</span>', 1)
    target_dir = site / "books" / book_id
    target_dir.mkdir(parents=True)
    (target_dir / "index.html").write_text(versioned(page), encoding="utf-8")
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
index.write_text(versioned(index.read_text()).replace("</head>", "  " + BOOK_PATH + "\n</head>", 1))
index = target / "index.html"
text = index.read_text()
for name in ("styles.css", "app.js", "mathjax-config.js"):
    text = text.replace('"' + name + '"', '"' + name + '?v=' + revision + '"')
text = text.replace('</head>', '<meta name="recurrence-site-revision" content="' + revision + '"></head>')
text = versioned(text, "../").replace('</head>', BOOK_PATH + '</head>', 1)
index.write_text(text)
app = target / "app.js"
app.write_text(app.read_text().replace("'./model.mjs'", "'./model.mjs?v=" + revision + "'"))
print(f"Assembled Pages site {revision} with problem bank seed {manifest['seed']}")
