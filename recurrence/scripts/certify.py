#!/usr/bin/env python3
"""Publish only a bank checked by the matching compiled Lean source and audit."""
import hashlib
import json
import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / "build"
bank = json.loads((BUILD / "candidates.json").read_text(encoding="utf-8"))
proof = (ROOT / "lean/Recurrence/Generated.lean").read_bytes()
assert hashlib.sha256(proof).hexdigest() == bank["proof_source_sha256"]
from compiler import compile_blocks
from rules import normalize_recipe
from scoring import assess, score_routes
from solve import find_routes
config = bank['generation_config']
for p in bank['problems']:
    assert normalize_recipe(p['recipe'], config) == p['recipe']
    assert compile_blocks(p['recipe'], config) == p['ir']
    assert assess(p['ir'], score_routes(p['ir'], find_routes(p['ir'], config)), config)['accepted']
assert (ROOT / "lean/.lake/build/lib/lean/Recurrence/Generated.olean").is_file(), "Lean compilation did not produce Generated.olean"
log = (BUILD / "lean.log").read_text(encoding="utf-8")
assert "sorryAx" not in log, "Untrusted proof dependency"
for path in (ROOT / "lean").rglob("*.lean"):
    if ".lake" in path.parts: continue
    source = re.sub(r"--[^\n]*", "", path.read_text(encoding="utf-8"))
    assert not re.search(r"\b(sorry|admit|axiom)\b", source), f"Incomplete or assumed proof: {path}"
for p in bank["problems"]:
    for theorem in p["lean_theorems"]:
        assert f"Recurrence.{theorem}" in log, f"Missing axiom audit: {theorem}"
    p["verification"] = {"status": "lean-verified", "scope": "general-term-initial-recurrence-uniqueness"}
    if p["ir"]["reciprocal"]: p["verification"]["domain"] = "all-natural-indices"
bank["verification"] = {"status": "lean-verified", "toolchain": "leanprover/lean4:v4.19.0",
                        "mathlib": "v4.19.0", "commit": os.environ.get("GITHUB_SHA", "local"),
                        "run_id": os.environ.get("GITHUB_RUN_ID"), "count": len(bank["problems"])}
data = json.dumps(bank, ensure_ascii=False, separators=(",", ":")).encode()
(BUILD / "problems.json").write_bytes(data)
manifest = {"schema_version": 1, **bank["verification"], "bank_sha256": hashlib.sha256(data).hexdigest(),
            "proof_source_sha256": bank["proof_source_sha256"]}
(BUILD / "manifest.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")
print(f"Certified {len(bank['problems'])} problems; bank SHA-256 {manifest['bank_sha256']}")
