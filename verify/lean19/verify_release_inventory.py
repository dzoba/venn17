#!/usr/bin/env python3
"""Verify every packaged file against the SHA-256 inventory (standard library only)."""
from pathlib import Path
import hashlib
import json
import os

root = Path(__file__).resolve().parent
manifest = json.loads((root / "BUNDLE-MANIFEST.json").read_text())
errors = []
excluded = set(manifest.get("excluded", []))
actual = {
    p.relative_to(root).as_posix()
    for p in root.rglob("*")
    if p.is_file() or p.is_symlink()
}
expected = set(manifest["files"]) | excluded
for name in sorted(actual - expected):
    errors.append("Unlisted: " + name)
for name in sorted(expected - actual):
    errors.append("Missing listed/excluded path: " + name)
for name, entry in manifest["files"].items():
    path = root / name
    if entry["type"] == "symlink":
        if not path.is_symlink() or os.readlink(path) != entry["target"]:
            errors.append("Changed symlink: " + name)
        continue
    if not path.is_file():
        errors.append("Missing: " + name)
        continue
    data = path.read_bytes()
    if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
        errors.append("Changed: " + name)
if errors:
    raise SystemExit("\n".join(errors))
print("Verified " + str(len(manifest["files"])) + " hashed packaged files and complete file inventory.")
