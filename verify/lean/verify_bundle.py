#!/usr/bin/env python3
"""Verify every packaged file against the SHA-256 inventory (standard library only)."""
from pathlib import Path
import hashlib
import json
import os

root = Path(__file__).resolve().parent
manifest = json.loads((root / "BUNDLE-MANIFEST.json").read_text())
errors = []
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
print("Verified " + str(len(manifest["files"])) + " packaged files.")
