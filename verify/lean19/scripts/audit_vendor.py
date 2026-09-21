"""Check the vendored classification sources against the pinned source manifest."""
import hashlib
import json
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1] / "Vendor"
    manifest = json.loads((root / "classification-sources.json").read_text())
    errors = []
    for module in manifest["modules"]:
        path = root.joinpath(*module.split(".")).with_suffix(".lean")
        if not path.exists():
            errors.append(f"missing: {module}")
        elif hashlib.sha256(path.read_bytes()).hexdigest() != manifest["sha256"][module]:
            errors.append(f"source differs from upstream: {module}")
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"Verified {len(manifest['modules'])} unchanged sources at {manifest['commit']}.")


if __name__ == "__main__":
    main()
