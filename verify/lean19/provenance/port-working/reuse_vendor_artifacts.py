#!/usr/bin/env python3
"""Plan or apply reuse of byte-identical, generic Vendor Lean artifacts.

The default action is ``plan``.  It validates the completed baseline and writes
an exact, SHA-256-addressed manifest, but does not touch the Lean 19 build tree.
``apply`` requires that manifest and copies only its allow-listed files.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path


PORT_ROOT = Path(__file__).resolve().parent
BASELINE = PORT_ROOT / "baseline17"
TARGET = PORT_ROOT / "lean19"
STATUS_FILE = PORT_ROOT / "logs" / "baseline17" / "status.json"
DEFAULT_MANIFEST = PORT_ROOT / "planning" / "vendor-reuse-manifest.json"
BUILD = Path(".lake/build")
ALLOWED_NAMESPACES = {"JordanCurve", "ClassificationOfSurfaces", "Schoenflies"}
EXPECTED_MODULES = 309


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def tree_digest(entries: list[dict], key: str) -> str:
    h = hashlib.sha256()
    for entry in entries:
        h.update(entry["path"].encode())
        h.update(b"\0")
        h.update(entry[key].encode())
        h.update(b"\n")
    return h.hexdigest()


def load_status() -> dict:
    try:
        data = json.loads(STATUS_FILE.read_text())
    except (OSError, json.JSONDecodeError) as e:
        raise RuntimeError(f"cannot read baseline status {STATUS_FILE}: {e}") from e
    if data.get("status") != "PASS":
        raise RuntimeError(
            f"baseline status is {data.get('status')!r}, not 'PASS'; no manifest or reuse allowed"
        )
    return data


def validate_configuration() -> dict:
    checked = {}
    for rel in ("lean-toolchain", "lake-manifest.json", "LICENSE", "CITATION.cff"):
        left, right = BASELINE / rel, TARGET / rel
        if not left.is_file() or not right.is_file():
            raise RuntimeError(f"missing required provenance/configuration file: {rel}")
        lh, rh = sha256(left), sha256(right)
        if lh != rh:
            raise RuntimeError(f"baseline and target {rel} differ")
        checked[rel] = lh

    base_lake = (BASELINE / "lakefile.lean").read_text()
    target_lake = (TARGET / "lakefile.lean").read_text()
    normalized = target_lake.replace(
        'path := "venn19-closure-s196002.json"',
        'path := "venn17-local-c3-s2.json"',
    ).replace("lean_lib Venn19 where", "lean_lib Venn17 where")
    if normalized != base_lake:
        raise RuntimeError(
            "lakefile.lean differs beyond the reviewed input-file and Venn17/Venn19 target changes"
        )
    checked["lakefile.lean"] = {
        "baseline_sha256": sha256(BASELINE / "lakefile.lean"),
        "target_sha256": sha256(TARGET / "lakefile.lean"),
        "vendor_configuration_equal_after_reviewed_normalization": True,
    }
    return checked


def module_artifact_paths(module_path: Path) -> list[Path]:
    """Return the complete allow-list for one generic module.

    setup.json is deliberately absent: it embeds absolute build-tree paths and
    is neither an output named by the Lean-artifact trace nor needed for reuse.
    Native objects/libraries are absent because these three libraries do not
    precompile modules in lakefile.lean.
    """
    stem = str(module_path)
    return [
        Path("lib/lean") / f"{stem}.olean",
        Path("lib/lean") / f"{stem}.olean.hash",
        Path("lib/lean") / f"{stem}.ilean",
        Path("lib/lean") / f"{stem}.ilean.hash",
        Path("lib/lean") / f"{stem}.trace",
        Path("ir") / f"{stem}.c",
        Path("ir") / f"{stem}.c.hash",
    ]


def inventory() -> tuple[list[dict], list[dict]]:
    modules = []
    artifacts = []
    for src in sorted((BASELINE / "Vendor").rglob("*.lean")):
        rel = src.relative_to(BASELINE / "Vendor")
        module_path = rel.with_suffix("")
        if module_path.parts[0] not in ALLOWED_NAMESPACES:
            raise RuntimeError(f"unexpected Vendor namespace: {rel}")
        target_src = TARGET / "Vendor" / rel
        if not target_src.is_file():
            raise RuntimeError(f"target is missing Vendor source: {rel}")
        left_hash, right_hash = sha256(src), sha256(target_src)
        if left_hash != right_hash:
            raise RuntimeError(f"Vendor source differs: {rel}")
        modules.append({"path": rel.as_posix(), "sha256": left_hash})

        for build_rel in module_artifact_paths(module_path):
            artifact = BASELINE / BUILD / build_rel
            if not artifact.is_file():
                raise RuntimeError(f"completed baseline lacks artifact: {BUILD / build_rel}")
            artifacts.append(
                {
                    "path": build_rel.as_posix(),
                    "bytes": artifact.stat().st_size,
                    "sha256": sha256(artifact),
                }
            )

    if len(modules) != EXPECTED_MODULES:
        raise RuntimeError(f"expected {EXPECTED_MODULES} Vendor modules, found {len(modules)}")
    expected_artifacts = EXPECTED_MODULES * 7
    if len(artifacts) != expected_artifacts:
        raise RuntimeError(f"expected {expected_artifacts} artifacts, found {len(artifacts)}")
    return modules, artifacts


def make_manifest(status: dict) -> dict:
    checked = validate_configuration()
    modules, artifacts = inventory()
    return {
        "schema": 1,
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "purpose": "reuse byte-identical generic Vendor Lean artifacts from the fresh Lean17 baseline",
        "baseline": str(BASELINE),
        "target": str(TARGET),
        "baseline_status_file": str(STATUS_FILE),
        "baseline_status_sha256": sha256(STATUS_FILE),
        "baseline_status": status.get("status"),
        "baseline_command": status.get("command"),
        "baseline_started_utc": status.get("started_utc"),
        "baseline_finished_utc": status.get("finished_utc"),
        "configuration_and_provenance": checked,
        "allowed_namespaces": sorted(ALLOWED_NAMESPACES),
        "excluded": [
            "all Venn17, Venn19, VennCore, and VennTopology artifacts",
            "all setup.json files because they contain baseline absolute paths",
            "all object, archive, and dynamic-library artifacts",
        ],
        "module_count": len(modules),
        "artifact_count": len(artifacts),
        "artifact_bytes": sum(x["bytes"] for x in artifacts),
        "vendor_sources_digest_sha256": tree_digest(modules, "sha256"),
        "artifacts_digest_sha256": tree_digest(artifacts, "sha256"),
        "modules": modules,
        "artifacts": artifacts,
        "post_copy_validation": (
            "python3 reuse_vendor_artifacts.py check"
        ),
    }


def validate_saved_manifest(manifest: dict) -> None:
    status = load_status()
    validate_configuration()
    if manifest.get("baseline") != str(BASELINE) or manifest.get("target") != str(TARGET):
        raise RuntimeError("manifest baseline/target paths do not match this port")
    if manifest.get("baseline_status") != "PASS":
        raise RuntimeError("manifest was not made from a PASS baseline")
    if manifest.get("baseline_status_sha256") != sha256(STATUS_FILE):
        raise RuntimeError("baseline status changed since the manifest was written; run plan again")

    modules = manifest.get("modules")
    artifacts = manifest.get("artifacts")
    if not isinstance(modules, list) or len(modules) != EXPECTED_MODULES:
        raise RuntimeError("manifest has the wrong module set")
    if not isinstance(artifacts, list) or len(artifacts) != EXPECTED_MODULES * 7:
        raise RuntimeError("manifest has the wrong artifact set")

    allowed = set()
    for module in modules:
        rel = Path(module["path"])
        module_path = rel.with_suffix("")
        if module_path.parts[0] not in ALLOWED_NAMESPACES or rel.suffix != ".lean":
            raise RuntimeError(f"manifest contains disallowed module: {rel}")
        for build_rel in module_artifact_paths(module_path):
            allowed.add(build_rel.as_posix())
        for root in (BASELINE, TARGET):
            source = root / "Vendor" / rel
            if not source.is_file() or sha256(source) != module["sha256"]:
                raise RuntimeError(f"Vendor source no longer matches manifest: {source}")

    if {x.get("path") for x in artifacts} != allowed:
        raise RuntimeError("manifest artifact paths differ from the exact module-derived allow-list")
    for item in artifacts:
        source = BASELINE / BUILD / item["path"]
        if not source.is_file() or source.stat().st_size != item["bytes"] or sha256(source) != item["sha256"]:
            raise RuntimeError(f"baseline artifact no longer matches manifest: {source}")
    del status  # load_status is intentionally also a fresh PASS gate.


def apply_manifest(manifest: dict) -> tuple[int, int]:
    artifacts = manifest["artifacts"]
    # Preflight every destination before writing any file.
    for item in artifacts:
        destination = TARGET / BUILD / item["path"]
        if destination.exists() and (
            not destination.is_file()
            or destination.stat().st_size != item["bytes"]
            or sha256(destination) != item["sha256"]
        ):
            raise RuntimeError(f"refusing to overwrite conflicting target artifact: {destination}")

    copied = skipped = 0
    for item in artifacts:
        source = BASELINE / BUILD / item["path"]
        destination = TARGET / BUILD / item["path"]
        if destination.exists():
            skipped += 1
            continue
        destination.parent.mkdir(parents=True, exist_ok=True)
        fd, tmp_name = tempfile.mkstemp(prefix=f".{destination.name}.", dir=destination.parent)
        os.close(fd)
        tmp = Path(tmp_name)
        try:
            shutil.copy2(source, tmp)
            if tmp.stat().st_size != item["bytes"] or sha256(tmp) != item["sha256"]:
                raise RuntimeError(f"copy verification failed: {destination}")
            os.replace(tmp, destination)
        finally:
            tmp.unlink(missing_ok=True)
        copied += 1
    return copied, skipped


def check_manifest(manifest: dict) -> int:
    """Ask Lake to accept every copied module without permitting compilation.

    Explicit module targets are intentional.  On this source tree, Lake 5.0.0's
    library target collection reports the same generic "bad imports" error in
    the successfully built baseline.  Each explicit module target succeeds and
    exercises the actual leanArts trace/output check.
    """
    modules = manifest["modules"]
    artifacts = manifest["artifacts"]
    for item in artifacts:
        target = TARGET / BUILD / item["path"]
        if not target.is_file() or target.stat().st_size != item["bytes"] or sha256(target) != item["sha256"]:
            raise RuntimeError(f"target artifact does not match manifest: {target}")

    lake = Path.home() / ".elan/toolchains/leanprover--lean4---v4.32.1/bin/lake"
    if not lake.is_file():
        raise RuntimeError(f"expected Lake executable is missing: {lake}")
    targets = [f"+{'.'.join(Path(x['path']).with_suffix('').parts)}" for x in modules]
    cmd = [
        str(lake), "--rehash", "--no-build", "--no-cache", "--no-ansi",
        "build", *targets,
    ]
    print(f"Strict Lake check: {len(targets)} explicit module targets; compilation disabled.")
    return subprocess.run(cmd, cwd=TARGET).returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", nargs="?", choices=("plan", "apply", "check"), default="plan")
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    args = parser.parse_args()
    try:
        if args.action == "plan":
            status = load_status()
            manifest = make_manifest(status)
            args.manifest.parent.mkdir(parents=True, exist_ok=True)
            args.manifest.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
            print(f"PLAN ONLY: wrote {args.manifest}")
            print(f"modules: {manifest['module_count']}")
            print(f"artifacts: {manifest['artifact_count']}")
            print(f"bytes: {manifest['artifact_bytes']}")
            print("No target build artifact was changed.")
        else:
            try:
                manifest = json.loads(args.manifest.read_text())
            except (OSError, json.JSONDecodeError) as e:
                raise RuntimeError(f"cannot read manifest {args.manifest}: {e}") from e
            validate_saved_manifest(manifest)
            if args.action == "apply":
                copied, skipped = apply_manifest(manifest)
                print(f"copied: {copied}; already identical: {skipped}")
                print("Required next gate (this script does not run it):")
                print(manifest["post_copy_validation"])
            else:
                return check_manifest(manifest)
        return 0
    except RuntimeError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
