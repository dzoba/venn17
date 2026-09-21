#!/usr/bin/env python3
"""Plan or run bounded post-build verification for the Lean 19 source port."""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time
import traceback


ROOT = Path(__file__).resolve().parent
PROJECT = ROOT / "lean19"
BUILD_STATUS = ROOT / "logs/lean19/status.json"
OUT = ROOT / "logs/lean19/postbuild"
BASELINE_AXIOMS = ROOT / "logs/baseline17/audit-topology-output.txt"
TOOLCHAIN = Path("/Users/dzoba/.elan/toolchains/leanprover--lean4---v4.32.1/bin")
INPUT = "venn19-closure-s196002.json"
GIB = 1024**3

EXPECTED_THEOREM_TYPES = {
    "Venn19.Topology.supplied_simple_rotational_venn": (
        "Venn19.Topology.SimpleRotationalVenn "
        "Venn19.Topology.rotationalVennCurve "
        "Venn19.Topology.rotationalVennSide"
    ),
    "Venn19.Topology.exists_simple_rotational_venn_19": (
        "∃ (C : Fin 19 → Set Venn19.Topology.Plane) "
        "(S : Fin 19 → Bool → Set Venn19.Topology.Plane), "
        "Venn19.Topology.SimpleRotationalVenn C S"
    ),
}

THEOREM_CHECK_SOURCE = """import VennTopology

-- These examples are compiled type ascriptions, not textual name checks.
example :
    Venn19.Topology.SimpleRotationalVenn
      Venn19.Topology.rotationalVennCurve
      Venn19.Topology.rotationalVennSide :=
  Venn19.Topology.supplied_simple_rotational_venn

example :
    ∃ (C : Fin 19 → Set Venn19.Topology.Plane)
      (S : Fin 19 → Bool → Set Venn19.Topology.Plane),
      Venn19.Topology.SimpleRotationalVenn C S :=
  Venn19.Topology.exists_simple_rotational_venn_19

#eval IO.println "BEGIN supplied_simple_rotational_venn CHECK"
#check Venn19.Topology.supplied_simple_rotational_venn
#eval IO.println "END supplied_simple_rotational_venn CHECK"
#eval IO.println "BEGIN supplied_simple_rotational_venn PRINT"
#print Venn19.Topology.supplied_simple_rotational_venn
#eval IO.println "END supplied_simple_rotational_venn PRINT"

#eval IO.println "BEGIN exists_simple_rotational_venn_19 CHECK"
#check Venn19.Topology.exists_simple_rotational_venn_19
#eval IO.println "END exists_simple_rotational_venn_19 CHECK"
#eval IO.println "BEGIN exists_simple_rotational_venn_19 PRINT"
#print Venn19.Topology.exists_simple_rotational_venn_19
#eval IO.println "END exists_simple_rotational_venn_19 PRINT"
"""


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def write_json(path, value):
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2) + "\n")
    tmp.replace(path)


def plan():
    """Commands mirror the local README/PORT-README verification commands."""
    py_audit = str(OUT / "python-audit.json")
    statement = str(OUT / "theorem-statements.lean")
    lake = str(TOOLCHAIN / "lake")
    return [
        ["shasum", "-a", "256", "-c", "PORT-SHA256SUMS"],
        [lake, "--no-cache", "--no-ansi", "build", "Venn19.Tests"],
        [lake, "--no-cache", "--no-ansi", "exe", "venn_check", INPUT],
        ["python3", "scripts/check.py", "--output", py_audit],
        ["python3", "scripts/test_checkers.py"],
        ["python3", "scripts/audit_vendor.py"],
        [lake, "--no-cache", "--no-ansi", "env", "lean", "scripts/audit_topology.lean"],
        [lake, "--no-cache", "--no-ansi", "env", "lean", statement],
    ]


def owned_rows(pgid):
    text = subprocess.check_output(
        ["/bin/ps", "-axo", "pid=,pgid=,rss=,command="], text=True)
    rows = []
    for line in text.splitlines():
        fields = line.strip().split(None, 3)
        if len(fields) != 4:
            continue
        try:
            pid, group, rss = map(int, fields[:3])
        except ValueError:
            continue
        if group == pgid:
            rows.append((pid, rss * 1024, fields[3][:1000]))
    return rows


def tree_size_no_follow(root):
    """Count regular files under root without following the packages symlink."""
    total = 0
    for base, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = [d for d in dirs if not (Path(base) / d).is_symlink()]
        for name in files:
            path = Path(base) / name
            try:
                if not path.is_symlink() and path.is_file():
                    total += path.stat().st_size
            except FileNotFoundError:
                pass
    return total


def evidence_size():
    return tree_size_no_follow(OUT) if OUT.exists() else 0


def resource_violation(started, wall_limit, evidence_limit,
                       owned_root_limit, filesystem_reserve):
    elapsed = time.monotonic() - started
    if elapsed >= wall_limit:
        return "TOTAL_WALL_LIMIT", {"elapsed_seconds": elapsed}
    out_bytes = evidence_size()
    if out_bytes > evidence_limit:
        return "EVIDENCE_OUTPUT_LIMIT", {"evidence_bytes": out_bytes}
    owned_root_bytes = tree_size_no_follow(ROOT)
    if owned_root_bytes > owned_root_limit:
        return "OWNED_LEAN_DIRECTORY_LIMIT", {"owned_lean_bytes": owned_root_bytes}
    free_bytes = shutil.disk_usage(PROJECT).free
    if free_bytes < filesystem_reserve:
        return "FILESYSTEM_RESERVE", {"filesystem_available_bytes": free_bytes}
    return None, {
        "elapsed_seconds": elapsed,
        "evidence_bytes": out_bytes,
        "owned_lean_bytes": owned_root_bytes,
        "filesystem_available_bytes": free_bytes,
    }


def run_step(index, cmd, env, started, wall_limit, rss_limit,
             evidence_limit, project_limit, filesystem_reserve):
    name = f"{index:02d}-{Path(cmd[0]).name}"
    log_path, time_path = OUT / f"{name}.log", OUT / f"{name}.time.txt"
    step_started = time.monotonic()
    record = {
        "index": index, "command": cmd, "started_utc": now(),
        "log": log_path.name, "time": time_path.name,
        "peak_aggregate_rss_bytes_lower_bound": 0,
        "peak_processes_observed": 0, "status": "RUNNING",
    }
    reason, resources = resource_violation(
        started, wall_limit, evidence_limit, project_limit, filesystem_reserve)
    record["resources_before_start"] = resources
    if reason:
        record.update(status="FAILED", failure_reason=reason,
                      finished_utc=now(), elapsed_seconds=0,
                      exit_code=None, command_started=False)
        return record

    wrapped = ["/usr/bin/time", "-l", "-p", "-o", str(time_path), *cmd]
    with log_path.open("wb") as log:
        child = subprocess.Popen(
            wrapped, cwd=PROJECT, env=env, stdout=log,
            stderr=subprocess.STDOUT, start_new_session=True)
        record["command_started"] = True
        detail = {}
        try:
            while child.poll() is None:
                rows = owned_rows(child.pid)
                rss = sum(row[1] for row in rows)
                record["peak_aggregate_rss_bytes_lower_bound"] = max(
                    record["peak_aggregate_rss_bytes_lower_bound"], rss)
                record["peak_processes_observed"] = max(
                    record["peak_processes_observed"], len(rows))
                reason, detail = resource_violation(
                    started, wall_limit, evidence_limit,
                    project_limit, filesystem_reserve)
                if not reason and rss > rss_limit:
                    reason, detail = "RSS_LIMIT", {"aggregate_rss_bytes": rss}
                if reason:
                    break
                time.sleep(2)
        except BaseException as exc:
            reason = "DRIVER_ERROR"
            detail = {"error": repr(exc)}
        if reason and child.poll() is None:
            os.killpg(child.pid, signal.SIGTERM)
            try:
                child.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
        code = child.wait()
    if not reason:
        reason, detail = resource_violation(
            started, wall_limit, evidence_limit,
            project_limit, filesystem_reserve)
    if reason:
        status, failure_reason = "FAILED", reason
    elif code != 0:
        status, failure_reason = "FAILED", "NONZERO_EXIT"
    else:
        status, failure_reason = "PASS", None
    record.update(
        finished_utc=now(), elapsed_seconds=time.monotonic() - step_started,
        exit_code=code, status=status, final_resource_detail=detail)
    if failure_reason:
        record["failure_reason"] = failure_reason
    return record


def canonical_axioms(text, lean19=False):
    if lean19:
        text = text.replace("Venn19", "Venn17")
        text = text.replace("exists_simple_rotational_venn_19",
                            "exists_simple_rotational_venn_17")
    return re.sub(r"\s+", " ", text).strip()


def final_axioms(text, theorem):
    match = re.search(r"'" + re.escape(theorem) +
                      r"' depends on axioms: \[(.*?)\]", text, re.S)
    if not match:
        raise RuntimeError(f"missing axiom output for {theorem}")
    return [x.strip() for x in match.group(1).replace("\n", " ").split(",") if x.strip()]


def active_hashes():
    entries = []
    for line in (PROJECT / "PORT-SHA256SUMS").read_text().splitlines():
        digest, path = line.split(None, 1)
        path = path.strip()
        actual = hashlib.sha256((PROJECT / path).read_bytes()).hexdigest()
        entries.append({"path": path, "expected_sha256": digest,
                        "actual_sha256": actual, "match": actual == digest})
    return entries


def validate_theorem_output(text):
    actual = {}
    missing = []
    for short in ("supplied_simple_rotational_venn", "exists_simple_rotational_venn_19"):
        for action in ("CHECK", "PRINT"):
            begin, end = f"BEGIN {short} {action}", f"END {short} {action}"
            match = re.search(
                re.escape(begin) + r"\s*(.*?)\s*" + re.escape(end), text, re.S)
            if match:
                actual[f"{short}_{action.lower()}"] = match.group(1).strip()
            else:
                missing.extend([begin, end])
    if missing:
        raise RuntimeError(f"missing theorem output markers: {missing}")
    for theorem in EXPECTED_THEOREM_TYPES:
        if theorem not in text:
            raise RuntimeError(f"theorem output does not name {theorem}")
    encoded = text.encode()
    return {
        "path": "08-lake.log",
        "sha256": hashlib.sha256(encoded).hexdigest(),
        "bytes": len(encoded),
        "markers_complete": True,
        "compiled_type_ascriptions": EXPECTED_THEOREM_TYPES,
        "actual_check_and_print_output": actual,
    }


def execute(args, ownership):
    build = json.loads(BUILD_STATUS.read_text())
    if build.get("status") != "PASS":
        raise RuntimeError(
            f"REFUSED: {BUILD_STATUS} status is {build.get('status')!r}, not PASS")
    if OUT.exists():
        raise RuntimeError(f"REFUSED: evidence directory already exists: {OUT}")
    if not BASELINE_AXIOMS.is_file():
        raise RuntimeError(f"REFUSED: missing baseline audit: {BASELINE_AXIOMS}")
    subprocess.run(["/bin/ps", "-axo", "pid=,pgid=,rss=,command="], check=True,
                   stdout=subprocess.DEVNULL)
    subprocess.run(["/usr/sbin/sysctl", "kern.clockrate"], check=True,
                   stdout=subprocess.DEVNULL)

    started = time.monotonic()
    limits = {
        "wall_limit_seconds": args.wall_seconds,
        "rss_limit_bytes": args.rss_limit_gib * GIB,
        "evidence_limit_bytes": args.output_limit_gib * GIB,
        "owned_lean_directory_limit_bytes": args.project_limit_gib * GIB,
        "filesystem_reserve_bytes": args.filesystem_reserve_gib * GIB,
    }
    reason, detail = resource_violation(
        started, limits["wall_limit_seconds"], limits["evidence_limit_bytes"],
        limits["owned_lean_directory_limit_bytes"], limits["filesystem_reserve_bytes"])
    if reason:
        raise RuntimeError(f"REFUSED: initial resource gate {reason}: {detail}")

    OUT.mkdir(parents=True)
    ownership["output_created"] = True
    (OUT / "theorem-statements.lean").write_text(THEOREM_CHECK_SOURCE)
    write_json(OUT / "status.json", {
        "status": "RUNNING", "started_utc": now(), "limits": limits})
    env = os.environ.copy()
    env.update(PATH=str(TOOLCHAIN) + os.pathsep + env["PATH"],
               LEAN_NUM_THREADS="1", LAKE_NO_CACHE="1")
    records = []
    commands = plan()
    for index, cmd in enumerate(commands, 1):
        record = run_step(
            index, cmd, env, started, limits["wall_limit_seconds"],
            limits["rss_limit_bytes"], limits["evidence_limit_bytes"],
            limits["owned_lean_directory_limit_bytes"],
            limits["filesystem_reserve_bytes"])
        records.append(record)
        write_json(OUT / "resource-report.json", records)
        if record["status"] != "PASS":
            write_json(OUT / "status.json", {
                "status": "FAILED", "failed_step": index,
                "failure_reason": record.get("failure_reason"),
                "finished_utc": now(), "limits": limits})
            return 1

    hashes = active_hashes()
    write_json(OUT / "active-hashes.json", hashes)
    audit = (OUT / "07-lake.log").read_text()
    baseline = BASELINE_AXIOMS.read_text()
    ax19 = final_axioms(audit, "Venn19.Topology.supplied_simple_rotational_venn")
    ax17 = final_axioms(baseline, "Venn17.Topology.supplied_simple_rotational_venn")
    mapped19 = [x.replace("Venn19", "Venn17") for x in ax19]
    statement_output = (OUT / "08-lake.log").read_text()
    theorem_evidence = validate_theorem_output(statement_output)
    write_json(OUT / "theorem-interface-output.json", theorem_evidence)
    summary = {
        "status": "PASS",
        "build_gate": str(BUILD_STATUS),
        "elapsed_seconds": time.monotonic() - started,
        "limits": limits,
        "all_active_hashes_match": all(x["match"] for x in hashes),
        "active_hash_count": len(hashes),
        "license_preserved": (PROJECT / "LICENSE").read_bytes() == (ROOT / "baseline17/LICENSE").read_bytes(),
        "citation_preserved": (PROJECT / "CITATION.cff").read_bytes() == (ROOT / "baseline17/CITATION.cff").read_bytes(),
        "axiom_outputs_equal_after_whitespace_and_only_documented_renames":
            canonical_axioms(audit, True) == canonical_axioms(baseline),
        "final_axiom_lists_equal_after_Venn19_to_Venn17": mapped19 == ax17,
        "final_axiom_count": len(ax19),
        "native_decide_axiom_count": sum("native_decide" in x for x in ax19),
        "logical_axioms": [x for x in ax19 if "native_decide" not in x],
        "theorem_interface_evidence": theorem_evidence,
        "trust_boundary": "native_decide trusts Lean's compiler/runtime; no kernel reduction claim is made for those finite checks",
    }
    checks = [
        summary["all_active_hashes_match"], summary["license_preserved"],
        summary["citation_preserved"],
        summary["axiom_outputs_equal_after_whitespace_and_only_documented_renames"],
        summary["final_axiom_lists_equal_after_Venn19_to_Venn17"],
        summary["final_axiom_count"] == 23,
        summary["native_decide_axiom_count"] == 20,
        summary["logical_axioms"] == ["propext", "Classical.choice", "Quot.sound"],
        theorem_evidence["markers_complete"],
    ]
    summary["status"] = "PASS" if all(checks) else "COMPARISON_FAILED"
    write_json(OUT / "summary.json", summary)
    write_json(OUT / "status.json", {
        "status": summary["status"], "finished_utc": now(), "limits": limits})
    return 0 if summary["status"] == "PASS" else 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--run", action="store_true", help="execute after PASS gate")
    parser.add_argument("--wall-seconds", type=int, default=7200)
    parser.add_argument("--rss-limit-gib", type=int, default=32)
    parser.add_argument("--output-limit-gib", type=int, default=2,
                        help="postbuild evidence directory cap")
    parser.add_argument("--project-limit-gib", type=int, default=10,
                        help="full lean19-port root cap, excluding symlink targets")
    parser.add_argument("--filesystem-reserve-gib", type=int, default=8)
    args = parser.parse_args()
    numeric = {
        "--wall-seconds": args.wall_seconds,
        "--rss-limit-gib": args.rss_limit_gib,
        "--output-limit-gib": args.output_limit_gib,
        "--project-limit-gib": args.project_limit_gib,
        "--filesystem-reserve-gib": args.filesystem_reserve_gib,
    }
    for option, value in numeric.items():
        if value <= 0:
            parser.error(f"{option} must be positive")

    commands = plan()
    if not args.run:
        print(json.dumps({
            "mode": "PLAN_ONLY", "required_build_status": "PASS",
            "gate": str(BUILD_STATUS), "output": str(OUT),
            "limits": {
                "wall_seconds": args.wall_seconds,
                "rss_limit_gib": args.rss_limit_gib,
                "evidence_limit_gib": args.output_limit_gib,
                "owned_lean_directory_limit_gib": args.project_limit_gib,
                "filesystem_reserve_gib": args.filesystem_reserve_gib,
            },
            "commands": commands,
            "compiled_theorem_type_ascriptions": EXPECTED_THEOREM_TYPES,
            "trust_boundary": "20 expected input-specific native_decide axioms plus Lean's three standard logical axioms",
        }, indent=2))
        return 0

    ownership = {"output_created": False}
    try:
        return execute(args, ownership)
    except BaseException as exc:
        if ownership["output_created"]:
            error_text = traceback.format_exc()
            try:
                (OUT / "driver-error.log").write_text(error_text)
                write_json(OUT / "status.json", {
                    "status": "FAILED", "failure_reason": "DRIVER_EXCEPTION",
                    "error": repr(exc), "finished_utc": now()})
            except BaseException:
                pass
        print(f"FAILED: {exc!r}", file=os.sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
