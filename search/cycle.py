#!/usr/bin/env python3
"""cycle.py -- unattended cycle driver for relaxed_walk5.

Each cycle launches S parallel relaxed_walk5 processes from the current best
state, waits for all of them, keeps the lowest-energy result as the state the
next cycle starts from, and logs the cycle to results.md / results.json.
Stops as soon as a run reports complete=true or drops a <prefix>-venn.json.

  python3 cycle.py <n> <start: - | file.json | file.raw> <outdir> \
      --cycles C --seeds S --seconds D --thot TH --tcold TC \
      [--pb 0.15] [--target 0.5] [--seedbase 1000] \
      [--lambda0 L0] [--lambda1 L1] [--lambda-period P] [--temps T,T,...] \
      [--chunk N] [--select energy|best] [--keep-worse]

The lambda/temps/chunk options are forwarded to each child as RW_LAMBDA0,
RW_LAMBDA1, RW_LAMBDA_PERIOD, RW_TEMPS and RW_CHUNK, and are only set when the
option is given (RW_TEMPS is cleared when --temps is absent, so the default is
still one annealed walk thot -> tcold).

Restartable: outdir/state.json records the cycle to resume at and the current
best state, and is re-read if the driver is started again on the same outdir.
"""
import argparse
import json
import os
import shlex
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
POLAR = HERE.parent                      # .../research/polar-calibration
BINARY = HERE / "relaxed_walk5"

# Independent structural checker. Run in its own interpreter from POLAR so the
# driver never has to import the scaffold modules itself.
CHECK_CODE = r'''
import sys, json, traceback
sys.path.insert(0, 'gks-scaffold')
sys.path.insert(0, '../matching-repair/controls')
path = sys.argv[1]; n = int(sys.argv[2])
try:
    from interval_growth import oriented_faces
    from gks_scaffold import check
    d = json.load(open(path))
    faces = {frozenset(x) for x in d['faces']}
    r = check(n, oriented_faces(faces, n))
    ok = (r['all_labels'] and r['euler'] == 2
          and set(r['edge_multiplicities']) == {2}
          and r['vertices_single_rotation_cycle']
          and r['curves_two_sides_connected']
          and r['rotation_symmetric']
          and r['non_transversal_faces'] == 0
          and r['repeated_vertex_faces'] == 0)
    print(json.dumps({'ok': bool(ok), 'report': r}, default=str))
except Exception as e:
    print(json.dumps({'ok': False,
                      'error': ''.join(traceback.format_exception_only(type(e), e)).strip(),
                      'traceback': traceback.format_exc()}))
'''


def run_checker(json_path, n):
    """Independent gks_scaffold check of an exported diagram. Never raises."""
    try:
        p = subprocess.run([sys.executable, "-c", CHECK_CODE, str(json_path), str(n)],
                           cwd=str(POLAR), capture_output=True, text=True, timeout=1800)
    except Exception as e:  # noqa: BLE001 - the checker must never kill the driver
        return {"ok": False, "error": "checker subprocess failed: %r" % (e,)}
    out = (p.stdout or "").strip().splitlines()
    for line in reversed(out):
        try:
            return json.loads(line)
        except ValueError:
            continue
    return {"ok": False, "error": "checker produced no JSON (rc=%d): %s"
                                  % (p.returncode, (p.stderr or "")[-500:])}


def parse_stdout_json(path):
    """Last JSON object printed by relaxed_walk5, or None."""
    try:
        lines = Path(path).read_text().splitlines()
    except OSError:
        return None
    for line in reversed(lines):
        line = line.strip()
        if line.startswith("{"):
            try:
                return json.loads(line)
            except ValueError:
                continue
    return None


def native_check_lines(path):
    """The program's own 'native check PASSED/FAILED' lines from stderr."""
    try:
        return [ln.strip() for ln in Path(path).read_text().splitlines()
                if "native check" in ln]
    except OSError:
        return []


def energy_key(rec, select="energy"):
    """Sort key over a run's stdout JSON.

    select='energy': lowest final energy, ties broken by best_energy.
    select='best':   lowest best_energy, ties broken by final energy.
    """
    inf = float("inf")
    r = rec["result"]
    if r is None:
        return (inf, inf)
    if select == "best":
        return (r.get("best_energy", inf), r.get("energy", inf))
    return (r.get("energy", inf), r.get("best_energy", inf))


def load_state(path):
    try:
        return json.loads(Path(path).read_text())
    except (OSError, ValueError):
        return None


def save_state(path, state):
    tmp = Path(str(path) + ".tmp")
    tmp.write_text(json.dumps(state, indent=2) + "\n")
    tmp.replace(path)


def append_results_json(path, row):
    rows = []
    if path.exists():
        try:
            rows = json.loads(path.read_text())
            if not isinstance(rows, list):
                rows = []
        except ValueError:
            rows = []
    rows.append(row)
    tmp = Path(str(path) + ".tmp")
    tmp.write_text(json.dumps(rows, indent=2) + "\n")
    tmp.replace(path)


MD_HEADER = (
    "| cycle | per-seed final E | chosen | best E so far | start state | wall min |\n"
    "|---|---|---|---|---|---|\n"
)


def append_results_md(path, text, header_needed, preamble=None):
    with open(path, "a") as f:
        if header_needed:
            if preamble:
                f.write(preamble)
            f.write(MD_HEADER)
        f.write(text)


def main():
    ap = argparse.ArgumentParser(description="cycle driver for relaxed_walk5")
    ap.add_argument("n", type=int)
    ap.add_argument("start", help="'-' (interval sphere), a faces .json, or a .raw state")
    ap.add_argument("outdir")
    ap.add_argument("--cycles", type=int, required=True)
    ap.add_argument("--seeds", type=int, required=True)
    ap.add_argument("--seconds", type=float, required=True)
    ap.add_argument("--thot", type=float, required=True)
    ap.add_argument("--tcold", type=float, required=True)
    ap.add_argument("--pb", type=float, default=0.15, help="RW_PB")
    ap.add_argument("--target", type=float, default=0.5, help="RW_TARGET")
    ap.add_argument("--seedbase", type=int, default=1000)
    ap.add_argument("--lambda0", type=float, default=None,
                    help="RW_LAMBDA0: duplicate weight at the start of each run")
    ap.add_argument("--lambda1", type=float, default=None,
                    help="RW_LAMBDA1: duplicate weight at the end of each run")
    ap.add_argument("--lambda-period", type=float, default=None,
                    help="RW_LAMBDA_PERIOD: seconds of the lambda triangle wave (0 = linear ramp)")
    ap.add_argument("--temps", default=None,
                    help="RW_TEMPS: comma-separated replica ladder; thot/tcold are still "
                         "passed on the command line")
    ap.add_argument("--chunk", type=int, default=None,
                    help="RW_CHUNK: steps per replica between exchange attempts")
    ap.add_argument("--select", choices=("energy", "best"), default="energy",
                    help="stdout field that picks the cycle winner (default: energy)")
    ap.add_argument("--keep-worse", action="store_true",
                    help="always advance to the winner's -last.raw, even if its energy is "
                         "above the best so far")
    a = ap.parse_args()

    cmdline = "python3 " + " ".join(shlex.quote(x) for x in sys.argv)

    if not BINARY.exists():
        sys.exit("missing binary: %s" % BINARY)

    outdir = Path(a.outdir).resolve()
    outdir.mkdir(parents=True, exist_ok=True)
    results_md = outdir / "results.md"
    results_json = outdir / "results.json"
    state_path = outdir / "state.json"

    start = a.start if a.start == "-" else str(Path(a.start).resolve())
    best_state = start
    best_energy = float("inf")
    first_cycle = 1

    st = load_state(state_path)
    if st:
        if st.get("found"):
            print("state.json says a solution was already found (%s); nothing to do."
                  % st.get("found"))
            return 0
        best_state = st.get("best_state", start)
        be = st.get("best_energy")
        best_energy = float("inf") if be is None else float(be)
        first_cycle = int(st.get("next_cycle", 1))
        print("resuming at cycle %d, best E=%s, state=%s"
              % (first_cycle, "inf" if best_energy == float("inf") else int(best_energy),
                 best_state))

    if first_cycle > a.cycles:
        print("nothing to do: next_cycle=%d > --cycles=%d" % (first_cycle, a.cycles))
        return 0

    env = dict(os.environ)
    env["RW_TARGET"] = str(a.target)
    env["RW_PB"] = str(a.pb)
    if a.temps:
        env["RW_TEMPS"] = a.temps        # replica ladder; thot/tcold still on argv
    else:
        env.pop("RW_TEMPS", None)        # single annealed walk thot -> tcold
    for name, val in (("RW_LAMBDA0", a.lambda0),
                      ("RW_LAMBDA1", a.lambda1),
                      ("RW_LAMBDA_PERIOD", a.lambda_period),
                      ("RW_CHUNK", a.chunk)):
        if val is not None:
            env[name] = str(val)
    # exactly what the children get, for results.json / state.json
    rw_env = {k: env[k] for k in sorted(env) if k.startswith("RW_")}

    options = {
        "pb": a.pb, "target": a.target, "lambda0": a.lambda0, "lambda1": a.lambda1,
        "lambda_period": a.lambda_period, "temps": a.temps, "chunk": a.chunk,
        "select": a.select, "keep_worse": a.keep_worse,
    }

    if not results_md.exists():
        append_results_md(results_md, "", True,
                          preamble="Command: `%s`\n\nchild env: %s; select=%s; keep_worse=%s\n\n"
                                   % (cmdline,
                                      " ".join("%s=%s" % kv for kv in sorted(rw_env.items()))
                                      or "(none)",
                                      a.select, a.keep_worse))

    for c in range(first_cycle, a.cycles + 1):
        t0 = time.time()
        start_state = best_state
        procs = []
        for k in range(1, a.seeds + 1):
            seed = a.seedbase + 100 * c + k
            prefix = outdir / ("c%d-s%d" % (c, k))
            cmd = [str(BINARY), str(a.n), str(a.seconds), str(seed), str(prefix),
                   str(a.thot), str(a.tcold), start_state]
            fo = open(str(prefix) + ".out", "w")
            fe = open(str(prefix) + ".err", "w")
            p = subprocess.Popen(cmd, cwd=str(HERE), env=env, stdout=fo, stderr=fe)
            procs.append({"k": k, "seed": seed, "prefix": prefix, "proc": p,
                          "files": (fo, fe), "cmd": cmd})

        try:
            for pr in procs:
                pr["rc"] = pr["proc"].wait()
        except KeyboardInterrupt:
            for pr in procs:
                pr["proc"].terminate()
            for pr in procs:
                pr["proc"].wait()
            for pr in procs:
                for fh in pr["files"]:
                    fh.close()
            print("interrupted during cycle %d; state.json not advanced" % c)
            return 130
        for pr in procs:
            for fh in pr["files"]:
                fh.close()

        runs = []
        for pr in procs:
            prefix = pr["prefix"]
            res = parse_stdout_json(str(prefix) + ".out")
            venn_json = Path(str(prefix) + "-venn.json")
            runs.append({
                "k": pr["k"], "seed": pr["seed"], "prefix": str(prefix),
                "rc": pr.get("rc"), "result": res,
                "venn_json": str(venn_json) if venn_json.exists() else None,
                "native_check": native_check_lines(str(prefix) + ".err"),
            })

        wall_min = (time.time() - t0) / 60.0

        # pick the winner on the --select field, ties broken by the other one
        ranked = sorted(runs, key=lambda r: energy_key(r, a.select))
        winner = ranked[0]
        w_energy = energy_key(winner, a.select)[0]

        improved = w_energy <= best_energy
        usable = winner["result"] is not None
        if improved and usable:
            best_state = (winner["prefix"] + "-best.raw") if (a.select == "best" and os.path.exists(winner["prefix"] + "-best.raw")) else (winner["prefix"] + "-last.raw")
            best_energy = w_energy
            note = ""
        elif a.keep_worse and usable:
            # advance anyway: schedules whose reported E rises while the
            # weighted energy falls would otherwise stall on an old state
            best_state = (winner["prefix"] + "-best.raw") if (a.select == "best" and os.path.exists(winner["prefix"] + "-best.raw")) else (winner["prefix"] + "-last.raw")
            note = "advanced anyway (--keep-worse)"
        else:
            note = "no improvement"

        per_seed = " ".join(
            "s%d=%s" % (r["k"], "ERR" if r["result"] is None else r["result"]["energy"])
            for r in runs)
        best_str = "inf" if best_energy == float("inf") else str(int(best_energy))

        # did anything finish?
        finished = [r for r in runs
                    if (r["result"] is not None and r["result"].get("complete")) or r["venn_json"]]

        row = {
            "cycle": c, "n": a.n, "seeds": a.seeds, "seconds": a.seconds,
            "thot": a.thot, "tcold": a.tcold, "pb": a.pb, "target": a.target,
            "seedbase": a.seedbase, "options": options, "rw_env": rw_env,
            "start_state": start_state, "wall_minutes": round(wall_min, 3),
            "runs": runs, "chosen_seed": winner["seed"], "chosen_k": winner["k"],
            "chosen_energy": None if w_energy == float("inf") else int(w_energy),
            "best_energy": None if best_energy == float("inf") else int(best_energy),
            "best_state": best_state, "note": note,
        }

        md = "| %d | %s | s%d (seed %d) | %s | %s | %.2f |%s\n" % (
            c, per_seed, winner["k"], winner["seed"], best_str,
            start_state if start_state == "-" else os.path.relpath(start_state, outdir),
            wall_min, (" " + note) if note else "")
        summary = ("cycle %d: %s -> chosen s%d (seed %d) E=%s, best E=%s, %.1f min%s"
                   % (c, per_seed, winner["k"], winner["seed"],
                      "ERR" if w_energy == float("inf") else int(w_energy),
                      best_str, wall_min, (" [" + note + "]") if note else ""))

        found_tag = None
        if finished:
            f = finished[0]
            tag = "FOUND-%d-c%d-s%d" % (a.n, c, f["k"])
            found_tag = tag
            src_json = f["venn_json"] or (f["prefix"] + "-last.json")
            src_raw = (f["prefix"] + "-venn.raw") if f["venn_json"] else (f["prefix"] + "-last.raw")
            dst_json = outdir / (tag + ".json")
            dst_raw = outdir / (tag + ".raw")
            for src, dst in ((src_json, dst_json), (src_raw, dst_raw)):
                try:
                    shutil.copyfile(src, dst)
                except OSError as e:
                    md += "\nCopy failed for `%s`: %s\n" % (src, e)

            chk = run_checker(dst_json, a.n)
            row["found"] = {
                "tag": tag, "seed": f["seed"], "k": f["k"],
                "source_json": src_json, "source_raw": src_raw,
                "json": str(dst_json), "raw": str(dst_raw),
                "checker": chk, "native_check": f["native_check"],
            }
            md += ("\n**SOLUTION** cycle %d seed %d -> `%s.json` / `%s.raw`\n"
                   "- independent gks_scaffold check: **%s**%s\n"
                   "- native check (stderr): %s\n\n"
                   % (c, f["seed"], tag, tag,
                      "PASSED" if chk.get("ok") else "FAILED",
                      "" if chk.get("ok") else (" -- " + str(chk.get("error") or
                                                             chk.get("report")))[:1500],
                      "; ".join(f["native_check"]) or "(none)"))
            summary += ("\nSOLUTION %s: independent check %s; native: %s"
                        % (tag, "PASSED" if chk.get("ok") else "FAILED",
                           "; ".join(f["native_check"]) or "(none)"))

        append_results_md(results_md, md, False)
        append_results_json(results_json, row)
        save_state(state_path, {
            "n": a.n, "outdir": str(outdir), "start": start,
            "cycles": a.cycles, "seeds": a.seeds, "seconds": a.seconds,
            "thot": a.thot, "tcold": a.tcold, "pb": a.pb, "target": a.target,
            "seedbase": a.seedbase, "options": options, "rw_env": rw_env,
            "cmdline": cmdline,
            "best_state": best_state,
            "best_energy": None if best_energy == float("inf") else int(best_energy),
            "next_cycle": c + 1, "found": found_tag,
        })

        print(summary, flush=True)
        if found_tag:
            print("stopping: solution written to %s" % (outdir / found_tag), flush=True)
            return 0

    print("done: %d cycles, best E=%s, state=%s"
          % (a.cycles, "inf" if best_energy == float("inf") else int(best_energy), best_state))
    return 0


if __name__ == "__main__":
    sys.exit(main())
