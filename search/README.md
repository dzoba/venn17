# relaxed-walk: Metropolis walk on labelled quadrangulations with duplicate labels allowed (claude, 2026-09-17)

Why: strict growth (v3..v15) jams at 17 (98.3%) because a lens insertion is legal only when BOTH new labels are missing,
and at the plateau no such coincidence exists (legal L ~ 0). Every earlier method kept "no duplicate regions" as a hard
constraint. Here it is a penalty: state = Z_n-symmetric quadrangulation of the sphere by cube squares whose vertices are
REGIONS (objects) carrying labels, several regions may carry the same label; energy E = sum_L |mult(L) - 1| = missing +
duplicates. E = 0 is a simple symmetric Venn diagram: the moves never change the number of components of a curve, and
verifyVenn() re-checks natively (all labels once, Euler 2, rotation symmetry on darts, each curve one cycle) before a
state is exported as a diagram. Metropolis at temperature T: accept with prob min(1, exp(-dE_orbit / T)).

Moves (half-edge map, each applied to all n rotation images, rejected if the images' dart footprints overlap):
- RII (lens insertion) at dart u->ua: faces ab@u, ac@u -> the other four faces of the 3-cube; creates regions u^b^c, u^a^b^c.
- inverse RII at dart x->y with deg x = deg y = 3 and the 4-face pattern: removes the two regions.
- RIII (triangle flip) at dart out of a degree-3 vertex v: v -> v^a^b^c.
Half insertion (one new label missing, the other already present) costs 0: holes and duplicates diffuse and annihilate.

Program: `relaxed_walk.cpp` (sha256 in SHA256SUMS). CLI:
  ./relaxed_walk n seconds seed out_prefix T0 T1 [load|-] [--strict] [pT pR] [reportEvery] [exportEvery]
load: `-` = interval sphere; a v13-style export (faces of LSB-first label strings; must be label-unique); or `*.raw`
(exact state from this program, duplicates allowed). Outputs: <prefix>-last.raw/.json every exportEvery s and at the end;
<prefix>-venn.json/.raw when E hits 0 (only claimed if the native check passes; verify independently with
gks_scaffold.check afterwards). stdout: one JSON line. RW_CHECK=1 runs the full structural check after every accepted move.
Raw state format (for external scaffolds, e.g. a resolved GKS diagram): line 1 `n V D`; then V lines `alive label rotv`;
then D lines `alive twin next orig axis rotd` (dart = half-edge; next = next dart around the face, faces are 4-cycles of
cube-square labels; rotd/rotv = image under label rotation bit i -> i-1; twin swaps orientation).

Results log below (times on a loaded machine).
- n=7: instant (RW_CHECK on: every move keeps the structure). n=11 blind, T=0.3: 10.7 / 27.0 / 2.7 s (seeds 1-3), all
  three pass the Python checker independently.
- DECISIVE 13 TEST (13:39): source scaling/m1-13/s2-c6-grow.json = 8166/8192 labels (26 missing), never finished by strict
  v13 growth (1020 s) + 6 repair_v2 cycles. Relaxed walk T=0.2: seeds 1, 2 reach E=0 in 73.7 s and 27.8 s, native check
  passed (stall13/T0.2-s*-venn.json). T=0.35 melts: missing -> 0 but ~1,500 duplicate regions persist (too hot).
  So the strict plateau IS a jam of the no-duplicate constraint, and the relaxed walk unjams it at 13.
- 17 plateau test launched 13:40: p17/ from queue/best.json (2244 missing), T = 0.10/0.15/0.20/0.25, 3600 s each.
- 13 blind at T=0.3 (cal13/): 0/4 in 900 s, best E 208-234, ~600-800 duplicates: too hot for blind 13. Rerun at 0.2/0.15 (cal13b/).
- 17 plateau, v1, first 4 min: T=0.10 E 2244 -> 2074 (missing 1700, dups 374); T=0.15 best 2142; T=0.20 E ~3200 (melted);
  T=0.25 E ~6000 (melted). Added T=0.00/0.03/0.05/0.07 and an anneal 0.10 -> 0 (p17/). Killed the 0.20/0.25 runs.
- `relaxed_walk2.cpp`: + targeted proposals (env RW_TARGET, default 0.5 = fraction of proposals that are targeted):
  pick a random MISSING label L, random axes b != c, a random region with label L^b^c, and the dart out of it whose two
  faces have axes {a,b} and {a,c}: the lens there creates L (dE = -2 or 0); or pick a random DUPLICATED label, a random
  region carrying it of degree 3, and try RIII / inverse RII on it. Same moves, same checks; only the proposal changes.
  Stalled 13 state: 2.3 s / 8.2 s (v1: 73.7 / 27.8 s). Blind 11: 10.4 / 2.0 / 13.3 s. RW_CHECK at 7 passes.
- 17 plateau with v2 launched 13:53 (p17/v2-T0.05-s1, v2-T0.10-s1, 3600 s).
- 13 blind, v1 (cal13b/): T=0.2 completes in 224.8 s and 207.8 s (seeds 1, 2), matching the strict engine's blind median
  (235 s); T=0.15: 585 s and one 900 s timeout at E=52. So the relaxed walk is a full replacement for strict growth at 13.
- 17 plateau at 13 min (v1, T=0.10): E=2040 (missing 1649 + dups 391); every low-T run sits at E 2040-2108 with
  annihilations (-34 each) about one per 2 min: diffusion-limited. v2 keeps dups at ~100-170 but E similar.
- `relaxed_walk3.cpp`: v2 + write journal (jset/jpush/jpop/jsetl record old values; jundoTo() restores exactly) and
  `hunt`: with prob RW_HUNT a proposal picks a duplicated region (or a missing label's lens site), then searches move
  sequences of depth RW_DEPTH (branch RW_BRANCH per level, all moves forced) for net dE < 0; failures are undone via the
  journal. RW_CHECK at 7 passes with depth 2 and 3. Hunts cost ~1 ms each, so RW_HUNT must be small (0.01-0.05) and they
  only pay at the plateau (blind 11 with RW_HUNT=0.05 is 100x slower). 17 plateau test p17/v3-* (20 min, from best.json).
- v3 hunts on the 17 plateau: 1 win per ~50,000 hunts (depth 2, branch 10); E after 60 s no better than v1/v2. Dropped.
- Diagnosis from the traces: at low T holes are almost immobile (a hole moves only through a degree-3 unique region whose
  flip target is exactly that label), at high T (0.20-0.25) everything moves but a gas of thousands of duplicates forms.
  All single-T runs reach E = 2006 (7 annihilations) and then crawl. Classic case for annealing / replica exchange.
- `relaxed_walk4.cpp`: replica exchange. RW_TEMPS=comma list of temperatures (one replica each; all start from the load),
  RW_CHUNK proposals per replica per round; after each round adjacent replicas swap states with the standard criterion
  (T=0 replica accepts a swap iff the neighbour's E is <= its own). State swapping is done by std::swap of the state
  vectors (O(1)). Blind 11 with temps 0/0.1/0.2/0.3: 0.4 s, 0.4 s (single T: 2-10 s); stalled 13: 0.4 s, 8.9 s; RW_CHECK
  at 7 passes. 17 plateau PT runs launched 14:16: p17/pt6 (0..0.25, 6 replicas), pt7 (0..0.22, 7), pt4 (0..0.30, 4).
- 13 blind with replica exchange (cal13pt/, temps 0/0.1/0.2/0.3): 144.3 s and 184.3 s. Faster than single-T (208-225 s)
  and than strict growth (235 s median).
- `relaxed_walk5.cpp` (codex's observation, board 681-683): the cube inverse RII only removes the 3-cube pattern (two
  degree-3 regions); a genuine BIGON (degree-2 region L between curves a and b, faces [L,A,M1,B] and [L,B,M2,A] with
  label M1 = label M2 = L^a^b, M1 != M2 as objects) was unremovable and frozen. Added kind 3 = bigon removal (delete L,
  merge M1 and M2, re-pair the four surviving darts; dE in {-2, 0}) and kind 4 = bigon insertion at a region M and two
  of its out-darts with distinct axes (M splits into M1, M2, new L = M^a^b; dE in {0, +2}). RW_PB = share of uniform
  proposals that try a bigon move (default 0.15); targeted dup removal uses bigon removal on degree-2 dups. Energy
  prediction is now an exact simulation over all n images (valid for non-prime n too). verifyStructure now also checks
  that every vertex's darts form one rotation cycle of length deg. RW_CHECK passes at 7, 9 (no symmetric 9-Venn exists;
  the walk reaches E=6 and stays), and 11. Stalled 13 with PT(3): 1.8 s / 0.3 s.
- 14:33 launched v5: p17/v5-pt6, v5-pt4, v5-T0 (from the plateau) and gks17/gks-v5-pt4, gks-v5-T0.05 (from codex's
  research/resolved-gks/gks17-quotient-resolved.raw, E=69394 duplicates, all labels present).
- 14:50 findings. Anneals gain only while hot: v2 anneal 0.25->0 reached E=1700 at T=0.19 (t=600 s) and stayed at 1700
  for the remaining 30 min of cooling; v5 anneal 0.30->0 reached 1768 at T=0.21 and froze. Productive window ~0.19-0.25.
  v4 PT ladder to 0.30: best 1700 at 36 min (exchange acceptance only 4%: ladder too sparse). GKS basin (codex
  gks17-quotient-resolved.raw, E=69394): v5 PT(0..0.15) reaches E=2244 = 255 missing + 1989 dups in 25 min; T=0.05 floors
  at 2414. Both basins arrive near E~2000 from opposite compositions.
- v5 now has RW_LAMBDA0/RW_LAMBDA1: duplicates weigh lambda in the acceptance rule (E reported unchanged), linear
  schedule over the run. Launched: window tests (p17/v5-hold0.20, v5-hold0.22, v5-anneal0.25-0.15, v5-ptwin with ladder
  0/0.16/0.18/0.20/0.22/0.24, scratch17/v5-scratch-hold0.20) and lambda anneals 0.3->1 at T=0.15 from both basins.

## cycle.py: unattended cycle driver (claude, 2026-09-17)

`cycle.py` runs relaxed_walk5 in cycles of S parallel seeds, chaining the best state forward:

```
python3 cycle.py <n> <start: - | file.json | file.raw> <outdir> \
    --cycles C --seeds S --seconds D --thot TH --tcold TC \
    [--pb 0.15] [--target 0.5] [--seedbase 1000]
```

Per cycle c: launch S processes `relaxed_walk5 n D seed outdir/c<c>-s<k> TH TC <best state>` with seeds
`seedbase+100*c+k`, k = 1..S, env RW_TARGET/RW_PB from the flags and RW_TEMPS cleared (so each run is a single walk
annealed linearly TH -> TC over D seconds, not a replica ladder). stdout/stderr go to `c<c>-s<k>.out/.err`. It waits for
all S (subprocess wait, no sleep polling), parses the one-line JSON from each stdout, and picks the lowest final
`energy`, ties broken by `best_energy`. The winner's `-last.raw` becomes the next cycle's start state only if its energy
is <= the current best; otherwise the previous state is kept and the row is marked `no improvement`.

Outputs in `outdir`: `results.md` (one table row per cycle: per-seed final energies, chosen seed, best E so far, start
state, wall minutes), `results.json` (same plus the full stdout JSON of every run), and `state.json`. Restarting the
driver on an existing `outdir` resumes from `state.json` at the next cycle with the recorded best state, so raising
`--cycles` (or changing D/TH/TC) continues an earlier run instead of restarting it.

Stop condition: if any run reports `complete=true` or leaves a `-venn.json`, the driver copies it to
`FOUND-<n>-c<c>-s<k>.json/.raw`, runs the independent `gks_scaffold.check` (via `oriented_faces`, in its own interpreter
from the polar-calibration directory), records both that verdict and the program's own `native check PASSED/FAILED`
stderr line in results.md, and exits. Both are recorded because a diagram with genuine bigons can fail the Python
checker while still being valid.

Calibration from the n=13 test runs (16-core machine also running 13 other walks, so step rates were about half):
- `--cycles 2 --seeds 3 --seconds 60 --thot 0.25 --tcold 0.0` from `-` (cycletest13/): E 8034 -> 78 -> 52, and four more
  resumed cycles reached 26 and sat there. No E=0.
- `--seconds 120 --thot 0.2 --tcold 0.15` from `-` (cycletest13-warm/): stuck at 182, then 156, then 78 after a 300 s cycle.
- Bare `relaxed_walk5 13 240 1 x 0.2 0.2 -` on the same machine reached E=0 at 54.7 s.
So short cycles are worse than one long walk at blind 13: annealing to TC=0 freezes the back half of every cycle, and
each restart re-melts from a cold state. Energy is quantized in steps of 2n (moves apply to full rotation orbits), which
is why independent seeds often report the identical E. Use D at least as long as the expected solve time at that
temperature (~210 s for blind 13 at T=0.2 per the runs above) and keep TC at or near TH; cycling pays for pushing a
plateau state forward, not for replacing a single long run. Note the binary's `t=` progress lines print `[T=...]` as T0,
not the live annealed temperature, so a ramp is not visible there.
- 15:03 local heating: RW_THOT sets a hot temperature used only for defect-targeted proposals (missing-label lens sites,
  duplicated regions); uniform proposals use the ladder/schedule temperature. Runs p17/v5-local-c0.05-h0.25 and -h0.30.
- cycle.py (Opus agent build) verified end to end at 7 (FOUND file + independent check) and chaining at 9; at 13 with
  cycles cooling to 0 it stalls at E=26, consistent with the window finding: cycles must hold inside the window.
- Window tests at 11 min: hold 0.20 -> 1904 (descending), hold 0.22 -> best 1938, anneal 0.25->0.15 -> 1938;
  from scratch at 0.20: 6375 missing after 11 min (strict growth needs ~1 h for that).
- 15:10 v4 ladder 0/0.10/0.20/0.30 (p17/pt4) finished: best E=1666 (1479 missing + 187 dups) at 60 min; exchange
  acceptance 3%. Saved as best/plateau-pt4-E1666.raw (replica 0 state at the end). Best plateau-derived state so far.
- 15:25 KEY RESULT: gks17/gks-v5-lam0.3-1.0-T0.15 (from codex's gks17-quotient-resolved.raw, duplicate weight lambda
  ramped 0.3 -> 1.0 over 60 min at T=0.15): E=986 at 28 min, best 884, only 34 missing labels (2 orbits), 952
  duplicates. Plateau-derived lambda run: best 1632. Local heating (RW_THOT): no gain (1972), dropped.
  Added RW_LAMBDA_PERIOD (triangle-wave lambda between LAMBDA0 and LAMBDA1). Checkpoint of the lambda run at ~25 min
  saved as best/gks-lam-checkpoint-1525.raw; continuation runs gks17/gksck-osc0.6-1.4-p600-T0.15 and gksck-lam1.2-T0.15.
  Also launched from the scaffold: lambda 0.3->1.0 at T=0.20, lambda 0.3->1.5 at T=0.15, lambda 0.2->1.0 seed 2,
  hold 0.22, ladder 0/0.1/0.2/0.3, lambda=2 at T=0.2.
- 15:27 MISSING-SET ANALYSIS (analysis/missing_overlap.py, Opus agent): the strict plateau and three plateau-derived
  relaxed states share 69 missing orbits (Jaccard 0.53-0.73, 50-70x chance; 90% of the shared set lies in core129),
  but the GKS-basin states and the from-scratch state have missing sets essentially DISJOINT from that core and from
  each other (Jaccard 0.00-0.02), and no orbit is missing in all seven states. The "persistent core" is a property of
  the strict-growth basin, not of the problem. Consequence: stop polishing the plateau basin; work the GKS basin and
  from-scratch with duplicate-weight schedules.
- 15:48 GKS basin + lambda ramp is the line. At 24 min: T=0.20 -> E=544 (best 408; 68 missing = 4 orbits, 476 dups);
  seed 2 at T=0.15 (lambda 0.2->1) -> 578 (34 missing); T=0.15 original at 53 min -> 782; hold 0.22 at lambda=1 -> best
  816; lambda 0.3->1.5 -> 884; lambda=2 fixed -> 3264 (bad); ladder to 0.30 -> 1224. Continuations from the 25-min
  checkpoint (osc, 1.2) did not beat their parent. From scratch with lambda=0.2 held at T=0.2: only 170 missing after
  21 min (6664 dups): coverage is easy at low lambda; duplicates are the whole endgame. Plateau controls: 1598-1700.
  Launched: ramp at T=0.22, 0.25, a 2-hour ramp at 0.20, and seed 3 at 0.20.
- 15:55 cycle.py schedule options (Opus agent). New flags, each forwarded to every child as an env var and only set
  when the flag is given: `--lambda0` (RW_LAMBDA0), `--lambda1` (RW_LAMBDA1), `--lambda-period` (RW_LAMBDA_PERIOD),
  `--temps` (RW_TEMPS, comma list; `--thot/--tcold` still go on the child's command line, so the ladder and the argv
  temperatures coexist as in the bare binary), `--chunk` (RW_CHUNK). `--pb`/`--target` are unchanged and still always
  set. Without `--temps`, RW_TEMPS is cleared as before, so the default is still one annealed walk thot -> tcold.
  Also `--select {energy,best}` (default energy) chooses which stdout field ranks the seeds in a cycle -- `best` ranks
  on `best_energy` instead of the final `energy`, useful when a run ends hot -- and `--keep-worse` makes the driver
  advance to the cycle winner's `-last.raw` even when its energy is above the best so far, for lambda schedules whose
  reported E (unweighted) rises while the weighted energy falls. `best E so far` stays the true minimum either way;
  only the chained state moves. The full command line, the RW_* variables actually handed to the children, and
  select/keep_worse are written once at the top of results.md when it is created, and into every results.json row and
  state.json (`options` / `rw_env` / `cmdline`). Resume is unchanged: state.json still drives `next_cycle` and the
  best state, and the options come from the resuming command line, so a schedule can be changed between resumes.
  Verified at 13: `--cycles 2 --seeds 3 --seconds 90 --thot 0.2 --tcold 0.2 --lambda0 0.5 --lambda1 1.0` from `-`
  (cycletest13b/) gave E 26 -> 0 and a FOUND file that passes the independent check; child stderr shows `lam=` walking
  0.56 -> 0.95 over each 90 s run, i.e. the ramp reaches the children.
- 15:55 the original GKS ramp (T=0.15) finished at E=782 (68 missing, 714 dups). Its trace: E 3910 (lambda 0.31) ->
  1428 (0.41) -> 1020 (0.53) -> 884 (0.63) -> 850 (0.70) -> 782 (1.0): the descent slows as lambda approaches 1.
  Plateau ramp finished at 1598. The T=0.20 ramp was already at 408 at 24 min: temperature matters as much as lambda.
- 16:25 BEST E=238 (gks-v5-lam0.3-1.0-T0.20 final: 34 missing = 2 orbits, 204 dups = 12 orbits), saved as
  best/gks-lam-T020-E272-t3300.raw (periodic export at t=3300, E=272; the final E=238 state is best/gks-lam-T020-E238-final.raw). Sweep at 34 min: T=0.25 best 204; seed 3 at 0.20 best 272; T=0.22 best 340; 2-h ramp 306
  at lambda 0.5. T=0.15 ramps end 340-782; hold 0.22 at lambda=1: 544; ladder to 0.30: 680; lambda=2: 3264.
  From scratch with the ramp at T=0.20: 1530 in 56 min. Cycle drivers started from the 238 state: cycles-mild/
  (lambda 0.85->1, 20-min cycles, 6 seeds) and cycles-strong/ (lambda 0.6->1, 40-min cycles, 6 seeds), T=0.20.
- 16:30 relaxed_walk5 now writes <prefix>-best.raw whenever a new best E (<= RW_BESTCAP, default 3000) is reached
  (5-s throttle); the T=0.20 ramp ended at 272 after touching 238, so keeping only the last state lost the best.
  cycle.py with --select best advances from -best.raw when present.
- 17:50 E=68 WITH ZERO MISSING LABELS: the 2-hour ramp (lambda 0.3->1.0, T=0.20) ended at E=68 = 68 duplicate regions
  (4 orbits), all 131,072 labels present; final state best/gks-2h-final.raw (sha256 35a7703b...), re-loads with
  structure OK. 60-min ramps: bests 102 (T=0.25), 170 (0.20 s3), 204 (0.22); finals 170-272. Hunts (depth 3-4) from
  the E=136 export: no gain. Endgame launched from the final state: endgame/cycles-mild (T=0.20, lambda 0.85->1,
  20-min cycles, 6 seeds), endgame/cycles-strong (T=0.25, lambda 0.6->1, 40-min, 6 seeds), endgame/hold-lam1-T0.20 and
  -T0.25 (4 h, lambda=1, best-save on). Hourly cron checks for FOUND files and verifies before any claim.
