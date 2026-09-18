# Building and running the search

## Build

```
c++ -O2 -std=c++17 -o relaxed_walk5 relaxed_walk5.cpp
```

No dependencies beyond a C++17 standard library. `README.md` in this directory is the
running log of the search, copied unchanged from the research tree.

## Command line

```
relaxed_walk5 n seconds seed out_prefix T0 T1 [load|-] [--strict] [pT pR] [reportEvery] [exportEvery]
```

`load` is a `.raw` state to start from (`-` starts from scratch). Duplicate regions are
weighted by lambda in the acceptance rule; lambda ramps linearly from `RW_LAMBDA0` to
`RW_LAMBDA1` over the run. Relevant environment variables: `RW_LAMBDA0`, `RW_LAMBDA1`,
`RW_LAMBDA_PERIOD`, `RW_TEMPS`, `RW_PB`, `RW_TARGET`, `RW_CHUNK`, `RW_BESTCAP`.

On reaching energy 0 the program writes `<out_prefix>-venn.json` (the certificate) and
`<out_prefix>-venn.raw` (the full half-edge state).

`cycle.py` is an unattended driver: it launches S parallel `relaxed_walk5` processes from
the current best state, keeps the lowest-energy result as the next cycle's start, and stops
when a run reports `complete=true`. `trace.py` summarises `relaxed_walk5` stderr traces.

## Starting state

All four 17-curve solutions descend from the same input: `gks17-quotient-resolved.raw`, a
resolved Griggs-Killian-Savage 17 scaffold (all 2^17 labels present, 69,394 duplicate
regions; header `17 200466 801856`, sha256
`d4f226142dcf0cadc281f62130340a142fedb30d72ae2e71c40413d0a1449551`). That 28 MB file is not
included in this repository.

## The four runs that produced the certificates

### venn17-gcp-s12, venn17-gcp-s14, venn17-gcp-s16

One 3-hour anneal per seed, 30 seeds (one per core) on a single `n2-custom-30-30720` Spot VM
in `us-central1-a`, started 2026-09-17 16:32:58 EDT. Odd seeds ran at T=0.20, even seeds at
T=0.25; seeds 12, 14 and 16 are all T=0.25. Each seed ran:

```
RW_TARGET=0.5 RW_PB=0.15 RW_LAMBDA0=0.3 RW_LAMBDA1=1.0 \
  ./relaxed_walk5 17 10800 $SEED out/s$SEED 0.25 0.25 \
    gks17-quotient-resolved.raw 0.25 0.25 60 300 \
    > out/s$SEED.out 2> out/s$SEED.err
```

(the trailing `0.25 0.25 60 300` are `pT pR reportEvery exportEvery`). Reported results:

| seed | wall seconds to energy 0 | steps | final |
| --- | --- | --- | --- |
| 12 | 10472.3 | 1,437,885,945 | energy 0, missing 0, dups 0, labels 131072 |
| 14 | 10252.2 | 1,429,594,256 | energy 0, missing 0, dups 0, labels 131072 |
| 16 | 6998.8 | 777,022,221 | energy 0, missing 0, dups 0, labels 131072 |

### venn17-local-c3-s2

A `cycle.py` run on the local machine, 40-minute cycles of 6 seeds at T=0.25 with lambda
ramping 0.6 -> 1.0 inside each cycle:

```
python3 cycle.py 17 best/gks-2h-final.raw endgame/cycles-strong \
    --cycles 20 --seeds 6 --seconds 2400 --thot 0.25 --tcold 0.25 \
    --lambda0 0.6 --lambda1 1.0 --select best --seedbase 50000
```

The driver forwarded `RW_LAMBDA0=0.6 RW_LAMBDA1=1.0 RW_PB=0.15 RW_TARGET=0.5` to each child.
Its start state `best/gks-2h-final.raw` was the end of a separate 2-hour lambda 0.3 -> 1.0
ramp at T=0.20 from `gks17-quotient-resolved.raw`, which had reached energy 68 (68 duplicate
regions, zero missing labels).

Cycle 3, seed 2 (seed number 50302) reached energy 0 at t=1972.8 s after 732,703,945 steps:
`energy 0, missing 0, dups 0, best_energy 0, complete true, labels 131072`.
