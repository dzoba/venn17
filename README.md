# venn17

This repository holds six certificates for simple symmetric Venn diagrams together with
everything needed to check them: four independent 17-curve certificates (`certificates/venn17-*.json`,
found 2026-09-17), an 11-curve and a 13-curve certificate (`certificates/best11-s0.json`,
`certificates/v3-13-s0.json`), a standalone structural checker (`verify/`), the search program and
the exact run configurations that produced the four 17-curve solutions (`search/`), a pen-plotter
SVG exporter with rendered 11- and 13-curve drawings (`plotter/`), and a write-up (`paper/`).
`verify/RESULTS.md` records the checker's transcript on all six files: all six PASS every criterion
the checker tests, and all six are non-monotone by the Bultena-Grunbaum-Ruskey test in
`verify/monotone_test.py`.

## Verify a certificate in one command

```
python3 verify/verify.py certificates/venn17-gcp-s12.json
```

Python 3 with no third-party packages; about 10 seconds for a 17-curve certificate, under a second
for the 11- and 13-curve ones. Pass several files to check them in one run. The exit status is 0
only if every file passes.

`verify.py` loads the certificate, re-orients its faces with `interval_growth.oriented_faces`, runs
`gks_scaffold.check` on the result, prints every field of the report, and prints `RESULT: PASS`
only when all eight of these hold:

| criterion | meaning |
| --- | --- |
| `all_labels` | all 2^n labels present, each exactly once |
| `euler == 2` | V - E + F = 2, so the map is a sphere |
| every edge multiplicity `== 2` | each edge borders exactly two faces |
| `vertices_single_rotation_cycle` | the rotation at every vertex is a single cycle |
| `curves_two_sides_connected` | both sides of every curve are connected, so each curve is one Jordan curve |
| `rotation_symmetric` | the face set is invariant under the Z_n rotation of labels |
| `non_transversal_faces == 0` | every crossing is transversal (bit pattern w.w) |
| `repeated_vertex_faces == 0` | no face repeats a vertex |

`verify/gks_scaffold.py`, `verify/interval_growth.py` and `verify/gks_chains.py` are copied
unchanged from the scaffold work and share no code with the search program in `search/`.

## Certificate format

A certificate is the **dual map** of the arrangement, as JSON:

```json
{"n": 17, "labels": 131072, "faces": [["00011111001010111", "00011111101010111",
                                       "00011111101010011", "00011111001010011"], ...]}
```

Each label is an `n`-character **LSB-first** bit string naming one region of the arrangement: bit
`i` is `1` when the region is inside curve `i`. Each entry of `faces` is one vertex (crossing) of
the Venn diagram, given as the four labels of the regions around it, in cyclic order; consecutive
labels in a face differ in exactly one bit. A 17-curve certificate has 131,072 labels and 131,070
faces. `n`, `labels` and the other top-level keys vary between files and are ignored by the checker
apart from `n`.

## Contents

| path | what it is |
| --- | --- |
| `certificates/` | the six certificates and `SHA256SUMS` |
| `verify/verify.py` | the checker; `verify/RESULTS.md` is its output on all six certificates |
| `verify/monotone_test.py` | Bultena-Grunbaum-Ruskey monotonicity test |
| `search/relaxed_walk5.cpp` | the relaxed Metropolis walk that found the 17-curve solutions |
| `search/BUILD.md` | how to build it and the run configurations behind the four solutions |
| `search/README.md` | the running log of the search, copied unchanged |
| `plotter/plotter_svg.py` | pen-plotter SVG exporter, plus rendered 11- and 13-curve drawings |
| `paper/venn17.tex`, `paper/venn17.pdf` | the write-up |

`plotter_svg.py` expects the scaffold modules on its import path; run it as
`PYTHONPATH=verify python3 plotter/plotter_svg.py certificates/best11-s0.json`. It needs NumPy,
and rsvg-convert or Inkscape for the PNG preview.

## Checksums

`sha256`, as in `certificates/SHA256SUMS`:

| file | sha256 |
| --- | --- |
| `best11-s0.json` | `865d73add9779287f17580240cd2669a8e7fd9286d720c03f261878e52528271` |
| `v3-13-s0.json` | `f01d59b7cc843dcf824b40b50b8f616953e775f0b2b0df28bdefbfc0a1ea67e2` |
| `venn17-gcp-s12.json` | `87f981b849073daa79b1438f1bb895e6bcac1926fe1c141e9b2c7617a04ff29b` |
| `venn17-gcp-s14.json` | `eec8cd5520337c60b9ecdbd9bf006ceb10002decdac94b6d51f08b19ac54a342` |
| `venn17-gcp-s16.json` | `431857aa80891474d1e5a91228fc3bcbcdd0c2caa24180993fb4ea6ac8f75173` |
| `venn17-local-c3-s2.json` | `c178d7bdde6e02b1b0c2780339434095d3633b8bb77a7293e9d575d04ad7ae77` |

Check them with `cd certificates && shasum -a 256 -c SHA256SUMS`.
