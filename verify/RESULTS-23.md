# Checker transcript, 23-curve certificates (2026-10-06)

`python3 verify/verify.py <file>` on each of the five 23-curve certificates (found 2026-10-06 at 04:00, 06:15, 08:58 and 10:54 UTC, i.e. 00:00, 02:15, 04:58 and 06:54 EDT, for `c25`, `c19`, `c21` and `f4`, and at about 02:46 UTC on 2026-10-06, i.e. 22:46 EDT on 2026-10-05, for `c6p`), followed by `verify/monotone_test.py`. The checker is the one in this repository at commit `5f08c24`, run on an Apple M4 Max (16 cores, 128 GB): `c25` and `c19` on 2026-10-06 06:43 to 07:07 UTC, `c21` on 2026-10-06 10:15 to 10:26 UTC, `c6p` on 2026-10-06 10:37 to 10:48 UTC, `f4` on 2026-10-06 about 11:36 to 11:46 UTC. The five certificates are not in `certificates/` (889,192,322 bytes each; they are release assets and on Zenodo); they were checked in the directory the author keeps them in, and the `file` line of each transcript and the monotone-test line printed that directory's absolute path. The directory part has been removed from those lines here, leaving the bare file name; nothing else in the transcript depends on the path. The `maximum resident set size` lines are the first two lines of the recorded `.time` output of the same runs (the rest of that output is omitted). The sections are in verification order, which is the order of the five `venn23-*` lines in `certificates/SHA256SUMS`; the order of discovery is `c6p`, `c25`, `c19`, `c21`, `f4`.

## venn23-c25-s230025.json
```
file        venn23-c25-s230025.json
n           23
faces       8388606 listed, 8388606 distinct
report:
  E                                16777212
  F                                8388606
  V                                8388608
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 16777212}
  euler                            2
  face_sizes                       {4: 8388606}
  non_transversal_faces            0
  repeated_vertex_faces            0
  rotation_symmetric               True
  venn_dual_valid                  True
  vertices_single_rotation_cycle   True
criteria:
  ok  all_labels
  ok  euler == 2
  ok  edge multiplicities all 2
  ok  vertices_single_rotation_cycle
  ok  curves_two_sides_connected
  ok  rotation_symmetric
  ok  non_transversal_faces == 0
  ok  repeated_vertex_faces == 0
elapsed     693.2 s
RESULT: PASS
```
recorded `.time` output (first two lines):
```
      697.18 real       648.26 user         8.78 sys
         20038762496  maximum resident set size
```
monotone test:
```
venn23-c25-s230025.json: n=23 labels=8388608 complete=True non_monotone_labels=1213066 e.g. ['00000000000000000011001', '00000000000000000011011', '00000000000000000011111']
```

## venn23-c19-s230019.json
```
file        venn23-c19-s230019.json
n           23
faces       8388606 listed, 8388606 distinct
report:
  E                                16777212
  F                                8388606
  V                                8388608
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 16777212}
  euler                            2
  face_sizes                       {4: 8388606}
  non_transversal_faces            0
  repeated_vertex_faces            0
  rotation_symmetric               True
  venn_dual_valid                  True
  vertices_single_rotation_cycle   True
criteria:
  ok  all_labels
  ok  euler == 2
  ok  edge multiplicities all 2
  ok  vertices_single_rotation_cycle
  ok  curves_two_sides_connected
  ok  rotation_symmetric
  ok  non_transversal_faces == 0
  ok  repeated_vertex_faces == 0
elapsed     734.3 s
RESULT: PASS
```
recorded `.time` output (first two lines):
```
      737.06 real       670.69 user         5.53 sys
         21378744320  maximum resident set size
```
monotone test:
```
venn23-c19-s230019.json: n=23 labels=8388608 complete=True non_monotone_labels=1202417 e.g. ['00000000000000000000101', '00000000000000000001010', '00000000000000000010001']
```

## venn23-c21-s230021.json
```
file        venn23-c21-s230021.json
n           23
faces       8388606 listed, 8388606 distinct
report:
  E                                16777212
  F                                8388606
  V                                8388608
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 16777212}
  euler                            2
  face_sizes                       {4: 8388606}
  non_transversal_faces            0
  repeated_vertex_faces            0
  rotation_symmetric               True
  venn_dual_valid                  True
  vertices_single_rotation_cycle   True
criteria:
  ok  all_labels
  ok  euler == 2
  ok  edge multiplicities all 2
  ok  vertices_single_rotation_cycle
  ok  curves_two_sides_connected
  ok  rotation_symmetric
  ok  non_transversal_faces == 0
  ok  repeated_vertex_faces == 0
elapsed     609.7 s
RESULT: PASS
```
recorded `.time` output (first two lines):
```
      612.41 real       606.98 user         3.48 sys
         21373550592  maximum resident set size
```
monotone test:
```
venn23-c21-s230021.json: n=23 labels=8388608 complete=True non_monotone_labels=1209731 e.g. ['00000000000000000011001', '00000000000000000011011', '00000000000000000011111']
```

## venn23-c6p-s1065101.json
```
file        venn23-c6p-s1065101.json
n           23
faces       8388606 listed, 8388606 distinct
report:
  E                                16777212
  F                                8388606
  V                                8388608
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 16777212}
  euler                            2
  face_sizes                       {4: 8388606}
  non_transversal_faces            0
  repeated_vertex_faces            0
  rotation_symmetric               True
  venn_dual_valid                  True
  vertices_single_rotation_cycle   True
criteria:
  ok  all_labels
  ok  euler == 2
  ok  edge multiplicities all 2
  ok  vertices_single_rotation_cycle
  ok  curves_two_sides_connected
  ok  rotation_symmetric
  ok  non_transversal_faces == 0
  ok  repeated_vertex_faces == 0
elapsed     632.9 s
RESULT: PASS
```
recorded `.time` output (first two lines):
```
      635.72 real       628.68 user         4.67 sys
         22484844544  maximum resident set size
```
monotone test:
```
venn23-c6p-s1065101.json: n=23 labels=8388608 complete=True non_monotone_labels=1207914 e.g. ['00000000000000000011001', '00000000000000000011011', '00000000000000000011111']
```

## venn23-f4-s254004.json
```
file        venn23-f4-s254004.json
n           23
faces       8388606 listed, 8388606 distinct
report:
  E                                16777212
  F                                8388606
  V                                8388608
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 16777212}
  euler                            2
  face_sizes                       {4: 8388606}
  non_transversal_faces            0
  repeated_vertex_faces            0
  rotation_symmetric               True
  venn_dual_valid                  True
  vertices_single_rotation_cycle   True
criteria:
  ok  all_labels
  ok  euler == 2
  ok  edge multiplicities all 2
  ok  vertices_single_rotation_cycle
  ok  curves_two_sides_connected
  ok  rotation_symmetric
  ok  non_transversal_faces == 0
  ok  repeated_vertex_faces == 0
elapsed     614.4 s
RESULT: PASS
```
recorded `.time` output (first two lines):
```
      617.16 real       612.95 user         3.90 sys
         21374074880  maximum resident set size
```
monotone test:
```
venn23-f4-s254004.json: n=23 labels=8388608 complete=True non_monotone_labels=1207523 e.g. ['00000000000000000011001', '00000000000000000011011', '00000000000000000011111']
```

## Checksums

`cd certificates && shasum -a 256 -c SHA256SUMS --ignore-missing` on the in-tree files:
```
best11-s0.json: OK
v3-13-s0.json: OK
venn17-gcp-s12.json: OK
venn17-gcp-s14.json: OK
venn17-gcp-s16.json: OK
venn17-local-c3-s2.json: OK
venn19-closure-s195001.json: OK
venn19-closure-s195002.json: OK
venn19-closure-s196001.json: OK
venn19-closure-s196002.json: OK
venn19-closure-s196004.json: OK
venn19-closure-s196007.json: OK
venn19-fresh-s192015.json: OK
venn19-fresh-s190002.json: OK
venn19-fresh-s192007.json: OK
venn19-ramp12h-s192102.json: OK
venn19-ramp12h-s192104.json: OK
venn19-ramp12h-s192106.json: OK
```
The 23-curve lines of `SHA256SUMS`, checked against the decompressed files in the directory they were verified in (`grep venn23 SHA256SUMS | shasum -a 256 -c -`, run 2026-10-06 13:08 UTC on all five lines, after the `f4` line was added; earlier runs at 10:41 UTC and 11:31 UTC checked the first three and the first four lines with the same result):
```
venn23-c25-s230025.json: OK
venn23-c19-s230019.json: OK
venn23-c21-s230021.json: OK
venn23-c6p-s1065101.json: OK
venn23-f4-s254004.json: OK
```

## Distinctness

Canonical forms over all 4n = 92 label maps (2 pole swaps x 2 mirrors x 23 rotations), by the definition used for the 19-curve certificates (`canon_venn.py`: the minimum over the 4n maps of sha256(repr(sorted canonical faces)); run here with `canon_venn_cached.py`, the same hash definition with the 92 maps of one file shared among 3 forked workers, which writes each file's form to a `.canon.json` sidecar). The form of each file was computed in a run of its own (output `files 1 isomorphism classes 1` each): the first two finished 2026-10-06 07:37 UTC (2,978 s and 2,974 s of wall per file), the third 09:56 UTC (1,902 s), the fourth (`c6p`) 11:12 UTC (2,430 s), the fifth (`f4`) about 12:03 UTC (2,260 s). The comparison of the five was then run on all five files at about 12:06 UTC, in discovery order, and read the forms back from the sidecars; its output in full:
```
029acb28b5b43effa4e72b981e19db083624e4192d4c6e042e740f0e1359db3b venn23-c6p-s1065101.json cached
400e52795ed400dfbb2672ff25aab73d1edf2fe20cf50cc09b54387f707c32df venn23-c25-s230025.json cached
337076aeb90fd04f3651f8a713ca099dd87224004acfd5f2b9bce2731e34b1d8 venn23-c19-s230019.json cached
56f659b4663acb1f9339861756ebc8f451eddef08f634d9b5edca072ef8f6425 venn23-c21-s230021.json cached
2670bfda8bc0f91eb1cb493cdad9df9e891340d7f929bb6999ecd4a933cdfd60 venn23-f4-s254004.json cached
files 5 isomorphism classes 5
029acb28b5b4 1 ['venn23-c6p-s1065101.json']
400e52795ed4 1 ['venn23-c25-s230025.json']
337076aeb90f 1 ['venn23-c19-s230019.json']
56f659b4663a 1 ['venn23-c21-s230021.json']
2670bfda8bc0 1 ['venn23-f4-s254004.json']
```
(An earlier comparison of the first four, run at 11:16 UTC before `f4` was found, gave `files 4 isomorphism classes 4` with the same four forms.) The five hashes differ, so no two of the five certificates are isomorphic under any rotation, mirror or pole swap. Codex's region-degree histograms (the number of crossings around each region, counted by a separate streaming reader) differ for all ten pairs among the five as well, which separates all five under arbitrary relabelings, not only the 92 symmetries: the first four were compared pairwise before `f4` was found, and `f4`'s histogram, computed at 12:16 UTC from the `.json` file with its sha256 checked before and after, differs from each of the other four (2,944,046 regions of degree 3 in `f4` against 2,951,107, 2,950,003, 2,937,192 and 2,947,197 in `c25`, `c19`, `c21` and `c6p`). As unordered label quadruples in a fixed frame the `c25` and `c19` face sets have symmetric difference 15,122,914 of 16,777,212 (they share 827,149 of 8,388,606 faces each); the figure is the same under every rotation of the labels because each set is Z_23-invariant. (This face-set comparison was run for `c25` and `c19` only.)

## Other checks

- The third checker written by Codex, which audits the raw search state directly (a pinned native reimport by its inspector `qinspect`, sha256 `37af40c6...`) and was run on the first nine 19-curve certificates, was run on all five 23-curve raw states on 2026-10-06, serially on the first four 10:15 to 10:19 UTC and on `f4` at 12:15 UTC, with the input's sha256 checked before and after each run (c25 raw `812349fa...`, c19 raw `51b848a5...`, c21 raw `b8a89f59...`, c6p raw `6e569819...`, f4 raw `f02f895c...`). All five: status PASS, order 23, missing 0, duplicates 0, energy 0, V 8,388,608, E 16,777,212, F 8,388,606, Euler characteristic 2, and the expected 23-fold orbit counts with two fixed polar vertices. For c25 the first wrapper receipt reported FAIL ("rotation/orbit count mismatch") from the wrapper's own arithmetic, which had assumed every vertex orbit has 23 members; the native inspector had exited 0 with the figures above, and a reassessed receipt (10:17 UTC) re-checks the saved inspector output with the two fixed poles accounted for, confirms the input and inspector hashes, and records that no rerun took place. The receipts (one JSON file per state, plus the reassessed one for c25) are kept by the author with the raw states; the raw states themselves are not published, since every claim about a certificate is checkable from the `.json` file alone.
- A full proof run (`run_candidate.py ... --prove`) of the Lean development ported to n = 23 was launched on `venn23-c25-s230025.json` (sha256 `adc5a02e...`) at 2026-10-06 10:17:57 UTC, with Lean 4.32.1 and the pinned Mathlib of the 19-curve proof. Its compiled finite checker (`venn_check`) exited 0 with `regions := 8388608, arcs := 16777212, crossings := 8388606` and every one of its twelve flags true (`squareCrossings`, `twoFacesPerArc`, `connectedMap`, `orientedSurface`, `singleVertexLinks`, `eulerTwo`, `singleCurveCycles`, `connectedCurveSides`, `everyPattern`, `simpleCrossings`, `rotationalSymmetry`, `poleRotationOneStep`), ending `PASS: all finite combinatorial checks. This run does not check geometric realization.`; the meridian, sector and pole witnesses the geometric proof consumes were then generated (`WITNESSES_PROPOSED_NOT_PROVED`). The final stage, `lake build Venn23 VennTopology`, failed at about 10:42 UTC: the run's own resource guard stopped it with "owned process group RSS exceeds 16384 MiB", the 16 GiB limit that run had been given (`formal_geometry_proved: false`). So no theorem has been proved for a 23-curve certificate; the unfinished build is being resumed from its cache and the witnesses already generated, with a 64 GiB limit and no change to the statements or axioms [TBD: Lean 23 result on c25 from the resumed build; this release waits for it].
- The pilot `c6p` was found by the ordinary-walk arm of a pilot of Codex's memory-assisted engine at about 22:46 EDT on 5 October (its own native validation at 22:49 EDT, 71 minutes before c25) and recognised at 06:15 EDT on 6 October. It then passed the search engine's zero-step reload and the author's independent checker (10:20 to 10:31 UTC: V 8,388,608, E 16,777,212, F 8,388,606, Euler characteristic 2, all labels, all faces quadrilaterals, rotation symmetric, all crossings transversal; verdict "VERIFIED simple symmetric 23-Venn (both checks pass)"), the pinned native reimport above (10:18 to 10:19 UTC), `verify.py` (10:37 to 10:48 UTC, transcript above) and the monotone test (10:49 UTC), and its canonical form was computed at 11:12 UTC (Distinctness above). Its face export (`venn23-c6p-s1065101.json`) was written by the original engine during that zero-step reload; a second zero-step reload of the same raw state by the original engine, run separately under Codex's wrapper at 10:21 UTC with the input's sha256 checked before and after, wrote a byte-identical file. (Both exports therefore come from the original engine reading the same raw state; the two runs agree, but they are not two independent producers.)
- `f4` is the one certificate of the five found on a cloud virtual machine rather than on the author's laptop: a 4-vCPU `c2d-highcpu-4` instance in Google Cloud's `us-east4-b` zone, running the author's program as a hold at T 0.14 (seed 254004) from c6's E = 46 state, launched at about 21:23 EDT on 5 October; it reached E = 0 at engine time 34,272 s (06:54 EDT, 10:54 UTC, 6 October). The raw state was copied to the laptop with its sha256 checked on both machines, and it then passed the search engine's zero-step reload and the author's independent checker (11:26 to 11:35 UTC: V 8,388,608, E 16,777,212, F 8,388,606, Euler characteristic 2, all labels, all faces quadrilaterals, rotation symmetric, all crossings transversal; verdict "VERIFIED simple symmetric 23-Venn (both checks pass)"), `verify.py` (about 11:36 to 11:46 UTC, transcript above), the monotone test (11:48 UTC) and the pinned native reimport above (12:15 UTC), and its canonical form was computed at about 12:03 UTC and its region-degree histogram at 12:16 UTC (Distinctness above). Its state one move before completion had two missing orbits one bit apart and no duplicate (E = 46), so like `c25` and `c19` it closed by an insertion.
