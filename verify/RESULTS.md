# Verification results

Produced by running, from the repository root:

    python3 verify/verify.py certificates/best11-s0.json certificates/v3-13-s0.json \
        certificates/venn17-gcp-s12.json certificates/venn17-gcp-s14.json \
        certificates/venn17-gcp-s16.json certificates/venn17-local-c3-s2.json

    python3 verify/monotone_test.py certificates/best11-s0.json certificates/v3-13-s0.json \
        certificates/venn17-gcp-s12.json certificates/venn17-gcp-s14.json \
        certificates/venn17-gcp-s16.json certificates/venn17-local-c3-s2.json

Environment: Python 3.14.3, macOS (darwin 25.6.0), 2026-09-17.

## Summary

| certificate | n | faces | V | E | euler | all_labels | verify.py | non-monotone labels |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| best11-s0.json | 11 | 2046 | 2048 | 4092 | 2 | True | PASS | 319 |
| v3-13-s0.json | 13 | 8190 | 8192 | 16380 | 2 | True | PASS | 1222 |
| venn17-gcp-s12.json | 17 | 131070 | 131072 | 262140 | 2 | True | PASS | 16592 |
| venn17-gcp-s14.json | 17 | 131070 | 131072 | 262140 | 2 | True | PASS | 15249 |
| venn17-gcp-s16.json | 17 | 131070 | 131072 | 262140 | 2 | True | PASS | 15708 |
| venn17-local-c3-s2.json | 17 | 131070 | 131072 | 262140 | 2 | True | PASS | 15742 |

All six certificates satisfy every criterion verify.py checks: all_labels, euler == 2,
every edge multiplicity == 2, vertices_single_rotation_cycle, curves_two_sides_connected,
rotation_symmetric, non_transversal_faces == 0, repeated_vertex_faces == 0.

All six have a non-zero count of labels that violate the Bultena-Grunbaum-Ruskey
monotonicity condition, so none of these diagrams is monotone (0 would mean monotone).

Independent Lean 4 proof, 2026-09-18: `venn17-local-c3-s2.json` was rebuilt from scratch in
`verify/lean/` (Justin Grimes's formalization, Apache-2.0) on Lean 4.32.1 with Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`. `lake build` completed all 3468 jobs in 9 min 6 s
(peak RSS 3.4 GB, after a 2 min 25 s `lake exe cache get`), which is where Lean's kernel checks
`Venn17.Topology.supplied_simple_rotational_venn`: the certificate is realized in the plane by 17
embedded circles whose 2^17 side-intersections are all nonempty and path-connected, with no triple
points, transverse double points, and a rigid rotation through 2π/17 permuting the curves.
`lake exe venn_check venn17-local-c3-s2.json` printed all fifteen finite checks true and
`PASS: all finite combinatorial checks.` in 8.9 s;
`lake env lean scripts/audit_topology.lean` reproduced the shipped `topology-axioms.txt` byte for
byte (no `sorry`; `propext`, `Classical.choice`, `Quot.sound` and 20 `native_decide` axioms);
`scripts/audit_vendor.py` confirmed 309 unchanged vendored sources. Commands and full timings are
in the README's "Formal verification (Lean)" section.

## verify.py transcript

```
file        certificates/best11-s0.json
n           11
faces       2046 listed, 2046 distinct
report:
  E                                4092
  F                                2046
  V                                2048
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 4092}
  euler                            2
  face_sizes                       {4: 2046}
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
elapsed     0.1 s
RESULT: PASS

file        certificates/v3-13-s0.json
n           13
faces       8190 listed, 8190 distinct
report:
  E                                16380
  F                                8190
  V                                8192
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 16380}
  euler                            2
  face_sizes                       {4: 8190}
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
elapsed     0.9 s
RESULT: PASS

file        certificates/venn17-gcp-s12.json
n           17
faces       131070 listed, 131070 distinct
report:
  E                                262140
  F                                131070
  V                                131072
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 262140}
  euler                            2
  face_sizes                       {4: 131070}
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
elapsed     10.1 s
RESULT: PASS

file        certificates/venn17-gcp-s14.json
n           17
faces       131070 listed, 131070 distinct
report:
  E                                262140
  F                                131070
  V                                131072
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 262140}
  euler                            2
  face_sizes                       {4: 131070}
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
elapsed     10.9 s
RESULT: PASS

file        certificates/venn17-gcp-s16.json
n           17
faces       131070 listed, 131070 distinct
report:
  E                                262140
  F                                131070
  V                                131072
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 262140}
  euler                            2
  face_sizes                       {4: 131070}
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
elapsed     10.8 s
RESULT: PASS

file        certificates/venn17-local-c3-s2.json
n           17
faces       131070 listed, 131070 distinct
report:
  E                                262140
  F                                131070
  V                                131072
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 262140}
  euler                            2
  face_sizes                       {4: 131070}
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
elapsed     11.2 s
RESULT: PASS

```

## monotone_test.py transcript

```
certificates/best11-s0.json: n=11 labels=2048 complete=True non_monotone_labels=319 e.g. ['00000000101', '00000001001', '00000001010']
certificates/v3-13-s0.json: n=13 labels=8192 complete=True non_monotone_labels=1222 e.g. ['0000000001001', '0000000001011', '0000000001101']
certificates/venn17-gcp-s12.json: n=17 labels=131072 complete=True non_monotone_labels=16592 e.g. ['00000000000010011', '00000000000011011', '00000000000100110']
certificates/venn17-gcp-s14.json: n=17 labels=131072 complete=True non_monotone_labels=15249 e.g. ['00000000001000101', '00000000001011001', '00000000001101011']
certificates/venn17-gcp-s16.json: n=17 labels=131072 complete=True non_monotone_labels=15708 e.g. ['00000000000011011', '00000000000011111', '00000000000110110']
certificates/venn17-local-c3-s2.json: n=17 labels=131072 complete=True non_monotone_labels=15742 e.g. ['00000000000010101', '00000000000010111', '00000000000011011']
```
