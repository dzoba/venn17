# Checker transcript, 19-curve certificates (2026-09-21, seventh added 2026-09-22)

`python3 verify/verify.py certificates/<file>` on each of the seven 19-curve certificates (six from the closure runs of 20-21 September 2026, one from a fresh-start run that completed on 22 September 2026), followed by `verify/monotone_test.py`.

## certificates/venn19-closure-s195001.json
```
  V                                524288
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 1048572}
  euler                            2
  face_sizes                       {4: 524286}
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
elapsed     36.4 s
RESULT: PASS

```
monotone test:
```
certificates/venn19-closure-s195001.json: n=19 labels=524288 complete=True non_monotone_labels=68362 e.g. ['0000000000000010101', '0000000000000011111', '0000000000000100111']
```

## certificates/venn19-closure-s195002.json
```
  V                                524288
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 1048572}
  euler                            2
  face_sizes                       {4: 524286}
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
elapsed     36.8 s
RESULT: PASS

```
monotone test:
```
certificates/venn19-closure-s195002.json: n=19 labels=524288 complete=True non_monotone_labels=68058 e.g. ['0000000000000010101', '0000000000000011111', '0000000000000101010']
```

## certificates/venn19-closure-s196001.json
```
  V                                524288
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 1048572}
  euler                            2
  face_sizes                       {4: 524286}
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
elapsed     35.2 s
RESULT: PASS

```
monotone test:
```
certificates/venn19-closure-s196001.json: n=19 labels=524288 complete=True non_monotone_labels=67678 e.g. ['0000000000000010101', '0000000000000011101', '0000000000000101010']
```

## certificates/venn19-closure-s196002.json
```
  V                                524288
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 1048572}
  euler                            2
  face_sizes                       {4: 524286}
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
elapsed     37.5 s
RESULT: PASS

```
monotone test:
```
certificates/venn19-closure-s196002.json: n=19 labels=524288 complete=True non_monotone_labels=68210 e.g. ['0000000000000010101', '0000000000000101010', '0000000000000110011']
```

## certificates/venn19-closure-s196004.json
```
  V                                524288
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 1048572}
  euler                            2
  face_sizes                       {4: 524286}
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
elapsed     36.7 s
RESULT: PASS

```
monotone test:
```
certificates/venn19-closure-s196004.json: n=19 labels=524288 complete=True non_monotone_labels=68134 e.g. ['0000000000000010101', '0000000000000101010', '0000000000000110011']
```

## certificates/venn19-closure-s196007.json
```
  V                                524288
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 1048572}
  euler                            2
  face_sizes                       {4: 524286}
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
elapsed     35.9 s
RESULT: PASS

```
monotone test:
```
certificates/venn19-closure-s196007.json: n=19 labels=524288 complete=True non_monotone_labels=67203 e.g. ['0000000000000010101', '0000000000000010111', '0000000000000011111']
```

## certificates/venn19-fresh-s192015.json
```
file        venn19-fresh-s192015.json
n           19
faces       524286 listed, 524286 distinct
report:
  E                                1048572
  F                                524286
  V                                524288
  all_crossings_transversal        True
  all_labels                       True
  bad_edges                        0
  curves_two_sides_connected       True
  edge_multiplicities              {2: 1048572}
  euler                            2
  face_sizes                       {4: 524286}
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
elapsed     35.5 s
RESULT: PASS
```
monotone test:
```
certificates/venn19-fresh-s192015.json: n=19 labels=524288 complete=True non_monotone_labels=71155 e.g. ['0000000000000010011', '0000000000000011101', '0000000000000011111']
```

## Checksums
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
```
