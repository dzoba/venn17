# 19-curve certificates for formal verification

Three certificates of simple rotationally symmetric 19-Venn diagrams, in exactly the format of
`venn17-local-c3-s2.json` from the 17-curve Lean proof: `{"n": 19, "faces": [[l0, l1, l2, l3], ...]}`, each label a
19-character LSB-first bit string (character i = membership in curve i), each face one crossing given by its four
regions in cyclic order. 524,286 faces, 524,288 distinct labels, 1,048,572 edges.

The 17-curve development (`Venn17.*`) fixes n = 17 in its namespace, its `Array.range 17` loops and the `i < 17`
hypotheses of `each_curve_connected`, `each_curve_degree_two`, `each_side_connected`; a 19-curve version needs those
constants parametrized (or duplicated as `Venn19`) and `native_decide` re-run on a certificate about four times larger
(47 MB of JSON versus 10.7 MB). Nothing else about the statement changes: 19 Jordan curves in the plane, carried to
one another by a rigid rotation through 2*pi/19, every one of the 2^19 regions path-connected, no point on three
curves, every crossing transversal.

Checks already passed by each certificate (see ../README.md): the original search engine's structural reload, the
independent Python checker (`gks_scaffold.check` on `interval_growth.oriented_faces`), and the public repository's
`verify/verify.py`.

| file | sha256 |
|---|---|
| venn19-closure-s195001.json | 11142a0d03800cde4680e6635c0ec986a8f08b698be1bacfe849a6ce951d26bb |
| venn19-closure-s196002.json | ed26b3baa6e5c02bc3a4239b1dfbf84d66f731cad2dd2805a8c1770e2c1fdb5d |
| venn19-closure-s196004.json | ca84c06e669461dfc4d5e070d37518dfd687e7cf7348893e60802867133e6653 |
