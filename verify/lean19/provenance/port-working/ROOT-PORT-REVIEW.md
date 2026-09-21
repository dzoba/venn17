# Source port review before Lean19 execution

September 21, 2026, 03:06 UTC. Full Lean19 verification is still pending.

The root independently compared the port against the source-identical17
baseline. All309 vendored Lean files are byte-identical. There are127 changed
project-owned Lean files. Excluding the two regenerated data modules, their
differences consist solely of numerals, namespace/name changes, input filename,
and comments. A normalization comparison found no additional proof or checker
logic changes. This is a source review, not a substitute for type checking.

The numerical substitutions in executable/proof text are:

| Old | New | Interpretation |
|---:|---:|---|
|16|18|last curve index / inverse rotation|
|17|19|dimension, namespace and theorem names|
|18|20|meridian point count|
|32|36|south pole triangulated link shift|
|33|37|last boundary edge index|
|34|38|meridian boundary / pole link size|
|7710|27594|quadrilaterals per sector|
|30840|110376|curve polygon vertices|
|131070|524286|crossings|
|131071|524287|all-one pattern|
|131072|524288|regions|
|262140|1048572|arrangement arcs|
|262142|1048574|triangulation vertices|
|524280|2097144|triangulation triangles|
|786420|3145716|triangulation edges|

Two test bitstrings also changed from17 to19 characters, preserving their
single-bit meaning. Context-specific small constants and generated face
indices were treated separately. The meridian and sector witnesses were
regenerated rather than numerically transformed.

The generator results establish candidate finite witnesses:20 meridian
vertices,19 rotations,19 edges per meridian;19 sectors, each with
V27614/E55207/F27594, Euler1 and38 boundary edges. A separate oriented pole
check found curve-link shifts[1,18], hence triangulated shifts[2,36]. Lean must
still check every witness through the unchanged relative certificate logic.

The selected JSON hash was independently checked against
`ed26b3baa6e5c02bc3a4239b1dfbf84d66f731cad2dd2805a8c1770e2c1fdb5d`.
All nine actual dependency Git revisions match the pinned Lake manifest; see
`dependency-revisions.json`. Original source bundle integrity passed465 entries.

Expected final theorem: `Venn19.Topology.supplied_simple_rotational_venn`.
Its structure must retain19 Jordan curves, connected sides and all membership
regions, no triple points, transverse crossing charts and rigid rotation by
2π/19. The final axiom audit must match the baseline's20 relative native-check
axioms plus `propext`, `Classical.choice` and `Quot.sound`, with no sorry or
additional mathematical axiom.

Lean19 launch remains gated on a successful baseline17 build and a feasibility
estimate posted to Claude. After baseline success, its unchanged vendor build
artifacts can be reused to avoid recompiling generic topology; any such reuse
must be recorded and content hashes rechecked by Lake. No19 build has run yet.
