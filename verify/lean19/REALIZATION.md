# The certified 19-curve realization

## Finite certificate

The input `venn19-closure-s196002.json` lists 524,286 quadrilateral crossings
in cyclic order using 19-bit region labels. The project checks that all 524,288
labels occur, the dual graph has 1,048,572 edges, every edge has the required
incidence, vertex links are cyclic, curve and side data are connected, crossing
labels are transverse squares, and the order-19 rotation preserves the data.

The certificate SHA-256 is
`ed26b3baa6e5c02bc3a4239b1dfbf84d66f731cad2dd2805a8c1770e2c1fdb5d`.
The text is embedded into the Lean development as a declared Lake input. The
finite predicates are checked in Lean; the Python scripts provide independent
audits and witness generation, not trusted theorem premises.

## Surface and curve construction

The checked quadrangulation is triangulated with one center per crossing face.
The resulting counts are:

| Quantity | Count |
|---|---:|
| Quadrilateral faces | 524,286 |
| Region vertices | 524,288 |
| Arrangement edges | 1,048,572 |
| Triangulation vertices | 1,048,574 |
| Triangulation edges | 3,145,716 |
| Triangulation triangles | 2,097,144 |

The surface proofs establish the closed connected triangulated surface, compute
Euler characteristic 2, and use the vendored classification development to
identify it with the sphere. Curve polygons, local crossing charts, sides, and
all membership regions are then realized on that sphere.

## Equivariant planar realization

A generated meridian certificate supplies a 20-vertex path between the two
rotation-fixed poles, with 19 rotated rows of 19 faces. The sector certificate
has 19 sectors; each sector has 27,614 vertices, 55,207 edges, 27,594
quadrilaterals, Euler characteristic 1, and 38 boundary edges. The oriented pole
check gives curve-link steps `[1, 18]` and triangulated steps `[2, 36]`.

Lean checks these finite witnesses and proves the sector disks and equivariant
gluing. Stereographic projection then gives a plane homeomorphism for which the
order-19 action is the rigid positive rotation through `2π/19` about zero.

The definitions

```lean
rotationalVennCurve : Fin 19 → Set Plane
rotationalVennSide  : Fin 19 → Bool → Set Plane
```

use a reversed index order so that the file's decreasing label action becomes
the successor convention `i ↦ i + 1`. The theorem
`supplied_simple_rotational_venn` proves embedded Jordan curves, connected and
correctly bounded sides, every connected membership region, absence of triple
points, transverse crossing charts, and the rigid rotation law. The existential
wrapper packages those concrete curves and sides as a 19-curve example.

## Computational boundary

Twenty input-specific conclusions use `native_decide`, trusting Lean's compiler
and runtime for the large finite computations. The final theorem also uses
`propext`, `Classical.choice`, and `Quot.sound`. The topology and geometry built
from the certified data are ordinary kernel-checked proofs. The complete axiom
output is `topology-axioms.txt` and its baseline comparison is recorded in
`verification/lean19/postbuild/summary.json`.
