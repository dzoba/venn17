# Geometric formalization: complete rigid planar Venn proof

Import `VennTopology` for the combined results. Lean now constructs
`diagramSphereHomeomorph : Diagram ≃ₜ SphereRepresentative` and
`diagramPlaneHomeomorph : PuncturedDiagram ≃ₜ Plane` without additional geometric
hypotheses. The sphere identification follows from the certified normalization
trace and a proved Euler-count invariant for every move. Stereographic
projection removes the all-zero point.

`Venn17.Topology.planar_venn_diagram_verified` proves that the resulting 17
planar curves are embedded circles, their bit-1 sides are bounded and bit-0
sides are unbounded, and all 131,072 membership regions are nonempty and path
connected. `planar_no_triple_intersections`, `planar_crossing_iff`, and
`planar_transverse_crossing` transport simplicity and the exact crossing charts
to these actual plane curves.

`Venn17.Topology.supplied_simple_rotational_venn` now proves the full simple,
rigidly rotational Venn definition for the constructed plane curves, with no
remaining geometric hypotheses. Its rotation is a linear Euclidean isometry
through exactly `2π/17` about zero. The theorem includes every nonempty
path-connected membership region, the bounded inside/unbounded outside
interpretation, no triple intersections, and transverse crossing charts.

`rigidPlane_membership_verified` retains the original file's pattern labels
and their unique regions. `rigidPlane_crossing_iff` retains the exact crossing
list. The file's generator decreases curve labels; `vennIndexOrder` reverses
the cyclic order so the final family's positive rotation sends `i` to `i+1`.
`planeSymmetryConjugacy_rotation` also explicitly conjugates the earlier
`realizedPlaneSymmetry` to this rigid rotation.

The completed conjugacy construction uses the following proved inputs. Removing the
unique fixed point gives a free cyclic action whose orbit projection is a
17-sheeted covering (`rotationOrbitProjection_isCoveringMap` and
`rotationOrbitProjection_fiber_card`). The disk neighborhoods at the original
diagram's two poles have actual local rigid-rotation conjugacies
(`diagram_pole_disk_conjugacy`), with angles `+2π/17` and `-2π/17` in their
certified link parametrizations. There is now also an explicit system of 17
embedded pole-to-pole arcs (`diagram_meridian_system`). Distinct arcs meet
exactly at the poles; any two form an embedded circle, and the actual symmetry
advances the arcs while preserving their interval parameters. The corresponding
17 closed sectors now cover the sphere, intersect only on their specified
boundaries, and are proved homeomorphic to closed Euclidean disks. Their disk
charts preserve the given boundary parameters. Transporting the chart of
sector zero gives `equivariantSectorDisk_rotation`, including the last-to-first
case. The standard Euclidean sphere now has its own proved rigid-rotation
sector cover and equivariant disk charts. `sectorConjugacy` constructs the
homeomorphisms between corresponding sectors and proves the rotation equation
on each. `sector_boundary_compatibility` proves the exact equality of source
and target boundary identifications. Closed-cover gluing gives the global
`rigidSphereConjugacy`. `northStereographicComplex_rotation` proves equivariance
of the specified projection, and `rigidPlaneHomeomorph_rotation` gives the
unconditional rigid plane conjugacy.

The earlier surface, punctured-surface, and conditional planar certificates
remain available. Their hypotheses are now instantiated by the constructed
sphere and plane homeomorphisms.

## Completed in Lean

For the oriented quadrilateral array, assign a distinct unit coordinate vector
to every region label and another to every quadrilateral center. Subdivide each
quadrilateral into the four triangles spanned by its center and consecutive
corners. `diagramQuad.space` is the union of these closed triangles, and
`Diagram` is that set with the subspace topology.

The ambient real coordinate space is `(Nat ⊕ Fin numberOfFaces) → ℝ` with its
product topology. The construction uses only finitely many coordinates, but
this is not a drawing in the plane. Distinct labels give distinct basis vectors.

| Result | Lean declaration | Source |
| --- | --- | --- |
| Compact and Hausdorff | `diagram_compact`, `diagram_hausdorff` | `VennTopology/Dataset.lean` |
| Path connected | `diagram_pathConnected` | `VennTopology/Dataset.lean` |
| Triangles intersect exactly in the convex hull of their shared vertices | `Quad.triangle_inter` | `VennTopology/Intersections.lean` |
| Finite Mathlib geometric simplicial complex with this underlying space | `Quad.complex_faces_finite`, `Quad.complex_space` | `VennTopology/Intersections.lean` |
| Exactly 262,142 vertices, 786,420 edges, and 524,280 triangles in that complex, with no higher-dimensional faces | `diagram_triangulation_counts_verified` | `VennTopology/EulerCharacteristic.lean` |
| Simplicial Euler characteristic of the realized complex is 2 | `diagram_euler_characteristic` | `VennTopology/EulerCharacteristic.lean` |
| Finite barycentric triangulation homeomorphic to the same diagram, with the same exact simplex counts | `diagramFiniteTriangulation`, `diagram_finite_euler_characteristic` | `VennTopology/FiniteTriangulation.lean` |
| Vertex stars and the whole triangle family are connected through shared edges; each edge has exactly two incident triangles | `diagram_classification_input_verified` | `VennTopology/TriangulationIncidence.lean` |
| Polygon quotient with 786,420 twice-paired edges and 524,280 faces, homeomorphic to the same diagram | `diagramPolygonalHomeomorph`, `diagram_presentation_edge_multiplicity` | `VennTopology/PolygonalModel.lean` |
| Certified normalization to a canonical polygon quotient, preserving absence of boundary | `diagramNormalization`, `diagramCanonicalHomeomorph`, `diagram_normal_form_closed` | `VennTopology/ClassifiedSurface.lean` |
| Sphere or closed positive-genus orientable/nonorientable surface alternatives | `diagram_closed_classification` | `VennTopology/ClassifiedSurface.lean` |
| Polygon vertex classes map onto all 262,142 geometric vertices, giving polygon Euler count at least 2 | `diagram_polygon_euler_lower_bound` | `VennTopology/PolygonEulerLowerBound.lean` |
| Euler count is preserved by signed relabeling and cyclic face rotations | `eulerCharacteristic_signedIso` | `VennTopology/PolygonVertices.lean` |
| Closed canonical Euler counts are 2 for the sphere, `2 - 2p` for positive orientable genus, and `2 - p` for positive nonorientable genus | `sphere_euler_characteristic`, `orientable_euler_characteristic`, `nonOrientable_euler_characteristic` | `VennTopology/CanonicalEuler.lean` |
| Admissible closed canonical form with Euler count at least 2 must be the sphere | `normalForm_eq_sphere_of_euler_ge_two` | `VennTopology/EulerSphereCriterion.lean` |
| Face reversal preserves endpoint vertex classes and Euler count | `unorientedIsoVertexEquiv`, `eulerCharacteristic_unorientedIso` | `VennTopology/UnorientedEuler.lean` |
| Edge subdivision adds exactly one distinct vertex and one edge | `expandVertexEquiv`, `eulerCharacteristic_expand` | `VennTopology/P1Euler.lean` |
| Face splitting preserves vertices and adds one edge and one face, including valid one-sided cuts | `splitVertexEquiv`, `eulerCharacteristic_split` | `VennTopology/P2Euler.lean` |
| Every validity-safe normalization trace preserves Euler count | `eulerCharacteristic_normalForm` | `VennTopology/NormalizationEuler.lean` |
| The normalized diagram is the sphere; actual global sphere homeomorphism and exact polygon Euler count 2 | `diagram_normal_form_eq_sphere`, `diagramSphereHomeomorph`, `diagram_polygon_euler_characteristic` | `VennTopology/SphereReduction.lean` |
| Actual Euclidean plane realization with all membership regions | `diagramPlaneHomeomorph`, `planar_venn_diagram_verified` | `VennTopology/PlaneRealization.lean` |
| Simple plane crossings and exact-order cyclic plane homeomorphism | `planar_transverse_crossing`, `realizedPlaneSymmetry`, `planar_symmetry_no_short_period` | `VennTopology/PlaneArrangement.lean` |
| Free cyclic action away from the plane fixed point; orbit projection is a covering with 17 points per fiber | `rotationOrbitProjection_isCoveringMap`, `rotationOrbitProjection_fiber_card` | `VennTopology/RotationOrbits.lean` |
| Cyclic polygon shifts correspond to exactly specified rigid circle angles | `labeledPolygonHomeomorph_rotation` | `VennTopology/PolygonRotation.lean` |
| The pole links rotate by `+2π/17` and `-2π/17` | `zero_pole_link_rotation`, `one_pole_link_rotation` | `VennTopology/PoleRotation.lean` |
| The actual diagram symmetry is conjugate to rigid rotations on embedded disk neighborhoods of both poles | `diagram_pole_disk_conjugacy`, `pole_disk_range_mem_nhds` | `VennTopology/PoleDiskRotation.lean` |
| Explicit 17-edge meridians are embedded closed intervals joining the actual poles | `diagramMeridianHomeomorph`, `diagramMeridianMap_zero`, `diagramMeridianMap_one` | `VennTopology/MeridianArcs.lean` |
| Distinct meridians meet exactly at the poles; any pair forms a Jordan boundary; symmetry advances their parametrizations | `diagram_meridians_inter`, `diagram_meridian_system` | `VennTopology/MeridianIntersections.lean` |
| Compact path-connected sectors cover the sphere and rotate cyclically | `diagram_sectors_cover`, `diagramSector_pathConnected`, `diagram_sector_rotation` | `VennTopology/SectorGeometry.lean`, `SectorConnected.lean` |
| Distinct sectors intersect only on the assigned meridian boundaries | `sector_inter_subset_boundary` | `VennTopology/SectorIntersections.lean` |
| Each closed sector is a Euclidean closed disk with the prescribed boundary parametrization | `sectorDiskHomeomorph`, `sectorDiskHomeomorph_boundary` | `VennTopology/SectorDisk.lean` |
| Disk charts transported from sector zero respect the actual symmetry, including cyclic wraparound | `equivariantSectorDisk_boundary`, `equivariantSectorDisk_rotation` | `VennTopology/EquivariantSectorDisk.lean` |
| The target rotation is an actual Euclidean isometry with angle `2π/17` | `axialRotation`, `rigidGenerator`, `rigidSphereRotation_period` | `VennTopology/RigidSphere.lean` |
| Standard spherical sectors have prescribed-boundary disk charts respecting the rigid rotation | `sphereLuneDisk_boundary`, `equivariantRigidSectorDisk_boundary`, `equivariantRigidSectorDisk_rotation` | `VennTopology/SphereLunes.lean`, `RigidSectorDisk.lean` |
| Standard sectors cover the sphere and distinct sectors meet only on their meridian boundaries | `rigid_sectors_cover`, `rigid_sector_inter_subset_boundary` | `VennTopology/RigidSectorCover.lean`, `RigidSectorIntersections.lean` |
| Constructed source-to-target sector homeomorphisms satisfy the boundary and rotation equations | `sectorConjugacy_boundary`, `sectorwise_rigid_conjugacy` | `VennTopology/SectorConjugacy.lean` |
| Boundary identifications agree, and the sector maps glue to an unconditional global rigid sphere conjugacy | `sector_boundary_compatibility`, `rigidSphereConjugacy_rotation` | `VennTopology/RigidSphereConjugacy.lean` |
| The specified stereographic projection and full plane realization commute with rigid rotation | `northStereographicComplex_rotation`, `rigidPlaneHomeomorph_rotation` | `VennTopology/EquivariantStereographic.lean`, `RigidPlaneConjugacy.lean` |
| The full simple rotational Venn definition, with successor action on indices and no geometric hypotheses | `supplied_simple_rotational_venn`, `exists_simple_rotational_venn_17` | `VennTopology/RotationalVenn.lean` |
| Every triangle has three distinct, affinely independent vertices | `diagram_triangles_nondegenerate`, `Quad.point_affineIndependent` | `VennTopology/Certificate.lean`, `Intersections.lean` |
| A homeomorphism induced by the label action | `diagramRotation` | `VennTopology/DiagramSymmetry.lean` |
| Seventeenth power is identity | `diagram_rotation_period` | `VennTopology/DiagramSymmetry.lean` |
| Every smaller positive power moves the pattern-1 point | `diagram_rotation_no_short_period` | `VennTopology/DiagramSymmetry.lean` |
| Action on every region vertex follows the input bit shift | `diagram_rotation_pattern` | `VennTopology/DiagramSymmetry.lean` |
| The only fixed points are the all-zero and all-one vertices | `diagram_rotation_fixed_iff` | `VennTopology/FixedPoints.lean` |
| Every triangle dart occurs exactly in its certified cyclic vertex link | `every_link_has_cyclic_order`, `every_triangle_dart_occurs` | `VennTopology/LinkCertificate.lean` |
| Each geometric vertex link is homeomorphic to a circle | `diagram_geometric_link_circle` | `VennTopology/GeometricLinks.lean` |
| Punctured vertex stars are annuli | `diagram_punctured_star_annulus` | `VennTopology/GeometricLinks.lean` |
| Every point has an open disk neighborhood, including the disk center | `diagram_locally_open_disk` | `VennTopology/Surface.lean` |
| Second countability and genuine surface atlas | `diagram_second_countable`, `diagramChartedSpace` | `VennTopology/Surface.lean` |
| General planar Jordan separation theorem | `planar_jordan_separation` | `VennTopology/Planar.lean`, `Vendor/JordanCurve/` |
| Each of the 17 actual labelled curves is an embedded circle on the surface | `diagram_curves_are_embedded_circles`, `diagramCurveHomeomorph` | `VennTopology/DiagramCurves.lean` |
| Complementary regions are path connected and contain their pattern vertices | `diagramRegion_pathConnected`, `patternPoint_mem_region` | `VennTopology/Regions.lean` |
| Every complement point belongs to exactly one pattern region | `diagram_complement_unique_region` | `VennTopology/Regions.lean` |
| Exactly 131,072 connected components of the geometric complement | `diagramComponentsEquiv`, `diagram_complement_component_count` | `VennTopology/Regions.lean` |
| No triple intersections | `diagram_no_triple_intersections` | `VennTopology/CurveIntersections.lean` |
| Intersections are exactly the listed centers, each on exactly two curves | `diagram_crossing_iff`, `diagram_crossing_exactly_two` | `VennTopology/CurveIntersections.lean` |
| Every crossing has a plane chart taking its two curves exactly to the axes | `diagram_transverse_crossing` | `VennTopology/CrossingCharts.lean` |
| Crossing charts remain valid after deleting the all-zero point | `punctured_transverse_crossing` | `VennTopology/PuncturedCrossings.lean` |
| Continuous signed bit fields with exactly the curves as their zero sets | `diagram_bit_field_verified` | `VennTopology/CurveLevelSet.lean` |
| Both geometric sides of each individual curve are path connected | `diagramSide_pathConnected` | `VennTopology/CurveSides.lean` |
| Exactly two connected components of each individual curve's complement | `diagramSideComponentsEquiv`, `diagram_curve_complement_component_count` | `VennTopology/SideComponents.lean` |
| Every region point has its pattern's geometric side choices | `diagram_region_side_iff` | `VennTopology/SideComponents.lean` |
| Regions equal the intersections of their 17 selected sides | `diagramRegion_eq_sides` | `VennTopology/SideComponents.lean` |
| Symmetry shifts actual curves by `i-1` modulo 17 | `diagram_rotation_curve_image` | `VennTopology/CurveSymmetry.lean` |
| Symmetry maps whole pattern regions to their bit-shifted regions | `diagram_rotation_region_image` | `VennTopology/RegionSymmetry.lean` |
| Each region remains path connected after removing its marked point | `diagramRegion_punctured_pathConnected` | `VennTopology/PuncturedRegions.lean` |
| Exactly 131,072 complementary components after deleting the all-zero point | `punctured_complement_component_count` | `VennTopology/PuncturedArrangement.lean` |
| Punctured arrangement retains embedded curves, exact-order symmetry, and just the all-one fixed point | `punctured_arrangement_verified` | `VennTopology/PuncturedCertificate.lean` |
| Each individual curve still has two path-connected sides after removing the pole | `puncturedSide_pathConnected`, `punctured_curve_complement_component_count` | `VennTopology/PuncturedSides.lean` |
| Punctured regions equal their bit-selected side intersections | `puncturedRegion_eq_sides` | `VennTopology/PuncturedSides.lean` |
| Any plane homeomorphism sends bit-1 sides to bounded sets and bit-0 sides to unbounded sets | `planeSide_true_bounded`, `planeSide_false_unbounded` | `VennTopology/PlanarSides.lean` |
| Every planar membership choice is nonempty and path connected, conditional on that homeomorphism | `plane_every_membership_pattern`, `planar_sides_verified` | `VennTopology/PlanarSides.lean` |

The connectivity proof turns certified graph walks into continuous paths in
triangles. The simplex-intersection theorem follows from affine independence
of the coordinate vectors. It excludes accidental geometric overlaps.

The Euler proof now counts the actual faces of `diagramQuad.complex`, not just
the checker report. `GeometricFace q k` consists of its faces with exactly
`k` vertices. Injective vertex relabelling and coordinate-vector maps give
bijections between these geometric faces and finite subsets of the encoded
triangles. The link certificates prove that the map from each oriented
triangle dart to its ordered endpoint pair is injective, and that every edge
also occurs in the reverse direction. Thus the `12F` darts count precisely
twice the undirected geometric edges. Each quadrilateral contributes four
distinct triangles, and the vertices are exactly the `n` pattern vertices and
`F` centers. The resulting counts are `n+F`, `6F`, and `4F`; all higher-dimensional
faces are excluded. For this file, `262142 - 786420 + 524280 = 2`.
`geometricEulerCharacteristic` is this alternating simplex count. No invariance
or surface-classification theorem is silently inferred from the arithmetic.

The adapter to the external `GeometricTriangulation` representation restricts
the encoded natural-number coordinates to `Fin (n+F)` and extends back by zero.
Both directions are continuous and preserve the coordinate simplex sets.
All lower-dimensional faces are preserved by explicit bijections, so the
external library's own edge and triangle sets have the proved counts above.
Its realization is the concrete union of supported standard-simplex faces;
no arbitrary realization field or assumed homeomorphism is used.

The incidence proofs establish that an edge has precisely two incident
triangles: its two directed darts determine the triangles, and their reversed
orientations force those triangles to be different. The connected geometric
circle links also yield chains of triangles sharing edges at each fixed
vertex. A finite closed-cover argument supplies those chains. Combined with
connectedness of the surface, this proves global dual connectivity and hence
the library's full `SurfaceIncidence` predicate.

The next bridge is now geometric as well: `diagramPresentation` stores the
triangular boundary words, and `diagramPolygonalHomeomorph` identifies their
side-glued polygon quotient with `Diagram`. Boundary occurrences of an edge
are in bijection with its incident triangles. Consequently every presentation
edge has multiplicity two.

`PresentationClosedness.normalizationEquivalent_iff` proves that this property
survives signed relabelings, independent reversal of face traversal, edge
subdivision, face splitting (including the permitted degenerate splits), common
subdivisions, and the full equivalence closure used in normalization. In a
canonical normal form, each boundary component contributes an edge of
multiplicity one. Thus the normalized diagram has zero boundary components.
The resulting `diagram_closed_classification` gives actual homeomorphisms to
the sphere or closed positive-genus representatives. The retained
`diagramNormalization.equivalent` trace now supplies the proved Euler-invariance
argument. The earlier `diagram_classification_and_euler_verified` remains an
intermediate conjunction; `diagram_normal_form_eq_sphere` selects the sphere.

`PolygonVertices.Vertex P` is the finite quotient of oriented edge endpoints
by the corner identifications imposed by successive sides of every face. The
last-to-first corner is included, even for a monogon. Its cardinality defines
the vertex term of `PolygonVertices.eulerCharacteristic`; no genus formula is
built into this definition. Signed relabeling and cyclic rotation give an
explicit equivalence of these quotients and preserve the count.

For the input, mapping an endpoint to its geometric edge endpoint respects all
corner identifications and reaches every active vertex of the triangulation.
Surjectivity gives at least 262,142 polygon vertex classes, hence polygon Euler
count at least 2. Injectivity is not needed for the sphere argument. At the
canonical end, direct corner identifications collapse all endpoints to one
vertex. Counting the stored edges and faces proves `2`, `2 - 2p`, and `2 - p`
for the sphere, positive-genus orientable, and positive-genus nonorientable
closed forms respectively. Consequently only the sphere can have count at
least 2. This bound is now transported through normalization.

The move proofs use the actual endpoint quotients. Independent face reversal
reverses each corner relation and induces a quotient equivalence. Boundary-walk
lemmas in `PolygonWordWalk.lean` allow arbitrary cyclic starting positions and
both traversal directions. For P1, `expandVertexEquiv` identifies the expanded
vertex set with `Vertex P ⊕ Unit`; the midpoint is distinct from every old
vertex. For P2, `splitVertexEquiv` identifies the old and new vertex sets,
including a split with one empty piece. Source validity ensures the original
boundary is nonempty and excludes the empty-word-sphere exception.

Euler invariance then follows through directed subdivisions, common
subdivisions, face reversals, and the full normalization equivalence closure.
The resulting unconditional sphere homeomorphism also proves that the input's
polygon quotient has exactly 262,142 vertex classes. Stereographic projection
at the image of the all-zero point constructs `diagramPlaneHomeomorph`, which
instantiates all previously conditional planar side conclusions. These proofs
introduce no additional native checks or mathematical axioms.

The symmetry is an actual coordinate homeomorphism restricted to the realized
space. Face witnesses include cyclic corner shifts and a checked 17-step
period. The fixed-point proof applies to every point of the space, including
edge and triangle interiors: a triangle and its image can share only one of
the two distinguished vertices. This extra finite fact is checked against the
file and used through a proved geometric soundness theorem.

The new link certificate explicitly enumerates every incident triangle dart,
checks cyclic adjacency and distinct neighbors, and checks that no dart is
omitted. There are 262,142 active vertices and 1,572,840 triangle darts. The
soundness proof identifies the certified segment cycles with the links in the
original coordinate realization, including the change of coordinate labels.

The circle proof uses two continuous maps from finitely many closed intervals:
one traverses the coordinate polygon, the other traverses an additive circle.
Their fibers agree exactly. The disk proof similarly compares two continuous
maps from `Circle × [0,1]`, collapsing the entire circle only at the cone point.
Compact quotient maps prove continuity there. Restricting to the open disk
gives charts for the full open vertex stars, which cover every point of the
realization, including points inside edges and triangles. These are assembled
into Mathlib's `ChartedSpace ℂ Diagram`; the model is a real two-dimensional
plane, not a half-plane.

The labelled curve construction is separate from the vertex-link construction.
A polygon alternates crossing centers with arc midpoints. Its checker validates
30,840 vertices per curve, the bit label and containing triangle of every arm,
disjoint coordinate supports for distinct polygon vertices, and coverage of
every arm carrying that label. Disjoint supports make the linear map from an
abstract coordinate polygon injective even though arc midpoints are averages
of two region coordinates. The circle theorem is then transported to the
original `Diagram`, with its range proved equal to all of the specified arms.

Within each triangle the center-to-midpoint arm is exactly the locus where
the two region coordinates are equal. Away from the curves, one region
coordinate is strictly largest. This gives disjoint open pattern regions,
each star-convex in the encoded realization and therefore path connected.
They are clopen relative to the complement. Mathlib's connected-component
partition theorem supplies the actual equivalence to `Fin 131072`; this is
not just a count of graph vertices.

A noncentral point on an arm has two positive region coordinates. Those
coordinates determine the arc's bit label, so distinct labels cannot meet
there. At a center the checked alternating labels admit exactly two curves.

The transverse-crossing proof now supplies an explicit chart. In the open star
of a crossing center, write the four cyclic corner weights as `a₀,a₁,a₂,a₃`.
They are nonnegative, opposite weights cannot both be nonzero, and their sum is
less than 1. Map these weights to
`(a₀-a₁-a₂+a₃, a₀+a₁-a₂-a₃)`. The inverse uses the positive parts of
`(x+y)/2`, `(y-x)/2`, `-(x+y)/2`, and `(x-y)/2`. Both maps are proved
continuous and mutually inverse, including at the center and along triangle
edges. The target is the open square `|x|<1, |y|<1`.

The center goes to the origin. The two even-indexed arms map exactly to the
vertical axis and the two odd-indexed arms to the horizontal axis. The checked
alternating labels connect these statements to the actual curves. Positivity
of the center coordinate excludes arms from any other face in this neighborhood.
`CrossingSquare.HasCrossingChart` records this precise topological meaning of
transversality; it does not assert differentiability. The crossing stars exclude
the all-zero vertex, so the same charts work on the punctured surface.

For each bit, a continuous linear functional on the ambient coordinate space
assigns value −1 or +1 to each pattern vertex and the average of its four
corner values to each crossing center. Symbolic consequences of the checked
alternating edge labels prove that its zero set is exactly the labelled
circle, including centers lying on that circle when the containing triangle's
edge carries another label. No new native check is needed for these sign rules.

Intersecting a triangle with a strict signed halfspace is convex. Every point
in a signed side can be joined within such a set to a region vertex with the
same bit. The existing finite side-connectivity certificate then supplies
graph walks, which lift to continuous paths on that geometric side. The two
sides form a clopen partition of the individual curve's complement, yielding
an equivalence of its connected components with `Bool`. The intermediate value
theorem shows that every region retains its marked vertex's signs. Equality
of all 17 bits then proves `diagramRegion_eq_sides`.

The general theorem `preconnected_diff_singleton_of_neighborhood` proves that
removing a point from a preconnected set preserves preconnectedness when an
open neighborhood has preconnected puncture. Apply it to the bit-0 side,
using the all-zero region as the neighborhood. The surface atlas makes the
surface locally path connected, so the open punctured side is path connected.
The bit-1 side avoids the pole and is unchanged. The two sides again form a
clopen partition of each curve's complement, with components indexed by `Bool`.

For planar boundedness, the closed set where the bit field is nonnegative is
compact and excludes the all-zero pole, where the field has value −1. Its lift
to the punctured surface is compact, and its image under any plane
homeomorphism is compact, hence bounded. This contains the bit-1 side. The
curve is compact too; if the bit-0 side were bounded, their union would make
the entire plane bounded, a contradiction. All bit choices are realized:
the map from `Fin 131072` to `Fin 17 → Bool` is injective by bit extensionality
and surjective by equality of finite cardinalities. The existing region
connectivity theorems therefore establish the full membership-region
condition after any plane homeomorphism. No new native check is used.

The symmetry proof transports the individual center-to-midpoint segments under
the coordinate homeomorphism. The bit identity specifying the shifted label is
checked for every pattern and bit; the generic segment-image argument is proved
in Lean. Region symmetry follows by transporting the uniquely largest region
coordinate. These results apply to the entire geometric sets, not only the
marked vertices.

For puncturing a region, radial projection sends a noncentral point to its
geometric vertex link. Mixing any link point with weight `3/4` at the region
vertex gives a small circle strictly inside the region. Each point in the
punctured region can be joined to that circle inside one simplex while keeping
its dominant region coordinate below 1. This avoids the removed vertex. The
link is path connected, so the entire punctured region is path connected.
Restricting the curve embeddings and the symmetry to the punctured surface then
preserves their exact ranges, intersections, and period. The clopen region
partition again gives an equivalence of connected components with `Fin 131072`.

Generic topological proofs use only the ordinary Lean/Mathlib logical axioms.
Large input-specific incidence, link, curve, and symmetry checks use `native_decide`,
as do the earlier finite certificates. `#print axioms realized_surface_verified`
and `#print axioms realized_arrangement_verified`, together with
`#print axioms punctured_arrangement_verified`, show the exact dependencies,
also recorded in `topology-axioms.txt`.
The curve-symmetry theorem additionally uses `bit_rotation_verified`, a native
decision of the finite bit-flip/rotation identity.
The geometric side-connectivity theorem uses the pre-existing
`graph_certificates_pass` dependency through `each_side_connected`; the bit-field
and side proofs introduce no new native computations or axioms.
The simplex-counting arguments likewise use only standard logical axioms plus
the existing incidence, distinct-corner, and link certificates. The new
`supplied_oriented_face_count` native certificate verifies only that the
oriented face array has length 131,070. This explicit dependency appears in
the Euler theorem's axiom audit; no sphere theorem is assumed.
The finite-realization adapter and all new incidence arguments introduce no
additional native certificates or axioms.

All 309 vendored sources compile unchanged from the attributed upstream commit
in `Vendor/README.md`, with hashes checked by `scripts/audit_vendor.py`. The Jordan separation theorem, full strong Schoenflies theorem, and general
polygonal classification theorem
have only `propext`, `Classical.choice`, and `Quot.sound` as axiom dependencies.
The new closed-normalization invariant also uses only these logical axioms;
its diagram application adds no new native certificates. No rotation-conjugacy
theorem is imported or assumed. The
Jordan theorem applies to the transported candidate curves in
`plane_curve_complement_component_count`, conditional on the plane
homeomorphism. The constructed `diagramPlaneHomeomorph` now supplies that argument.
The polygon endpoint quotient, its relabeling invariance, the canonical Euler
formulas, and the geometric vertex surjection use only standard logical axioms.
The input lower bound and sphere/plane construction reuse the existing
certificates, including the face-array length check, with no new native checks.
The subsequent local rotation proof adds one explicit native certificate,
`supplied_pole_link_action_verified`: it checks both 34-vertex link lengths,
validity of their encoded labels, and the shifts by 2 and 32 under the actual
label action. It does not certify a topological conjugacy. The generic polygon
equivariance, radial disk extension, and covering arguments use only standard
logical axioms.

The meridian construction adds two native certificates in
`MeridianCertificate.lean`. `meridian_labels_verified` checks the 18 labels
of each rotated arc, their bounds and endpoint values, the rotation action,
and injectivity of every distinct pair's 34-vertex boundary.
`meridian_triangles_verified` checks explicit triangle witnesses for every
boundary edge against `suppliedModel.oriented`. The generated face witnesses
come from `scripts/find_meridians.py`; that search program is outside the trust
boundary. The geometric arc, exact intersection, and Jordan-boundary proofs
are derived from these finite checks. No disk-sector conclusion is certified
or assumed by either check.

The sector construction adds seven explicit native checks in
`SectorCertificate.lean`: color bounds and rotation, coordinate-support masks,
overlap witnesses on boundary edges, boundary triangle witnesses, dual-edge
incidences, spanning-tree connectivity, and the 7,710-face count for each color.
`SectorData.lean` is generated by `scripts/find_sectors.py`. Its output is
untrusted until checked against the original oriented face array. The Python
Euler counts in `output/sector-certificate.json` are diagnostics, not the basis
of the disk proof.

The disk proof uses the full strong Schoenflies development from the same
pinned upstream checkout. Its 186 additional dependency modules are copied
unchanged, bringing the manifest to 309 modules. The generic
`compactJordanRegionHomeomorph`, `puncturedJordanDisk`, and their boundary-value
theorems have only standard logical axioms. They identify a compact planar set
whose frontier lies on its specified Jordan curve, and which has an interior
point off that curve, with the closed bounded Jordan region. Stereographic
projection from a proved point outside each sector supplies that planar setup.
No disk homeomorphism is supplied as an assumption or as native-checker data.

## Completed conjugacy construction

The global sphere and plane conjugacies are proved. The construction has the
following verified stages:

- Every nonfixed point has minimal period 17; all 17 iterates are distinct.
- `RotationGroup = Multiplicative (ZMod 17)` acts continuously and freely on
  `FreePlane`. Its orbit quotient projection is a covering map with exactly
  17 points in each fiber.
- Each certified pole link has 34 vertices. The coordinate action shifts the
  all-zero link by 2 positions and the all-one link by 32 positions. The circle
  parametrizations are proved equivariant, including the last-to-first edge.
  Thus their actual angles are `+2π/17` and `-2π/17`.
- Radial extension gives injective continuous disk parametrizations into the
  original `Diagram`, taking disk center to the respective pole. Their images
  are neighborhoods of those poles. `diagram_pole_disk_conjugacy` identifies
  the **actual** `diagramRotation` there with the corresponding Euclidean
  disk rotation, including the center.
- `diagram_meridian_system` constructs 17 embedded intervals in the actual
  `Diagram`, each with 17 edges and endpoints at the two poles. Distinct arcs
  meet **exactly** at those poles, including when considering edge interiors.
  Every pair of distinct arcs forms an embedded circle. The symmetry advances
  the arc index and preserves its real interval parameter.

- The actual closed sectors form a compact, path-connected cover of `Diagram`.
  They rotate cyclically and share points only on their designated boundaries.
  Each boundary is the union of its two consecutive meridians.
- `sectorDiskHomeomorph` identifies every sector with the closed Euclidean
  unit disk. `sectorDiskHomeomorph_boundary` retains the prescribed circle
  parameter, rather than just asserting an unspecified disk homeomorphism.
- `equivariantSectorDisk` transports the chart of sector zero by the actual
  symmetry. Its boundary theorem retains those same parameters, and its
  rotation theorem says that passing to the next sector preserves the disk
  coordinate, including the wrap from 16 to 0.
- `axialRotation` is a proved Euclidean isometry of three-dimensional space:
  complex multiplication in the horizontal plane with the vertical coordinate
  fixed. `rigidSphereRotation` restricts it to the actual unit sphere, and
  `rigidGenerator` is exactly `Circle.exp (2π/17)`.
- The target meridian curves have an explicit formula: the real part of the
  circle parameter is the height, and its positive/negative imaginary parts
  select the two horizontal meridian rays. They are continuous and injective
  for distinct directions and rotate with the rigid generator.
- `sphereLuneDisk` supplies boundary-preserving disk charts for the spherical
  lunes. `equivariantRigidSectorDisk` transports the chart of sector zero by
  rigid rotations. Its boundary and rotation equations include wraparound.
  `rigid_sectors_cover` proves coverage of the entire sphere, and
  `rigid_sector_inter_subset_boundary` confines distinct-sector overlaps to
  their specified meridians, including the common poles. These target results
  have only standard logical axioms; no new native certificate is used.
- `sectorConjugacy` is an actual homeomorphism from each source sector to the
  corresponding target sector. `sectorConjugacy_boundary` preserves the
  specified parameters, and `sectorConjugacy_rotation` intertwines the actual
  diagram symmetry with the rigid Euclidean rotation, sector by sector.
- `diagramMeridianBoundaryMap_front` and `diagramMeridianBoundaryMap_back`
  identify the forward and reversed halves with the same interval parameters.
  `meridian_parameter_compatibility` proves that source and target meridian
  points are equal under exactly the same conditions: equal interval parameters,
  and either equal meridian indices or a common endpoint.
- `sector_boundary_compatibility` discharges the boundary hypothesis of the
  closed-cover gluing theorem. `rigidSphereConjugacy_rotation` is the resulting
  unconditional global rotation equation. Its zero and one pole theorems place
  the actual diagram poles at the Euclidean north and south poles.
- `northStereographicComplex_rotation` proves equivariance of stereographic
  projection from that north pole. Its horizontal chart is specified explicitly;
  no arbitrary coordinate choice is assumed to commute with rotation.
  `rigidPlaneHomeomorph_rotation` gives the actual plane conjugacy.
- `supplied_simple_rotational_venn` transports the already proved curves, sides,
  membership regions, and crossing charts through that plane homeomorphism.
  `rigidPlaneRotation_complex` identifies the rotation with multiplication by
  `Circle.exp (2π/17)` in orthonormal plane coordinates. Reversing the file's
  decreasing curve-index order gives the requested positive successor action.

No periodic-homeomorphism classification or rotation-conjugacy theorem is
assumed. These final arguments introduce no new native certificates or axioms;
their dependencies are recorded in `topology-axioms.txt`. The file-specific
finite certificates still use the explicitly documented `native_decide` trust
boundary. The final theorem has no unproved geometric assumptions or `sorry`.

There are no remaining obligations for the stated simple rotational Venn
property. Explicit region disk homeomorphisms or an executable drawing would
be further strengthening/output tasks; neither is required by the geometric
Venn definition proved by `supplied_simple_rotational_venn`.
