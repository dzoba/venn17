# Lean proof of the 17-curve rotational Venn diagram

## License

The original Lean proof and checker code, supporting scripts, and project
documentation are licensed under the Apache License, Version 2.0
(`SPDX-License-Identifier: Apache-2.0`). See [LICENSE](LICENSE).

Vendored sources and Lake dependencies retain their upstream licenses,
copyright notices, and attribution; see [Vendor/README.md](Vendor/README.md)
and the license files in each dependency. This license grant does not relicense
the supplied `message.txt` or `venn17-local-c3-s2.json` input files.

## Citation

To cite this formalization, use [CITATION.cff](CITATION.cff):

Justin Grimes (2026). *Lean formalization of a simple rotationally symmetric
17-Venn diagram*. Version 1.0.0. Released September 18, 2026.

This citation credits the formalization only, not the original diagram or
input certificate.

## Proof

This project verifies the finite combinatorial checks in `message.txt` and
proves that `venn17-local-c3-s2.json` has a simple, rigidly rotational planar
Venn realization. The final theorem is
`Venn17.Topology.supplied_simple_rotational_venn` in
[`VennTopology/RotationalVenn.lean`](VennTopology/RotationalVenn.lean).
It has no unproved geometric hypotheses and no `sorry`. The finite
`native_decide` certificates remain part of the explicit trust boundary below.

The construction starts with a geometric realization of the file. Lean proves
that the realization is a compact, connected topological surface without
boundary, with an explicit finite simplicial complex and open disk charts. It
also has a homeomorphism of exact order 17 whose only fixed points are the
all-zero and all-one vertices.
The actual geometric triangulation now has proved counts of 262,142 vertices,
786,420 edges, and 524,280 triangles, giving simplicial Euler characteristic 2.
The same surface now has a checked finite barycentric triangulation in the
representation used by the vendored surface-classification library. Its
triangles form a connected graph through shared edges, and every edge belongs
to exactly two triangles. The counts and Euler characteristic hold directly
for this representation as well.
Lean constructs a polygon quotient homeomorphic to the diagram, proves Euler
characteristic invariant under every certified normalization move, and excludes
all positive-genus and boundary alternatives. This gives an unconditional
homeomorphism to the sphere. Removing the all-zero point and using stereographic
projection gives an unconditional homeomorphism to the Euclidean plane.

Lean now also constructs all 17 labelled embedded circles **on this surface**.
Their complement has exactly 131,072 connected components, indexed by the
patterns and containing their corresponding pattern vertices. Every component
is path connected. Distinct curves intersect only at the listed crossing
centers; every center belongs to exactly two curves, and triple intersections
are excluded. Each crossing now has an explicit open-square chart taking the
center to the origin and the two curves exactly to the coordinate axes.

Each individual circle now has exactly two nonempty path-connected sides on
the surface. Continuous signed bit functions have the circles as their exact
zero sets. Every region is exactly the intersection of the 17 sides selected
by its pattern, so the labels describe all of its points.

The symmetry now provably shifts the actual curve sets and whole pattern
regions. Removing the all-zero point preserves all 17 embedded circles and
exactly 131,072 nonempty path-connected regions, including the punctured
all-zero region. The restricted homeomorphism still has exact order 17 and
has just the all-one point as its fixed point.
Each individual curve still has exactly two nonempty path-connected sides
after this deletion, with the same bit interpretation.

`planar_venn_diagram_verified` now proves an actual planar Venn realization:
17 embedded circles, bounded bit-1 sides, unbounded bit-0 sides, and nonempty
path-connected regions for every one of the 131,072 membership choices.
The exact crossing locations, absence of triple intersections, and transverse
crossing charts also hold for these plane curves. An actual plane homeomorphism
of exact order 17 permutes their curves and regions as specified.

The rigid-rotation obligation is now proved. `rigidSphereConjugacy` glues
boundary-compatible sector homeomorphisms into a global sphere homeomorphism.
The specified stereographic projection commutes with axial rotation, giving
`rigidPlaneHomeomorph_rotation`. Its target is a linear Euclidean isometry,
`rigidPlaneRotation`, with complex formula multiplication by
`Circle.exp (2 * Real.pi / 17)` and center zero.

`supplied_simple_rotational_venn` combines the Jordan curves, bounded inside
and unbounded outside sides, all nonempty path-connected membership regions,
absence of triple intersections, transverse crossing charts, and this rigid
rotation. The file's generator sends curve `i` to `i-1`; reversing the cyclic
index order gives `rotationalVennCurve`, on which the positive rotation sends
`i` to `i+1`. `rigidPlane_membership_verified` retains the original file's
pattern labels and proves their unique occurrence in the rigid realization.
The proof construction is documented in `REALIZATION.md`.

The independent Python audit and the Lean checker both find:

| Quantity | Recomputed value |
| --- | ---: |
| Region patterns | 131,072 |
| Arcs | 262,140 |
| Crossings | 131,070 |
| Euler characteristic | 2 |
| Crossings on each curve | 15,420 |
| Patterns on either side of each curve | 65,536 |

All finite checks pass, including orientation, single vertex links, one cycle
per curve, connected sides, and orientation-preserving rotation. We additionally
check the one-step cyclic action at the two fixed regions.

The input SHA-256 is:

```text
c178d7bdde6e02b1b0c2780339434095d3633b8bb77a7293e9d575d04ad7ae77
```

This checksum was computed locally. The `SHA256SUMS` file mentioned in the
message was not supplied, so there is no independent comparison to that file.

## Reproduce

Lean 4.32.1 and Mathlib commit
`520045ab14e26149ee970e2e617ca04b09bde5d6` are pinned. The finite checker uses
Lean/Std; the geometric proofs use Mathlib. On a fresh checkout, fetch the
pinned dependencies and their compiled cache before building:

```sh
lake exe cache get
lake build
lake exe venn_check venn17-local-c3-s2.json
python3 scripts/check.py --output audit.json
python3 scripts/test_checkers.py
lake build Venn17.Tests
lake env lean scripts/audit_topology.lean
python3 scripts/audit_vendor.py
shasum -a 256 -c SHA256SUMS
```

`lake build` checks both `Venn17` and `VennTopology`, as well as the executable.
The JSON is a declared
Lake dependency: changing it invalidates the proof build. It is embedded as a
literal string in `suppliedJSON`, parsed by Lean, and checked by pure Lean
functions. The elaborator only embeds text; it does not assert facts. Builds
must run from the project root. A clean proof build can take several minutes.

The standalone executable returns 0 only when all checks pass, and 1 on a
rejected input. The Python checker is a separate implementation, not an input
to the Lean proof. It uses assertions and intentionally refuses `python -O`.

## Theorems and files

- `Venn17/Proof.lean`: `supplied_file_verified` proves the exact input yields a
  report with the stated counts and all checks passing. `every_pattern_occurs`
  directly states that every natural number below 2^17 occurs in a parsed face.
  `every_crossing_is_a_square` directly states the bit-square shape of each face.
- `VennCore/Connectivity.lean`: `treeCheck_sound` proves that a checked parent/rank
  certificate gives actual finite graph walks to a common root. Its proof uses
  well-founded induction and no native computation axiom.
- `Venn17/Facts.lean`: direct graph connectivity, degree-two, side connectivity,
  and oriented crossing-rotation statements for this input, using checked
  witnesses and the general connectivity theorem. The expensive spanning-tree
  certificate computation is cached in `Venn17/GraphCertificate.lean`.
- `VennCore/Checker.lean`: parser, graph construction, orientation reconstruction,
  link checks, curve checks, and rotation checks.
- `VennCore/Symmetry.lean`: explicit oriented-face rotation witnesses. The generic
  checker modules are precompiled; the large input and proofs remain Lean data.
- `VennTopology/SurfaceCertificate.lean`: `realized_surface_verified` assembles
  the current geometric conclusion. Import `VennTopology` to use it. The earlier
  `realized_candidate_verified` remains available.
- `VennTopology/Surface.lean`: `diagram_locally_open_disk` and the actual
  `diagramChartedSpace : ChartedSpace ℂ Diagram`.
- `VennTopology/FiniteRealization.lean`: a proved coordinate restriction and
  zero-extension homeomorphism to a finite barycentric realization.
- `VennTopology/FiniteTriangulation.lean`: `diagramFiniteTriangulation` and its
  exact vertex, edge, triangle, and Euler counts in the external representation.
- `VennTopology/TriangulationIncidence.lean`:
  `diagram_classification_input_verified` proves the library's surface-incidence
  conditions, exactly two incident triangles per edge, and Euler characteristic 2.
- `VennTopology/PolygonalModel.lean`: `diagramPolygonalHomeomorph` identifies
  the diagram with the polygon quotient used by the normalization proof.
- `VennTopology/ClosedNormalization.lean`: the twice-paired-edge property is
  invariant under every normalization move; all positive-boundary canonical
  forms are excluded.
- `VennTopology/ClassifiedSurface.lean`: `diagram_closed_classification` gives
  the sphere/closed-positive-genus alternatives. `diagramNormalization` retains
  the normalization trace, and `diagramCanonicalHomeomorph` identifies its
  canonical quotient with the original diagram.
- `VennTopology/PolygonVertices.lean`: defines the vertex classes of polygon
  edge endpoints and proves Euler-count invariance under signed relabeling and
  cyclic face rotation.
- `VennTopology/CanonicalEuler.lean`, `EulerSphereCriterion.lean`: proves the
  canonical counts `2`, `2 - 2p`, and `2 - p`, then excludes positive genus
  whenever the count is at least 2.
- `VennTopology/PolygonEulerLowerBound.lean`: maps polygon vertex classes onto
  all geometric vertices and proves the input's polygon Euler count is at least 2.
- `VennTopology/UnorientedEuler.lean`, `P1Euler.lean`, `P2Euler.lean`: explicit
  vertex-quotient equivalences prove Euler invariance for face reversal, edge
  subdivision, and face splitting. `PolygonWordWalk.lean` supplies the boundary
  walk lemmas, including empty-piece and traversal-direction cases.
- `VennTopology/NormalizationEuler.lean`: Euler invariance along every
  validity-safe certified normalization trace.
- `VennTopology/SphereReduction.lean`: the unconditional
  `diagramSphereHomeomorph` and exact polygon vertex count/Euler characteristic.
- `VennTopology/PlaneRealization.lean`: `diagramPlaneHomeomorph` and
  `planar_venn_diagram_verified`, with no assumed geometric homeomorphism.
- `VennTopology/PlaneArrangement.lean`: simplicity, exact crossings and their
  charts, and the plane symmetry's exact order and curve/region action.
- `VennTopology/RotationOrbits.lean`: full-length nonfixed orbits and the actual
  free orbit quotient as a covering with exactly 17 points in every fiber.
- `VennTopology/PolygonRotation.lean`, `ConeRotation.lean`: kernel-checked
  equivariance of polygon-circle parametrizations and their radial disk extensions.
- `VennTopology/PoleRotationData.lean`, `PoleRotation.lean`, `PoleDiskRotation.lean`:
  one explicit finite certificate for the two pole-link shifts, its geometric
  soundness, and local rigid-rotation conjugacies on disk neighborhoods in the
  original diagram. These do not assert a global conjugacy.
- `VennTopology/MeridianData.lean`, `MeridianCertificate.lean`, `MeridianGeometry.lean`,
  `MeridianArcs.lean`, `MeridianIntersections.lean`: explicit equivariant
  pole-to-pole arcs, exact intersections at the poles, and Jordan boundaries
  formed by pairs of arcs.
- `VennTopology/SectorCertificate.lean`, `SectorGeometry.lean`, `SectorConnected.lean`,
  `SectorIntersections.lean`, `SectorFrontier.lean`: checked compact connected
  sector cover, cyclic symmetry, and controlled geometric overlaps.
- `VennTopology/JordanDisk.lean`, `SectorDisk.lean`, `EquivariantSectorDisk.lean`:
  actual closed-disk charts preserving the meridian boundary parametrization,
  transported from sector zero to respect the actual symmetry.
- `VennTopology/RigidSphere.lean`, `SphereMeridians.lean`, `SphereLunes.lean`,
  `RigidSectorDisk.lean`, `RigidSectorCover.lean`, `RigidSectorIntersections.lean`:
  the actual Euclidean sphere rotation through `2π/17`, explicit meridians,
  boundary-preserving equivariant disk charts, and the target sector cover
  with overlaps confined to its meridian boundaries. These use only standard
  logical axioms.
- `VennTopology/SectorConjugacy.lean`: constructed homeomorphisms from each
  source sector to its rigid spherical sector, with boundary values and the
  sectorwise rotation equation proved unconditionally.
- `VennTopology/SectorGluing.lean`: closed-cover gluing from boundary compatibility.
- `VennTopology/MeridianBoundaryParameters.lean`, `MeridianParameterEquality.lean`:
  forward/reversed boundary parameters and identical source/target parameter
  identifications, including both endpoints.
- `VennTopology/RigidSphereConjugacy.lean`: proves `SectorBoundaryCompatibility`
  and constructs the unconditional global rigid sphere conjugacy.
- `VennTopology/EquivariantStereographic.lean`, `RigidPlaneConjugacy.lean`:
  projection from the specified north pole commutes with axial rotations and
  yields the rigid plane conjugacy.
- `VennTopology/RotationalVenn.lean`: the final `supplied_simple_rotational_venn`
  theorem, original pattern/crossing correspondence, exact period, and the
  successor convention for the curve indices.
- `Vendor/Schoenflies/`: the full strong Schoenflies proof and disk-extension
  construction, copied unchanged from the pinned topology dependency.
- `scripts/find_sectors.py`: proposes the face colors and boundary witnesses;
  Lean checks these data separately from the geometric disk proof.
- `scripts/find_meridians.py`: searches the finite orbit graph for the meridian
  path and emits face witnesses; Lean independently checks all used data.
- `VennTopology/ArrangementCertificate.lean`: `realized_arrangement_verified`
  combines the new curve, region, and intersection conclusions on the surface.
- `VennCore/CurvePolygon.lean`, `VennTopology/CurveCertificate.lean`: validates
  ordered midpoint polygons, disjoint coordinate supports, and complete coverage
  of all labelled triangle arms. Large computations are cached in `CurveData.lean`.
- `VennTopology/MidpointPolygon.lean`, `CurveGeometry.lean`, `DiagramCurves.lean`:
  injective circle parametrizations of the actual center-to-midpoint curves.
- `VennTopology/TriangleMidline.lean`, `Regions.lean`: identifies the geometric
  complement, proves region path connectivity, and constructs
  `diagramComponentsEquiv : ConnectedComponents diagramComplement ≃ Fin 131072`.
- `VennTopology/CurveIntersections.lean`: no triple intersections, no unlisted
  intersections, and exactly two labels through each listed crossing center.
- `VennTopology/CrossingSquare.lean`, `CenterChart.lean`, `CrossingAxes.lean`:
  explicit mutually inverse coordinate maps between each center star and an
  open square, with opposite arms mapped to coordinate axes.
- `VennTopology/CrossingCharts.lean`, `PuncturedCrossings.lean`:
  `diagram_transverse_crossing` and `punctured_transverse_crossing` prove
  topological transverse crossings for the actual labelled curves, before and
  after deleting the all-zero point. Both combined arrangement certificates
  now include this property.
- `VennTopology/ArmSymmetry.lean`, `RegionSymmetry.lean`, `CurveSymmetry.lean`:
  the periodic homeomorphism maps curve `i` to `i-1` modulo 17 and each whole
  pattern region to its bit-shifted region. The bit-flip compatibility identity
  is checked over all 131,072 patterns and all 17 bits.
- `VennTopology/PuncturedRegions.lean`: removing a region's marked vertex
  preserves path connectivity, proved using radial paths to a small link circle.
- `VennTopology/PuncturedArrangement.lean`, `PuncturedCertificate.lean`:
  `punctured_arrangement_verified` combines the curve, region, intersection,
  and exact-order symmetry results after deleting the all-zero point. It does
  not assert a homeomorphism of the punctured surface with the plane.
- `VennCore/Links.lean`, `VennTopology/LinkCertificate.lean`: checked cyclic
  enumerations with coverage of all 1,572,840 triangle darts.
- `VennTopology/CyclicPolygon.lean`, `LabeledPolygon.lean`: coordinate polygons
  are circles, proved through compact parametrizations with equal fibers.
- `VennTopology/GeometricLinks.lean`: identifies those circles with the actual
  simplicial links; `Stars.lean`, `ConeDisk.lean`, and `OpenStarDisk.lean`
  construct annuli and disk charts, including continuity at the center.
- `VennTopology/Planar.lean`: the proved general Jordan separation theorem,
  from the four attributed sources in `Vendor/JordanCurve/`. See `Vendor/README.md`.
- `topology-axioms.txt`: recorded dependencies of the combined theorem and
  the generic circle, disk, and Jordan theorems.
- `VennTopology/Realization.lean`, `Intersections.lean`: an explicit union of
  four triangles per quadrilateral in a real coordinate space, its compactness,
  exact simplex intersections, and its finite Mathlib simplicial complex.
- `VennTopology/Incidence.lean`, `Dataset.lean`: soundness of geometric incidence
  certificates, continuous path connectivity, and distinct corners for this file.
- `VennTopology/Automorphism.lean`, `Periodic.lean`, `DiagramSymmetry.lean`:
  coordinate homeomorphisms, preservation of the realization, the file's action
  on pattern points, and exact order 17.
- `VennTopology/FixedPoints.lean`: `diagram_rotation_fixed_iff` proves that
  there are exactly two fixed points, including at nonvertex points of the space.
- `VennCore/Incidence.lean`, `Rotation.lean`: executable witnesses and checks
  used by these topology theorems.
- `scripts/check.py`, `audit.json`: independent audit and its recorded output.
- `lean-audit.txt`: recorded output of the Lean executable on the supplied file.
- `scripts/test_checkers.py`: corruption and invariance tests for both checkers.
- `Venn17/Tests.lean`: small adversarial checks for restricted paths, forged
  trees, disconnected vertex links, bit numbering, and orientation reversal.
  Curve tests also reject overlapping coordinate supports, incorrect labels,
  corrupt edge witnesses, and a valid cycle that omits a second component.

Some results are direct mathematical propositions about the finite arrays and
graphs. The main audit theorem additionally certifies execution of the stated
algorithms. There is not yet a general theorem translating every report field
into a topological assertion about a realized surface. In particular,
`accepts_iff` unfolds the report contract; it is not a topology soundness theorem.

## Trust boundary

Large input-specific computations use `native_decide`. This explicitly trusts
Lean's compiler/runtime and creates per-computation axioms. The source prints
the dependencies with `#print axioms`; it does not hide them. The ordinary
logical dependencies include `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry`s or hand-written mathematical axioms in the project.

The generic connectivity, geometric realization, simplex-intersection, and
automorphism proofs are kernel-checked. Applications to the large file depend
on native checking of the proposed incidence, tree, cyclic-link, curve-polygon,
arm-label, crossing-label, and symmetry certificates. Curve symmetry also uses
an explicit native check of the finite bit-flip/rotation identity. The generic
punctured-region, square-chart, disk-chart, and Jordan theorems use no native
computation axioms. The new crossing-chart arguments introduce no additional
native checks or mathematical axioms. The later pole-rotation argument adds
one explicit native certificate checking the two 34-vertex links and their
cyclic shifts; the topological conjugacies on the disk neighborhoods are then
proved from it. Two further native certificates check the meridian labels and
triangle witnesses. Embedded arcs, their exact geometric intersections, and
the equivariant Jordan boundaries are proved from these checks; the Python
witness generator is not trusted. Seven further native sector checks certify
face colors, coordinate support and overlap conditions, boundary witnesses,
dual incidences, connectivity, and face counts. The disk conclusions use the
proved full Schoenflies theorem, whose axiom dependencies are only standard
logical axioms. All 309 vendored dependency modules compile unchanged and have
recorded upstream hashes.
This is not an entirely kernel-reduced computational proof. See the official
[Lean axiom documentation](https://lean-lang.org/doc/reference/latest/Axioms/)
and [proof-validation documentation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

To inspect the geometric theorem directly:

```lean
import VennTopology

#check Venn17.Topology.diagramSphereHomeomorph
#check Venn17.Topology.diagramPlaneHomeomorph
#check Venn17.Topology.planar_venn_diagram_verified
#print axioms Venn17.Topology.planar_venn_diagram_verified
#check Venn17.Topology.realized_surface_verified
#check Venn17.Topology.realized_arrangement_verified
#print axioms Venn17.Topology.realized_arrangement_verified
#check Venn17.Topology.diagramChartedSpace
#check Venn17.Topology.planar_jordan_separation
```

The checksum is an external reproducibility check, not a SHA-256 theorem in
Lean. The theorem concerns the embedded file text. Flags such as `full`,
`energy`, `missing`, `duplicates`, and `labels` are ignored.

## Encoding conventions

Character `i` is bit `i` of the natural-number encoding. `rotate` moves character
`i` to `i-1 mod 17`, exactly as item 7 requests. Input face order and the order
of the four strings are immaterial; square cycles are reconstructed.

The checker builds the **dual quadrangulation**: vertices are membership
patterns, edges are arcs, and quadrilateral faces are crossings. Thus the
Euler calculation is 131072 − 262140 + 131070 = 2. In the eventual curve
arrangement, these roles of vertices and faces are interchanged.
The geometric realization subdivides each quadrilateral into four triangles.
Lean now proves its simplex counts through bijections with the actual faces of
`diagramQuad.complex`, obtaining 262142 − 786420 + 524280 = 2.
The classification theorem and Euler invariance are now applied to this
realization, proving it is a sphere. Stereographic projection supplies the
plane realization. Boundary-compatible sector maps and equivariant
stereographic projection now give its proved conjugacy to rigid rotation.

An arc is identified by its unordered pair of region labels, as stipulated by
the message. This representation does not describe arbitrary arrangements
with parallel arcs between the same pair of regions. The result is a statement
about this encoding and this candidate, not a characterization of all possible
JSON encodings of Venn diagrams.
