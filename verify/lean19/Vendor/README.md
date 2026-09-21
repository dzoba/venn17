# Vendored topology sources

The sources listed in `classification-sources.json` come from
https://github.com/mccorvie/classification-of-surfaces at commit
`e3c7230fe78d7b056a415d9ecae6f77887046b32`.

Copyright (c) 2026 ClassificationOfSurfaces contributors. Distributed under
Apache-2.0; the upstream license and source headers are retained.

The 309 modules are the combined dependency closure of
`ClassificationOfSurfaces.NormalForm`,
`ClassificationOfSurfaces.GeometricTriangulationRealization`, and
`Schoenflies.Main`, including the four `JordanCurve` modules. The full strong
Schoenflies development adds 186 unchanged modules to the previous closure. This now includes the actual
polygonal homeomorphism and normal-form classification proofs. Every source is
copied unchanged; the manifest records its SHA-256. Run
`python3 scripts/audit_vendor.py` from the project root to verify those copies.

Our surface is connected to the classification through its concrete
`diagramFiniteTriangulation`, proved incidence conditions, and explicit
`diagramPolygonalHomeomorph`. The generic classification produces alternatives;
it does not conclude that this particular surface is a sphere. Our normalization and Euler invariance proofs now exclude all non-spherical
alternatives, giving the actual sphere and plane realization. The full
Schoenflies development supplies disk charts for the proved meridian sectors;
it does not itself assert a conjugacy to rigid rotation.

The upstream project uses Lean 4.32.0 / Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`. These sources are checked again by
this project's pinned Lean 4.32.1 / Mathlib version. Any local port changes are
recorded below; the mathematical theorem statements are preserved.

Local port changes: none. All 309 sources compile unchanged with the pinned
Lean and Mathlib versions. `planar_jordan_separation`, `Schoenflies.schoenflies`, and the generic
`FiniteCyclicPresentation.hasEvalRepresentative` have only the standard
`propext`, `Classical.choice`, and `Quot.sound` axiom dependencies, as does our
new `PresentationClosedness.closed_classification` theorem.
