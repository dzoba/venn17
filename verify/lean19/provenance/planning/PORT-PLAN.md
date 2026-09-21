# Lean 19 port inventory and critical path

## Conclusion

The Lean 17 development can be duplicated as an exact 19-curve analogue, but it is not a one-file input swap. The finite checker, geometric realization, cyclic action, meridian construction, sector construction, rigid rotation, theorem statements, executable, tests, and audit all contain dimension-specific constants. The vendored topology library is generic and has no bare numeric `17` sites; it should remain byte-for-byte unchanged.

The target certificate is `venn19-closure-s196002.json`, SHA-256 `ed26b3baa6e5c02bc3a4239b1dfbf84d66f731cad2dd2805a8c1770e2c1fdb5d`. A streaming scan, which did not construct the large Python graph, confirmed 524,286 faces and exactly 55,188 crossings incident to every one of the 19 bit positions.

## Build-critical path

1. Duplicate the source bundle and retain the pinned Lean 4.32.1, Mathlib commit, Lake manifest, all 309 vendor modules, licenses, and notices. Rename only the project-owned module tree and namespace from `Venn17` to `Venn19`.
2. Change the Lake input dependency and embedded file to the selected 19 certificate. Keep the input SHA in `Venn19/Proof.lean` and in the bundle manifest.
3. Port the finite core first: parser dimension, graph sizes, 19 curve graphs, bit rotation by 18 positions, order 19, the two poles `0` and `524287`, and `Report.Passed` counts.
4. Regenerate `MeridianData.lean`. This mathematical feasibility gate passed: the adapted search found a 20-vertex pole-to-pole path and 19 rows of 19 face witnesses.
5. Regenerate `SectorData.lean`. This gate also passed: cutting along the 19 rotated meridians yielded exactly 19 components, each bounded by adjacent meridians, with the expected counts. A separate orientation reconstruction confirmed the required pole-link steps 2 and 36.
6. Port the geometric constants: `Fin 19`, `Fin 20`, `Fin 38`, pole link size 38, and rigid angles `2π/19`. Then port the derived counting theorems and final `SimpleRotationalVenn` statement.
7. Build in layers so failures are attributable: finite proof and graph certificate; dataset/link/curve certificates; symmetry and counts; meridian; sector; sphere/plane conjugacy; final theorem and axiom audit.

The 19 JSON is about 4.35 times as large as the 17 JSON. Most large checks are approximately four times the data volume. Checks that scan every face for every curve or sector can approach 4.5–5 times the work. `native_decide` also emits compiled artifacts, so peak memory and disk use may scale less gently than wall time.

## Replacement formulas

For `n = 19`:

| Quantity | Formula | 17 value | 19 value |
|---|---:|---:|---:|
| regions | `2^n` | 131,072 | 524,288 |
| north pole | `2^n - 1` | 131,071 | 524,287 |
| crossings/quadrilaterals | `2^n - 2` | 131,070 | 524,286 |
| arrangement arcs | `2(2^n - 2)` | 262,140 | 1,048,572 |
| crossings per curve | `2(2^n - 2)/n` | 15,420 | 55,188 |
| curve-polygon vertices | `4(2^n - 2)/n` | 30,840 | 110,376 |
| faces per sector | `(2^n - 2)/n` | 7,710 | 27,594 |
| sector vertices | `(2^n - 2)/n + n + 1` | 7,728 | 27,614 |
| sector edges | `2(2^n - 2)/n + n` | 15,437 | 55,207 |
| boundary edges per sector | `2n` | 34 | 38 |
| triangulation vertices | `2^(n+1) - 2` | 262,142 | 1,048,574 |
| triangulation edges | `6(2^n - 2)` | 786,420 | 3,145,716 |
| triangulation triangles | `4(2^n - 2)` | 524,280 | 2,097,144 |

The 19 per-curve value is measured directly from the certificate and also agrees with the formula. The sector counts are the exact analogue expected if the generated cut has the same topology; `find_sectors.py` must confirm them.

## Selective small-number changes

Do not globally replace `16`, `18`, `33`, or `34`.

- Rotation shift, inverse iterate, last curve index: `16 → 18`.
- Meridian point type and split: `Fin 18 → Fin 20`, `< 18 → < 20`; last point `17 → 19`; last edge `16 → 18`.
- Boundary type and modulus: `Fin 34 → Fin 38`, `%34 → %38`, `34-j → 38-j`, `33-j → 37-j`.
- Pole triangulated-link size: `34 → 38`; north step remains `2`; south step `32 → 36`.
- Angular identities: `(2π/34)*2 = 2π/17` becomes `(2π/38)*2 = 2π/19`; `(2π/34)*32 = -2π/17 + 2π` becomes `(2π/38)*36 = -2π/19 + 2π`.
- Regenerate all witness numbers in `MeridianData.lean` and `SectorData.lean`; do not transform their face indices.

The toy numbers elsewhere in `Venn17/Tests.lean` (`4`, `5`, `7`, `8`, `24`, and similar) describe small fabricated examples and must remain unchanged. Its five dimension-specific guards at lines 12–14 and 44–46 do change to 19/18. The Python adversarial tests contain both dimension-specific lengths and deliberately invalid 16/18 lengths; rewrite those cases semantically rather than replacing all numerals. No vendor Lean file contains a bare numeric 17 match.

## Generated certificate scripts

`find_meridians.py` hardcodes the input filename, rotate shift 16, orbit loop 16, north pole 131071, expected path length 18, 17 rotations, namespace, and status text. For 19 these become shift 18, orbit loop 18, pole 524287, path length 20, and 19 rotations. Its current representation loads the full JSON and constructs adjacency sets and an orbit-representative dictionary; at 19 this can consume several GiB.

`find_sectors.py` hardcodes the same input and rotation plus all `range(17)` loops and modulo 17 operations. It builds the full face list, edge-to-face dictionary, adjacency, colors, and components simultaneously. This is likely the peak-memory generator. Run it only after the meridian gate passes, with a memory limit and a timeout. If memory is a problem, retain only compact integer arrays or use an external-sort edge stream; do not weaken the Lean certificate.

The single-character sector encoding remains valid for 19 sectors (`A` through `S`). Its output grows from about 136 KB to roughly 0.53 MB.

## Native computation and axiom boundary

There are 27 `native_decide` proof invocations. The final theorem `supplied_simple_rotational_venn` depends on 20 of their generated compiler-trust axioms plus Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The exact 20 names are in `inventory.json`. The seven invocations outside the final dependency closure are the three standalone finite-checker theorems in `Venn17/Proof.lean`, `rotation_witnesses_pass`, `supplied_fixed_triangles_verified`, `supplied_pole_link_action_verified`, and `sector_face_counts_verified`. Preserve the same relative dependency set after namespace renaming and compare the new `#print axioms` output mechanically.

There are no explicit `axiom` declarations and no `sorry` terms in project or vendor Lean source. The word `sorry` appears only in vendor documentation. The port must add neither.

The heaviest native computations are expected to be `graph_certificates_pass`, `supplied_link_stars_verified`, `supplied_curve_polygons_verified`, `supplied_incidence_verified`, `supplied_rotation_verified`, and the sector overlap/connectivity checks. `sectorOverlapCheck` has the clearest superlinear constant increase because it nests face corners, all 19 colors, and up to 38 boundary positions.

## Theorems to preserve

The endpoint remains the exact analogue of:

- `Venn19.Topology.supplied_simple_rotational_venn`
- `Venn19.Topology.exists_simple_rotational_venn_19`

Its `SimpleRotationalVenn` structure asserts 19 Jordan curves in the plane, two open connected sides per curve, all `2^19` membership intersections path-connected, no triple points, crossing charts at every double point, and transport by the rigid positive rotation through `2π/19`.

The audit should retain the existing intermediate theorem families: finite file acceptance and pattern coverage; surface and triangulation; embedded curves, sides, regions, and transverse crossings; sphere classification and punctured plane; exact period and fixed points; meridians and sectors; rigid sphere conjugacy; stereographic plane conjugacy; final rotational Venn theorem.

## Licensing and citation

Keep the Apache-2.0 `LICENSE`, `Vendor/README.md`, all upstream source headers and licenses, `classification-sources.json`, and vendor hashes. Keep the original `CITATION.cff` as provenance for Justin Grimes's 17-curve formalization, or add port-specific citation metadata without rewriting authorship of the original work. The source bundle explicitly says `message.txt` and the 17 input certificate were not relicensed by its grant; treat the new 19 certificate's repository provenance separately and preserve its SHA-256 and accompanying README.

## Machine inventory

`dimension-sites.tsv` records every matching non-vendor Lean/Python source line for the main constants and the selectively reviewed small numbers: 879 lines across 79 files, comprising 1,024 matched tokens. Two files are test code and 77 are production or support files. `inventory.json` contains the formulas, native proof sites, exact final native-axiom names, and generator gates. Namespace/import renames are broader than this numeric inventory: every project-owned `Venn17` module and `namespace Venn17` declaration must become `Venn19`; vendor namespaces stay unchanged.
