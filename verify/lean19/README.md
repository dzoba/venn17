# Simple rotationally symmetric 19-Venn diagram: Lean formalization

> **Verification status (2026-09-21): PASS.**
>
> The full Lean build completed 3,468 jobs successfully. All eight bounded
> postbuild checks passed, including source hashes, Lean tests, both independent
> executable checkers, Vendor integrity, the full axiom comparison, and compiled
> type ascriptions for both public final theorems.

This is a 19-curve port of Justin Grimes's Lean formalization of a simple
rotationally symmetric 17-Venn diagram. It checks the selected 19-curve finite
certificate, constructs its topological and planar realization, and proves a
simple rotational Venn theorem in Lean 4.

## Main theorem

The concrete theorem is:

```lean
Venn19.Topology.supplied_simple_rotational_venn :
  Venn19.Topology.SimpleRotationalVenn
    Venn19.Topology.rotationalVennCurve
    Venn19.Topology.rotationalVennSide
```

The public existential form is:

```lean
Venn19.Topology.exists_simple_rotational_venn_19 :
  ∃ (C : Fin 19 → Set Venn19.Topology.Plane)
    (S : Fin 19 → Bool → Set Venn19.Topology.Plane),
    Venn19.Topology.SimpleRotationalVenn C S
```

`SimpleRotationalVenn C S` states that:

- each of the 19 curves is the image of an injective continuous circle map;
- each curve has disjoint, path-connected inside and outside sides whose union
  is its complement, with bounded inside and unbounded outside;
- all `2^19 = 524,288` Boolean membership regions are path-connected and hence
  nonempty;
- no point lies on three distinct curves;
- every double intersection has a local crossing-square chart; and
- rigid positive rotation through `2π/19` sends curve `i` to curve `i + 1`.

The proof source is
`VennTopology/RotationalVenn.lean`. The theorem has no remaining geometric or
conjugacy hypothesis: it is instantiated with the realization constructed from
the selected certificate.

## Selected certificate

The embedded input is:

```text
venn19-closure-s196002.json
SHA-256 ed26b3baa6e5c02bc3a4239b1dfbf84d66f731cad2dd2805a8c1770e2c1fdb5d
47,185,825 bytes
524,286 quadrilateral faces
```

Its dual has 524,288 region vertices and 1,048,572 edges. Generated Lean
witnesses include a 20-vertex pole-to-pole meridian and 19 sectors. Every sector
has 27,614 vertices, 55,207 edges, 27,594 faces, Euler characteristic 1, and 38
boundary edges. A separate orientation check found curve-link steps `[1, 18]`
and triangulated pole-link steps `[2, 36]`.

## Trust boundary

The audited final theorem closure contains Lean's three standard logical
axioms:

```text
propext
Classical.choice
Quot.sound
```

It also contains 20 input-specific `native_decide` axioms. These certify the
large finite data: graph and incidence structure, link stars, face counts,
curve and crossing labels, curve polygons, rotational identities, meridian
witnesses, and sector properties. `native_decide` trusts Lean's compiler and
runtime for those computations; this is not a claim of full kernel reduction
of the 47 MB certificate.

The generic topology, connectivity, simplex-intersection, geometric
realization, Schoenflies, conjugacy, and gluing arguments remain ordinary
kernel-checked Lean proofs. There are no `sorry`s or hand-written mathematical
axioms in the project.

The Lean17 baseline and Lean19 result were audited at exactly 20 corresponding
native axioms plus the three logical axioms. After the documented `Venn17` to
`Venn19` rename, the full audit outputs and the final theorem axiom lists match.

## Reproduce

The project pins Lean `leanprover/lean4:v4.32.1` and these dependency
revisions in `lake-manifest.json`:

| Package | Revision |
|---|---|
| Mathlib | `520045ab14e26149ee970e2e617ca04b09bde5d6` |
| plausible | `e12c1910fe855cbfc38803cd4e55543906d5fa62` |
| LeanSearchClient | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| importGraph | `7e9612bf0b9ee66db3cb5b9988a35afc706f5a12` |
| proofwidgets | `6e311e2a844da9b2cc3971187df2fe0066947b93` |
| aesop | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` |
| Qq | `38d591e778f100aec9762bb582f9c7f55f50e9dc` |
| batteries | `023ce7d62a0531e22a5331e20b587817a80d49ff` |
| Cli | `88679d088c9720c27ebdf2ba4dafe17341747f94` |

From the project root:

```sh
lake exe cache get
lake build
lake exe venn_check venn19-closure-s196002.json
python3 scripts/check.py --output audit.json
python3 scripts/test_checkers.py
lake build Venn19.Tests
lake env lean scripts/audit_topology.lean
python3 scripts/audit_vendor.py
shasum -a 256 -c SHA256SUMS
```

The checked build used `LEAN_NUM_THREADS=1` and disabled downloads with
`lake --no-cache --no-ansi build`. Dependency cache acquisition is shown for a
fresh checkout; it was not part of the measured build.

## Measured build

The successful Lean19 build completed 3,468 jobs with these measurements:

| Measurement | Value |
|---|---:|
| Controller elapsed time | 1,208.53 s |
| `/usr/bin/time` real time | 1,205.65 s |
| User / system CPU time | 911.98 s / 177.35 s |
| Maximum resident set reported by `time` | 4,169,744,384 bytes |
| Sampled aggregate RSS lower bound | 4,959,027,200 bytes |
| Largest sampled Lean process | 4,137,058,304 bytes |
| Owned project bytes at completion | 1,789,259,776 bytes |
| Exit code | 0 |

The sampled peak is a lower bound from two-second process polling. The largest
sampled module was `VennTopology/SectorCertificate.lean`. The generic Vendor
artifacts were accepted by a separate content-rehash/no-build check of all 309
modules in 12.89 seconds, with exit code 0.

This was a controlled port build with those byte-identical generic Vendor
artifacts reused from the freshly built Lean17 baseline. The elapsed time is
therefore not a clean-checkout or cold-dependency-cache benchmark. The baseline
itself compiled all 309 Vendor sources before their artifacts were reused.

## Verification results

All release checks passed:

- all 457 prepackaging source hashes matched;
- `lake build Venn19.Tests` passed;
- `lake exe venn_check venn19-closure-s196002.json` passed;
- independent `scripts/check.py` and corruption/invariance regression tests
  passed;
- all 309 Vendor modules remained byte-identical to upstream;
- the complete topology axiom audit matched the Lean17 baseline after only the
  documented namespace rename;
- the final theorem contains 20 native-decision axioms and the three logical
  axioms listed above; and
- compiled type ascriptions and recorded `#check`/`#print` output confirmed both
  final theorem interfaces.

The complete evidence is under `verification/lean19/`; baseline comparison is
under `verification/baseline17/`. The root `audit.json`, `lean-audit.txt`, and
`topology-axioms.txt` are the 19-specific outputs from the passing run.

## Credit and provenance

Justin Grimes is the author named by the upstream formalization's
`CITATION.cff`. The upstream source, Vendor modules, license, and citation are
preserved as provenance under Apache-2.0.

The root `CITATION.cff` remains byte-identical to Justin Grimes's supplied
Lean17 citation and therefore still describes that upstream release. It is kept
unchanged to avoid inventing release authorship or version metadata. See
`PORT-CREDITS.md` for the factual port and verification roles.

Claude coordinated the 19-candidate discovery and recorded the independent
certificate-verification transcript. Codex performed the dimension-19 source
port, generated and checked the Lean witness data, audited the transformed
sources and axiom boundary, and ran the controlled baseline and Lean19 builds.
These workflow credits do not replace Justin Grimes's authorship of the
formalization.

The original Lean17 documentation and evidence are preserved byte-for-byte in
`provenance/upstream-17/`. Working-port reviews and the historical 457-entry
prepackaging manifest are in `provenance/port-working/`.
