# Credits and provenance

## Upstream formalization

Justin Grimes is the author identified by the supplied `CITATION.cff` for the
Lean formalization of a simple rotationally symmetric 17-Venn diagram. That
formalization is the source of this dimension-19 port. The original
`CITATION.cff` and Apache-2.0 `LICENSE` remain byte-identical at the package root
and under `provenance/upstream-17/`.

The root citation intentionally continues to describe the upstream Lean17
release. No new personal authorship, release version, or publication metadata
has been invented for this local port.

The 309 files under `Vendor/` are byte-identical to the upstream bundle. Their
source headers and `Vendor/README.md` retain their own authorship and licensing
notices.

## 19-curve certificate discovery

The Claude-led search workflow coordinated candidate discovery and recorded the
independent verification transcript for the selected seed-196002 certificate.
The preserved discovery record is under `provenance/candidate-discovery/`.
Those search and Python checks are independent evidence; they are not Lean
proof assumptions.

## Port and verification

Codex performed the dimension-19 source port and audit: namespace and numerical
adaptation, generated meridian and sector witnesses, pole-orientation checking,
source-difference review, controlled baseline and Lean19 builds, axiom
comparison, theorem-interface checking, and package assembly.

These workflow credits distinguish who performed the search and porting work.
They do not replace Justin Grimes's upstream authorship or the individual
authorship notices in vendored sources.
