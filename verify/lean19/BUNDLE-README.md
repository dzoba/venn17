# Bundle contents

This directory is a standalone source-and-evidence package for the verified
Lean formalization of a simple rotationally symmetric 19-Venn diagram.

## Root-facing files

- `README.md` explains the theorem, trust boundary, reproduction, results, and
  attribution.
- `REALIZATION.md` describes the certified finite, spherical, and planar
  construction.
- `PORT-CREDITS.md` records factual upstream, discovery, port, and audit roles.
- `LICENSE` and `CITATION.cff` are byte-identical to the upstream Lean17 bundle.
  The citation describes that upstream release; it is preserved, not rewritten.
- `Venn19/`, `VennCore/`, `VennTopology/`, `Vendor/`, and the root `.lean` files
  are the exact sources that passed the recorded build.
- `venn19-closure-s196002.json` is the selected 47 MB certificate.
- `output/` contains the generated meridian and sector witness certificates.
- `scripts/` contains the checkers, generators, Vendor audit, and Lean axiom
  audit used by the recorded verification.
- `audit.json`, `lean-audit.txt`, and `topology-axioms.txt` are the corresponding
  Lean19 outputs from the passing postbuild run.
- `FINAL-THEOREM-AXIOMS.txt` extracts the exact 20 native and three logical
  axioms of the final theorem from that full audit.
- `verification/` contains every Lean19 build and postbuild log/timing file,
  baseline comparison evidence, and the Vendor artifact-reuse record.
- `provenance/upstream-17/` preserves the stale Lean17 documentation and
  evidence byte-for-byte.
- `provenance/port-working/` preserves the source review, transformation record,
  dependency pins, controllers, and historical 457-entry source inventory.
- `provenance/planning/` preserves the dimension-site and port inventories.
- `provenance/candidate-discovery/` preserves discovery metadata and checksums.

## Integrity files

`BUNDLE-MANIFEST.json` records the size, SHA-256, and category of every packaged
regular file except itself and `SHA256SUMS`. `SHA256SUMS` records every regular
file except itself and `BUNDLE-MANIFEST.json`. These mutual exclusions avoid
self-referential checksum recursion and are intentional.

Run:

```sh
python3 verify_bundle.py
python3 verify_release_inventory.py
shasum -a 256 -c SHA256SUMS
```

The first command is the unchanged upstream standard-library verifier and
verifies the JSON manifest. The second additionally rejects any unlisted file
or missing intentional exclusion. The third independently verifies the flat
checksum list.

## Deliberate exclusions

The package contains no `.lake` directory, compiled object, OLean, ILean,
dynamic library, dependency cache, cache symlink, or archive. Local absolute
paths remain in historical logs because those logs are preserved evidence of
the measured runs. They are not used by the source build.

This package has not been published externally.
