# Venn 19 Lean source port

This directory is a source-level port of Justin Grimes's Lean formalization of a simple rotationally symmetric 17-Venn diagram to the selected 19-curve certificate.

## Status

- Source namespace and project-owned module paths are ported from `Venn17` to `Venn19`.
- Dimension and derived-count constants have been reviewed and ported to 19.
- The selected input is `venn19-closure-s196002.json`, SHA-256 `ed26b3baa6e5c02bc3a4239b1dfbf84d66f731cad2dd2805a8c1770e2c1fdb5d`.
- `scripts/find_meridians.py` succeeded and generated a 20-vertex pole-to-pole seed plus 19 rows of 19 face witnesses.
- `scripts/find_sectors.py` succeeded and generated 19 sectors. Each has 27,614 vertices, 55,207 edges, 27,594 quadrilaterals, Euler characteristic 1, and 38 boundary edges.
- `scripts/check_pole_steps.py` reconstructed the global face orientation and confirmed curve-link steps `[1, 18]`, hence triangulated pole-link steps `[2, 36]` exactly as required by `PoleRotationData.lean`.
- No Lean 19 build or `native_decide` run has been performed yet. The generated data remain unverified by Lean until that build succeeds.

## Intended endpoint

The final theorem is `Venn19.Topology.supplied_simple_rotational_venn`, with existential wrapper `Venn19.Topology.exists_simple_rotational_venn_19`. It is intended to preserve the 17 proof's theorem structure and relative axiom boundary: standard logical axioms plus the same 20 input-specific native-decision dependencies in the final theorem closure.

## Provenance and retained files

`LICENSE`, `CITATION.cff`, and `Vendor/` are byte-for-byte copies of the upstream 17 source bundle. The upstream `README.md`, `REALIZATION.md`, `BUNDLE-README.md`, `message.txt`, `BUNDLE-MANIFEST.json`, `SHA256SUMS`, `audit.json`, `lean-audit.txt`, `topology-axioms.txt`, and `verification/` are retained as upstream provenance. They describe or hash the 17 build and are stale for this port until regenerated; they are not evidence that the 19 proof builds.

The local `.lake/packages` is a symlink to the existing pinned dependency cache. Dependencies are not copied into this directory. The Lean toolchain and `lake-manifest.json` remain pinned to the upstream versions.

## Reproducible source checks

Run from this directory:

```sh
shasum -a 256 venn19-closure-s196002.json
python3 scripts/find_meridians.py
python3 scripts/find_sectors.py
python3 scripts/check_pole_steps.py
jq '{path_length:(.path|length), rows:(.faces|length), row_lengths:(.faces|map(length)|unique)}' output/meridian-certificate.json
jq 'map({vertices,edges,faces,euler,boundary_edges}) | unique' output/sector-certificate.json
```

`PORT-SHA256SUMS` inventories the active port source, selected input, generated certificates, and scripts. The broader planning inventory is in `../planning/`.

## Required verification before release

1. Build the pinned 17 baseline successfully.
2. Run the 19 build without `sorry` or new axioms.
3. Run `lake build Venn19.Tests`, `lake env lean scripts/audit_topology.lean`, the executable checker, and Python regression tests.
4. Confirm the final theorem's axiom list contains the same 20 relative native-decision dependencies after the namespace change.
5. Regenerate the bundle manifest, SHA list, audit outputs, build log, and port-specific citation metadata while retaining the original citation as provenance.
