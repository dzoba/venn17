# Project source bundle: the 17-curve Lean proof

Start with `VennTopology/RotationalVenn.lean`. The main theorem is
`Venn17.Topology.supplied_simple_rotational_venn`; its precise statement is
`SimpleRotationalVenn` in that same file. `README.md` and `REALIZATION.md`
describe the construction and the explicit native-computation trust boundary.

## Included

- All project Lean sources, the original `message.txt`, and the input JSON.
- All 309 vendored topology modules, attribution, licenses, and source hashes.
- `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`, pinning the Lean
  version and the exact revisions of Mathlib and all eight other Lake dependencies.
  Lake downloads those dependencies during setup; `.lake/` is omitted from this ZIP.
- Checker and audit scripts, finite certificate generators and reports,
  `topology-axioms.txt`, and the successful 3,468-job build log in `verification/`.
- A per-file SHA-256 inventory and `verify_bundle.py` to check extraction integrity.

The archive contains sources, not compiled proof caches or the Lean executable.
The unrelated website and drawing HTML are omitted.

## Rebuild

Install Git and the Lean toolchain manager `elan` on the destination machine.
Python 3 is needed for the integrity and independent audit scripts.
Extract the ZIP (for example, `unzip venn17-lean-proof.zip` on macOS/Linux).
Run these commands from the extracted `venn17-lean-proof` directory:

```sh
python3 verify_bundle.py
elan toolchain install leanprover/lean4:v4.32.1
lake exe cache get
lake build
lake env lean scripts/audit_topology.lean
lake exe venn_check venn17-local-c3-s2.json
python3 scripts/audit_vendor.py
```

Internet access is required to install the toolchain and fetch the pinned
Git dependencies and recommended Mathlib compiled cache. `lake exe cache get`
fetches missing dependencies using the repository URLs and exact commits in
`lake-manifest.json`, then downloads the compiled cache. Without the cache,
`lake build` can build the fetched dependencies from source, which is substantially
slower and may require additional platform build tools. The `Vendor/` directory
is included because these local topology sources are not fetched by Lake.
Keep `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json` unchanged.
Do not run `lake update`: the lockfile already pins the audited revisions.

`verification/full-build.log` and `topology-axioms.txt` record verification in
the original workspace. Rebuilding and rerunning the audit independently
checks the proof on the recipient's machine. Large finite checks use
`native_decide` and therefore trust Lean's compiler/runtime as documented.
The final geometric theorem has no `sorry` or assumed geometric conclusions.

## What the result does and does not assert

The theorem proves Jordan curves, all nonempty connected membership regions,
topological transverse crossings without triples, and an actual rigid plane
rotation by 2π/17. The curve index order is reversed from the file's decreasing
order to state the rotation as i ↦ i+1. This is a result for the supplied file,
not a general soundness/completeness theorem for the checker on arbitrary JSON.
It does not assert differentiable curves or a separate classification of every
spherical membership region as a disk. The reference SHA256SUMS file mentioned
in message.txt was not supplied; the included SHA256SUMS was computed locally.

## License

The original Lean proof and checker code, supporting scripts, and project
documentation are licensed under Apache-2.0; see `LICENSE` and the licensing
section of `README.md`. Vendored sources and Lake dependencies retain their
upstream licenses and notices. The supplied `message.txt` and
`venn17-local-c3-s2.json` are not relicensed by this grant.

## Citation

See `CITATION.cff` for the citation of this formalization: Justin Grimes,
*Lean formalization of a simple rotationally symmetric 17-Venn diagram*,
version 1.0.0, released September 18, 2026. This citation credits the
formalization only, not the original diagram or input certificate.
