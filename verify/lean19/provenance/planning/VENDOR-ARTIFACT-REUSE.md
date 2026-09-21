# Reusing the generic Vendor artifacts

## Scope

The Lean 19 port keeps all 309 sources under `Vendor/` byte-identical to the
fresh Lean 17 baseline.  The reusable modules are exactly the modules rooted at
`JordanCurve`, `ClassificationOfSurfaces`, and `Schoenflies`.

For every module, the reuse manifest admits only seven files:

- `.lake/build/lib/lean/<Module>.olean`
- `.lake/build/lib/lean/<Module>.olean.hash`
- `.lake/build/lib/lean/<Module>.ilean`
- `.lake/build/lib/lean/<Module>.ilean.hash`
- `.lake/build/lib/lean/<Module>.trace`
- `.lake/build/ir/<Module>.c`
- `.lake/build/ir/<Module>.c.hash`

This is 2,163 files when the baseline is complete.  The script derives the
allow-list from the 309 source paths and records the SHA-256 and size of every
source and reused artifact.

`setup.json` is excluded because it contains absolute paths into the baseline
tree.  Objects, archives, dynamic libraries, and every artifact beneath the
`Venn17`, `Venn19`, `VennCore`, and `VennTopology` namespaces are also excluded.
The three generic libraries do not set `precompileModules`, so their normal
`leanArts` output has no module dynamic libraries to preserve.

## Safety gates and provenance

[`reuse_vendor_artifacts.py`](../reuse_vendor_artifacts.py) defaults to
`plan`.  It refuses unless `logs/baseline17/status.json` says `PASS`.  Before
writing a manifest, it verifies:

- identical `lean-toolchain` and `lake-manifest.json` files;
- identical `LICENSE` and `CITATION.cff` files;
- byte-identical Vendor sources;
- identical Lake configuration after normalizing only the reviewed diagram
  input and `Venn17`/`Venn19` library-name changes;
- all 2,163 allow-listed baseline artifacts exist.

The manifest records all hashes, byte counts, source paths, the baseline
command/status provenance, and the exclusions.  `apply` revalidates the PASS
status, all inputs, the saved allow-list, and every artifact hash.  It refuses
to overwrite a differing target file.  Copies go through a temporary file in
the destination directory and are verified before atomic replacement.  The
baseline is read-only throughout.

The Apache-2.0 `LICENSE` and `CITATION.cff` remain byte-identical in both trees;
the compiled outputs are copied with their original source attribution intact.

## Lake behavior

Lake 5.0.0-src from Lean 4.32.1 decides whether a Lean artifact is current by
comparing the newly computed dependency hash with `depHash` in `<Module>.trace`
and checking that its declared outputs exist.  A trace caption contains the
absolute source path, and its saved log contains old command paths, but captions
and logs do not contribute to `BuildTrace.hash`.  The source content hash,
imports, Lean version, options, module name, and package ID do contribute.  In
this port those inputs are unchanged for the three generic libraries.

`--rehash` sets Lake's `trustHash` option to false.  Lake recomputes file hashes
instead of trusting copied `.hash` files.  Combining it with `--no-build`
turns the first target-tree check into a strict gate: it succeeds only if every
requested artifact is already current and otherwise refuses to compile.

The check names all 309 modules explicitly.  Do not substitute the three Lean
library target names.  With Lake 5.0.0, the library-target form reports
`some modules have bad imports` in both this port and the already successful
baseline.  The error comes from `LeanLib.recCollectLocalModules` while it
collects a whole library; it does not identify a stale copied artifact.  The
explicit module form bypasses that collection path and checks each module's
actual `leanArts` trace and outputs.  The explicit check completed successfully
without `--rehash` before this procedure was updated (3,308 jobs, all current).

The copied trace may replay an old diagnostic log containing baseline paths.
That is cosmetic.  No `setup.json` with stale paths is copied.

## Commands after baseline PASS

From `/Users/dzoba/Developer/venn-diagram`:

```sh
python3 research/lean19-port/reuse_vendor_artifacts.py
python3 research/lean19-port/reuse_vendor_artifacts.py apply
python3 research/lean19-port/reuse_vendor_artifacts.py check
```

The first command writes
`research/lean19-port/planning/vendor-reuse-manifest.json` and changes no build
artifact.  The second performs only the manifest-authorized copies.  The third
first compares every target artifact with the SHA-256 manifest, then invokes
Lake as `lake --rehash --no-build --no-cache --no-ansi build` with all 309
explicit `+Module.Name` targets.  If it fails, do not run a normal Lean 19
build until the mismatch is understood.  On success, the later Lean 19 build
can reuse the generic libraries normally.

The rehash step writes `.hash` metadata for imported dependencies.  If the
shared `.lake/packages` cache is read-only in a sandbox, run this check with the
same filesystem permission used for the baseline build; it still cannot
compile because `--no-build` remains set.

## Expected saving

The fresh serial baseline completed 3,468 jobs in 3,093.9 seconds.  It spent
most of its long vendor phase on these 309 modules.  Reuse should remove that
elaboration work from the Lean 19 build, which is expected to save tens of
minutes at one Lean thread.  The completed seven-file reuse set is 271,488,573
bytes (about 259 MiB), as recorded in the manifest.

Copying is used instead of hard-linking so a later Lake write in the Lean 19
tree cannot change the proven baseline.  This costs roughly the final manifest
size in additional disk space.
