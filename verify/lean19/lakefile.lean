import Lake
open Lake DSL

package venn_proof where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "520045ab14e26149ee970e2e617ca04b09bde5d6"

input_file diagram where
  path := "venn19-closure-s196002.json"
  text := false

lean_lib VennCore where
  precompileModules := true

lean_lib JordanCurve where
  srcDir := "Vendor"

lean_lib ClassificationOfSurfaces where
  srcDir := "Vendor"

lean_lib Schoenflies where
  srcDir := "Vendor"

@[default_target]
lean_lib Venn19 where
  needs := #[diagram]

@[default_target]
lean_lib VennTopology

@[default_target]
lean_exe venn_check where
  root := `Main
