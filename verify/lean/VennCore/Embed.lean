import Lean

open Lean Elab Term

/-- Embed the exact file text as a string literal in the theorem's definition.
This elaborator does not assert any propositions or run the checker. -/
elab "input_file% " path:str : term => do
  let text ← IO.FS.readFile path.getString
  return mkStrLit text
