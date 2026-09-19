import VennCore.Checker

def main (args : List String) : IO UInt32 := do
  let path := args.headD "venn17-local-c3-s2.json"
  let text ← IO.FS.readFile path
  match Venn17.audit text with
  | .error e =>
    IO.eprintln s!"FAIL: {e}"
    return 1
  | .ok r =>
    IO.println (repr r)
    if r.Passed then
      IO.println "PASS: all finite combinatorial checks. Geometric realization is not formalized."
      return 0
    else
      IO.eprintln "FAIL: at least one combinatorial check failed"
      return 1
