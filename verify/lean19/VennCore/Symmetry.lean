import VennCore.Checker

namespace Venn19

def cyclicShifts (f : Face) : Array Face :=
  (Array.range 4).map fun k => (Array.range 4).map fun j => f[(k+j)%4]!

def rotationWitnesses (fs : Array Face) : Array Nat := Id.run do
  let mut lookup : Std.HashMap Nat Nat := {}
  for i in [:fs.size] do lookup := lookup.insert (faceKey fs[i]!) i
  return fs.map fun f => lookup.getD (faceKey (f.map rotate)) fs.size

/-- The final test compares actual arrays; it does not assume injectivity of faceKey. -/
def rotationWitnessCheckFor (fs : Array Face) : Bool :=
  let witnesses := rotationWitnesses fs
  (Array.range fs.size).all fun f =>
    let g := witnesses[f]!
    g < fs.size &&
      (cyclicShifts (fs[f]!.map rotate)).contains fs[g]!


end Venn19
