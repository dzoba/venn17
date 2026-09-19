import VennCore.Symmetry

namespace Venn17

def steps (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => f (steps f n x)

def regionStep (v : Nat) : Nat := if v < 2^17 then rotate v else v

def regionRotationCheck : Bool :=
  (Array.range (2^17)).all fun v => rotate v < 2^17 && steps regionStep 17 v == v

def faceShift (fs : Array Face) (table : Array Nat) (f : Nat) : Nat :=
  (fs.getD (table.getD f 0) #[]).findIdx (fun v => v == rotate ((fs.getD f #[]).getD 0 0))

def faceRotationCheck (fs : Array Face) : Bool :=
  let table := rotationWitnesses fs
  (Array.range fs.size).all fun f =>
    let g := table.getD f 0
    let s := faceShift fs table f
    g < fs.size && s < 4 && steps (fun f => table.getD f 0) 17 f == f &&
      (Array.range 4).all fun k =>
        regionStep ((fs.getD f #[]).getD k 0) == (fs.getD g #[]).getD ((k+s)%4) 0

def trianglePole (u v : Nat) : Nat := if u == 0 || v == 0 then 0 else 131071

/-- Check that a triangle and its rotated image can share only one of the
two distinguished region vertices. -/
def fixedTriangleCheck (fs : Array Face) : Bool :=
  let table := rotationWitnesses fs
  (Array.range fs.size).all fun f =>
    table.getD f 0 != f && (Array.range 4).all fun k =>
      let u := (fs.getD f #[]).getD k 0
      let v := (fs.getD f #[]).getD ((k+1)%4) 0
      let p := trianglePole u v
      decide ((u = regionStep u ∨ u = regionStep v) → u = p) &&
      decide ((v = regionStep u ∨ v = regionStep v) → v = p)

end Venn17
