import VennCore.Checker

namespace Venn17.LinkProof

/-- Three times a triangle number plus a corner selects an oriented triangle
dart. Triangle `4*f+k` has vertices `(n+f, fs[f][k], fs[f][k+1])`. -/
def triangleVertex (fs : Array Face) (n t j : Nat) : Nat :=
  if j%3 == 0 then n+t/4 else
    (fs.getD (t/4) #[]).getD ((t%4 + if j%3 == 1 then 0 else 1)%4) 0

def owner (fs : Array Face) (n d : Nat) : Nat := triangleVertex fs n (d/3) (d%3)
def tail (fs : Array Face) (n d : Nat) : Nat := triangleVertex fs n (d/3) ((d+1)%3)
def head (fs : Array Face) (n d : Nat) : Nat := triangleVertex fs n (d/3) ((d+2)%3)

abbrev Stars := Array (Array Nat)

/-- Propose cyclically ordered incident darts. The checker below verifies the
proposal, including coverage of every dart; this algorithm is not trusted. -/
def propose (fs : Array Face) (n : Nat) : Stars := Id.run do
  let mut tables : Array (Std.HashMap Nat Nat) := Array.replicate (n+fs.size) {}
  for d in [:12*fs.size] do
    tables := tables.modify (owner fs n d) (fun tab => tab.insert (tail fs n d) d)
  let mut out := #[]
  for tab in tables do
    let mut d := (tab.toArray.getD 0 (0,12*fs.size)).2
    let mut row := #[]
    for _ in [:tab.size] do
      row := row.push d
      d := tab.getD (head fs n d) (12*fs.size)
    out := out.push row
  return out

def rowCheck (fs : Array Face) (n v : Nat) (row : Array Nat) : Bool :=
  3 ≤ row.size && decide ((row.map (tail fs n)).toList.Nodup) &&
    (Array.range row.size).all fun k =>
      let d := row.getD k 0
      d < 12*fs.size && owner fs n d == v &&
        head fs n d == tail fs n (row.getD ((k+1)%row.size) 0)

def rowsCheck (fs : Array Face) (n : Nat) (stars : Stars) : Bool :=
  stars.size == n+fs.size &&
    (Array.range stars.size).all fun v => rowCheck fs n v (stars.getD v #[])

def positions (fs : Array Face) (stars : Stars) : Array Nat := Id.run do
  let mut out := Array.replicate (12*fs.size) (12*fs.size)
  for row in stars do
    for k in [:row.size] do out := out.setIfInBounds (row.getD k 0) k
  return out

def coverageCheck (fs : Array Face) (n : Nat) (stars : Stars) : Bool :=
  let pos := positions fs stars
  (Array.range (12*fs.size)).all fun d =>
    let v := owner fs n d
    let row := stars.getD v #[]
    let k := pos.getD d 0
    v < stars.size && k < row.size && row.getD k 0 == d

def check (fs : Array Face) (n : Nat) (stars : Stars) : Bool :=
  rowsCheck fs n stars && coverageCheck fs n stars

end Venn17.LinkProof
