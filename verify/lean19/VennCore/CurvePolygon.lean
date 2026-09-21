import VennCore.Links

namespace Venn19.CurveProof

abbrev PairVertex := Nat × Nat

structure Polygon where
  vertices : Array PairVertex
  triangles : Array Nat
  deriving Inhabited, Repr

def center (fs : Array Face) (n t : Nat) : PairVertex :=
  let c := LinkProof.triangleVertex fs n t 0
  (c,c)

def ends (fs : Array Face) (n t : Nat) : PairVertex :=
  let u := LinkProof.triangleVertex fs n t 1
  let v := LinkProof.triangleVertex fs n t 2
  (min u v, max u v)

def hasLabel (fs : Array Face) (n i t : Nat) : Bool :=
  let e := ends fs n t
  e.1 ^^^ e.2 == 2^i

/-- Assign each coordinate to its proposed polygon vertex. Validation checks
both endpoints against this table, so repeated supports cannot be hidden. -/
def supportOwners (bound : Nat) (vs : Array PairVertex) : Array Nat := Id.run do
  let mut out := Array.replicate bound vs.size
  for j in [:vs.size] do
    let p := vs.getD j (0,0)
    out := (out.setIfInBounds p.1 j).setIfInBounds p.2 j
  return out

def supportsCheck (bound : Nat) (vs : Array PairVertex) : Bool :=
  let owners := supportOwners bound vs
  (Array.range vs.size).all fun j =>
    let p := vs.getD j (0,0)
    p.1 < bound && p.2 < bound && owners.getD p.1 vs.size == j &&
      owners.getD p.2 vs.size == j

def edgeCheck (fs : Array Face) (n i : Nat) (p : Polygon) (j : Nat) : Bool :=
  let t := p.triangles.getD j (4*fs.size)
  let a := p.vertices.getD j (0,0)
  let b := p.vertices.getD ((j+1)%p.vertices.size) (0,0)
  t < 4*fs.size && hasLabel fs n i t &&
    ((a == center fs n t && b == ends fs n t) ||
     (a == ends fs n t && b == center fs n t))

def polygonCheck (fs : Array Face) (n i : Nat) (p : Polygon) : Bool :=
  3 ≤ p.vertices.size && p.triangles.size == p.vertices.size &&
    supportsCheck (n+fs.size) p.vertices &&
    (Array.range p.vertices.size).all (edgeCheck fs n i p)

def trianglePositions (fs : Array Face) (p : Polygon) : Array Nat := Id.run do
  let mut out := Array.replicate (4*fs.size) p.vertices.size
  for j in [:p.triangles.size] do
    out := out.setIfInBounds (p.triangles.getD j (4*fs.size)) j
  return out

def coverageCheck (fs : Array Face) (n i : Nat) (p : Polygon) : Bool :=
  let pos := trianglePositions fs p
  (Array.range (4*fs.size)).all fun t =>
    !hasLabel fs n i t ||
      let j := pos.getD t p.vertices.size
      j < p.vertices.size && p.triangles.getD j (4*fs.size) == t

def check (fs : Array Face) (n i : Nat) (p : Polygon) : Bool :=
  polygonCheck fs n i p && coverageCheck fs n i p

/-- Untrusted proposal: follow a crossing, its outgoing arc midpoint, and the
next crossing. Only the checked arrays enter the topological proof. -/
def propose (fs : Array Face) (n i : Nat) : Polygon := Id.run do
  let mut across : Std.HashMap PairVertex (Array Nat) := {}
  let mut incident : Array (Array Nat) := Array.replicate fs.size #[]
  let mut start := 4*fs.size
  for t in [:4*fs.size] do
    if hasLabel fs n i t then
      across := across.insert (ends fs n t) ((across.getD (ends fs n t) #[]).push t)
      incident := incident.modify (t/4) (·.push t)
      start := min start t
  let mut vs := #[]
  let mut ts := #[]
  let mut seen := Array.replicate fs.size false
  let mut t := start
  for _ in [:fs.size] do
    if t < 4*fs.size && !(seen.getD (t/4) true) then
      seen := seen.setIfInBounds (t/4) true
      vs := (vs.push (center fs n t)).push (ends fs n t)
      let others := across.getD (ends fs n t) #[]
      let s := if others.getD 0 (4*fs.size) == t then others.getD 1 (4*fs.size)
        else others.getD 0 (4*fs.size)
      ts := (ts.push t).push s
      let exits := incident.getD (s/4) #[]
      t := if exits.getD 0 (4*fs.size) == s then exits.getD 1 (4*fs.size)
        else exits.getD 0 (4*fs.size)
  return ⟨vs,ts⟩

/-- Every arm has one of the requested curve labels. -/
def labelsCheck (fs : Array Face) (n count : Nat) : Bool :=
  (Array.range (4*fs.size)).all fun t => (Array.range count).any fun i => hasLabel fs n i t

def edgeMask (fs : Array Face) (n t : Nat) : Nat :=
  (ends fs n t).1 ^^^ (ends fs n t).2

/-- Each crossing uses two distinct labels, alternating around the four arms. -/
def crossingLabelsCheck (fs : Array Face) (n : Nat) : Bool :=
  (Array.range fs.size).all fun f =>
    edgeMask fs n (4*f) != edgeMask fs n (4*f+1) &&
      (Array.range 4).all fun k =>
        edgeMask fs n (4*f+k) == edgeMask fs n (4*f+k%2)

end Venn19.CurveProof
