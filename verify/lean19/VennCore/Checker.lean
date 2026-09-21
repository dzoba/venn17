import Lean
import Std

namespace Venn19

abbrev Face := Array Nat
abbrev Graph := Array (Array Nat)

def failUnless (b : Bool) (message : String) : Except String Unit :=
  if b then .ok () else .error message

def parsePattern (n : Nat) (j : Lean.Json) : Except String Nat := do
  let s ← j.getStr?
  failUnless (s.length == n) "wrong pattern length"
  let mut v := 0
  let mut bit := 1
  for c in s.toList do
    failUnless (c == '0' || c == '1') "nonbinary pattern"
    if c == '1' then v := v + bit
    bit := bit * 2
  return v

def powerOfTwo (v : Nat) : Bool := v != 0 && (v &&& (v - 1)) == 0

/-- Canonical order is reconstructed; input order is never assumed cyclic. -/
def parseFace (n : Nat) (j : Lean.Json) : Except String Face := do
  let raw ← j.getArr?
  failUnless (raw.size == 4) "crossing must contain four patterns"
  let vs ← raw.mapM (parsePattern n)
  let u := vs.foldl min (2^n)
  let bits := (vs.map (fun v => v ^^^ u)).filter powerOfTwo
  failUnless (bits.size == 2) "crossing does not have two single-bit directions"
  let a := bits[0]!
  let b := bits[1]!
  failUnless (a != b) "crossing repeats a curve"
  let cycle := #[u, u ^^^ a, u ^^^ a ^^^ b, u ^^^ b]
  failUnless (cycle.all vs.contains && vs.all cycle.contains) "crossing is not a bit square"
  return cycle

def parse (text : String) : Except String (Array Face) := do
  let j ← Lean.Json.parse text
  let n ← (← j.getObjVal? "n").getNat?
  failUnless (n == 19) "expected 19 curves"
  (← (← j.getObjVal? "faces").getArr?).mapM (parseFace n)

def addNeighbor (g : Graph) (v w : Nat) : Graph :=
  g.modify v (·.push w)

/-- A bounded breadth-first traversal; all queued vertices are marked on insertion. -/
def reachable (g : Graph) (start : Nat) (allowed : Nat → Bool := fun _ => true) : Array Bool := Id.run do
  let mut seen := Array.replicate g.size false
  if start >= g.size || !allowed start then return seen
  seen := seen.set! start true
  let mut queue := #[start]
  for k in [:g.size] do
    if k < queue.size then
      for w in g[queue[k]!]! do
        if w < g.size && allowed w && !seen[w]! then
          seen := seen.set! w true
          queue := queue.push w
  return seen

def connected (g : Graph) (active : Nat → Bool) : Bool := Id.run do
  let mut start := g.size
  for v in [:g.size] do
    if active v then start := v
  if start == g.size then return false
  let seen := reachable g start active
  return (Array.range g.size).all (fun v => !active v || seen[v]!)

abbrev Edge := Nat × Nat
abbrev Occurrence := Nat × Bool

def edgeKey (u v : Nat) : Edge := (min u v, max u v)

structure Model where
  faces : Array Face
  edges : Std.HashMap Edge (Array Occurrence)
  graph : Graph
  dual : Graph
  curves : Array Graph
  oriented : Array Face
  links : Array (Std.HashMap Nat Nat)
  orientationConsistent : Bool
  linksUnambiguous : Bool

def makeModel (faces : Array Face) : Model := Id.run do
  let mut edges : Std.HashMap Edge (Array Occurrence) := {}
  for f in [:faces.size] do
    for k in [:4] do
      let u := faces[f]![k]!
      let v := faces[f]![(k+1)%4]!
      let key := edgeKey u v
      edges := edges.insert key ((edges.getD key #[]).push (f, u < v))
  let mut graph : Graph := Array.replicate (2^19) #[]
  let mut dual : Graph := Array.replicate faces.size #[]
  let mut constraints : Array (Array (Nat × Bool)) := Array.replicate faces.size #[]
  let mut curves : Array Graph := Array.replicate 19 (Array.replicate faces.size #[])
  for ((u,v), occurrences) in edges.toArray do
    graph := addNeighbor (addNeighbor graph u v) v u
    if occurrences.size == 2 then
      let (f,d) := occurrences[0]!
      let (g,e) := occurrences[1]!
      dual := addNeighbor (addNeighbor dual f g) g f
      constraints := constraints.modify f (·.push (g,d == e))
      constraints := constraints.modify g (·.push (f,d == e))
      for i in [:19] do
        if (u ^^^ v) == 2^i then
          curves := curves.modify i (fun c => addNeighbor (addNeighbor c f g) g f)
  let mut signs : Array (Option Bool) := Array.replicate faces.size none
  let mut consistent := true
  if faces.size > 0 then signs := signs.set! 0 (some false)
  let mut queue := if faces.size > 0 then #[0] else #[]
  for k in [:faces.size] do
    if k < queue.size then
      let f := queue[k]!
      for (g, flip) in constraints[f]! do
        let expected := xor (signs[f]!.getD false) flip
        match signs[g]! with
        | some s => if s != expected then consistent := false
        | none =>
          signs := signs.set! g (some expected)
          queue := queue.push g
  consistent := consistent && signs.all Option.isSome
  let oriented := faces.mapIdx fun i f => if signs[i]!.getD false then f.reverse else f
  let mut links : Array (Std.HashMap Nat Nat) := Array.replicate (2^19) {}
  let mut unambiguous := true
  for f in oriented do
    for k in [:4] do
      let v := f[k]!
      let prev := f[(k+3)%4]!
      let next := f[(k+1)%4]!
      if links[v]!.contains prev then unambiguous := false
      links := links.modify v (fun l => l.insert prev next)
  return ⟨faces, edges, graph, dual, curves, oriented, links, consistent, unambiguous⟩

/-- A link must be one cycle containing all neighbors, with no repeated visit. -/
def singleLink (neighbors : Array Nat) (link : Std.HashMap Nat Nat) : Bool := Id.run do
  if neighbors.isEmpty || link.size != neighbors.size then return false
  let start := neighbors[0]!
  let mut cur := start
  let mut visited : Std.HashSet Nat := {}
  for _ in [:neighbors.size] do
    if visited.contains cur || !neighbors.contains cur then return false
    visited := visited.insert cur
    match link[cur]? with
    | none => return false
    | some next => cur := next
  return cur == start && visited.size == neighbors.size

def rotate (v : Nat) : Nat := v / 2 + (v % 2) * 2^18

/-- Only cyclic shifts are quotiented out, never orientation reversal. -/
def faceKey (f : Face) : Nat := Id.run do
  let mut answer := (2^19)^4
  for k in [:4] do
    let mut code := 0
    for j in [:4] do code := code * 2^19 + f[(k+j)%4]!
    answer := min answer code
  return answer

def rotationPreserved (m : Model) : Bool := Id.run do
  let mut keys : Std.HashSet Nat := {}
  for f in m.oriented do keys := keys.insert (faceKey f)
  if keys.size != m.faces.size then return false
  return m.oriented.all (fun f => keys.contains (faceKey (f.map rotate)))

/-- Identify the generator at both poles, up to reversing the global orientation.
An arbitrary order-19 automorphism alone need not have rotation number ±1/19. -/
def poleRotationOneStep (m : Model) : Bool :=
  let atPole := fun pole step =>
    m.links[pole]!.size == 19 && (Array.range 19).all fun i =>
      m.links[pole]![pole ^^^ 2^i]? == some (pole ^^^ 2^((i+step)%19))
  (atPole 0 1 && atPole (2^19-1) 18) || (atPole 0 18 && atPole (2^19-1) 1)

def allPatterns (m : Model) : Bool := Id.run do
  let mut seen := Array.replicate (2^19) false
  for f in m.faces do
    for v in f do
      if v >= seen.size then return false
      seen := seen.set! v true
  return seen.all id

def curveCycles (m : Model) : Bool :=
  m.curves.all fun g =>
    g.all (fun ns => ns.isEmpty || ns.size == 2) &&
    connected g (fun f => !g[f]!.isEmpty)

def connectedSides (m : Model) : Bool :=
  (Array.range 19).all fun i =>
    (#[false,true]).all fun side =>
      connected m.graph (fun v => ((v / 2^i) % 2 == 1) == side)

structure Report where
  regions : Nat
  arcs : Nat
  crossings : Nat
  squareCrossings : Bool
  twoFacesPerArc : Bool
  connectedMap : Bool
  orientedSurface : Bool
  singleVertexLinks : Bool
  eulerTwo : Bool
  singleCurveCycles : Bool
  connectedCurveSides : Bool
  everyPattern : Bool
  simpleCrossings : Bool
  rotationalSymmetry : Bool
  poleRotationOneStep : Bool
  deriving Repr, BEq, DecidableEq

def Report.Passed (r : Report) : Prop :=
  r.regions = 524288 ∧ r.arcs = 1048572 ∧ r.crossings = 524286 ∧
  r.squareCrossings = true ∧ r.twoFacesPerArc = true ∧
  r.connectedMap = true ∧ r.orientedSurface = true ∧
  r.singleVertexLinks = true ∧ r.eulerTwo = true ∧
  r.singleCurveCycles = true ∧ r.connectedCurveSides = true ∧
  r.everyPattern = true ∧ r.simpleCrossings = true ∧ r.rotationalSymmetry = true ∧
  r.poleRotationOneStep = true

instance (r : Report) : Decidable r.Passed := inferInstanceAs (Decidable (_ ∧ _))

def audit (text : String) : Except String Report := do
  let faces ← parse text
  let m := makeModel faces
  let regions := (m.graph.filter (fun ns => !ns.isEmpty)).size
  let arcs := m.edges.size
  let crossings := m.faces.size
  return {
    regions, arcs, crossings
    squareCrossings := true -- parseFace has already checked this for every face.
    twoFacesPerArc := m.edges.toArray.all (fun (_, fs) => fs.size == 2)
    connectedMap := connected m.graph (fun ns => !m.graph[ns]!.isEmpty) &&
      connected m.dual (fun _ => true)
    orientedSurface := m.orientationConsistent
    singleVertexLinks := m.linksUnambiguous && (Array.range m.graph.size).all
      (fun v => m.graph[v]!.isEmpty || singleLink m.graph[v]! m.links[v]!)
    eulerTwo := regions + crossings == arcs + 2
    singleCurveCycles := curveCycles m
    connectedCurveSides := connectedSides m
    everyPattern := allPatterns m
    simpleCrossings := true -- Four distinct bit-square corners and two distinct labels.
    rotationalSymmetry := rotationPreserved m
    poleRotationOneStep := Venn19.poleRotationOneStep m
  }

def accepts (text : String) : Bool :=
  match audit text with
  | .error _ => false
  | .ok report => decide report.Passed

/-- Soundness of the public Boolean API relative to the explicit report contract. -/
theorem accepts_iff (text : String) :
    accepts text = true ↔ ∃ r, audit text = .ok r ∧ r.Passed := by
  unfold accepts
  cases h : audit text with
  | error e => simp
  | ok r => simp

end Venn19
