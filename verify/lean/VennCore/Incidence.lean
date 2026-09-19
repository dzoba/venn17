import VennCore.Checker
import VennCore.Connectivity

namespace Venn17

def cornerDarts (fs : Array Face) (n : Nat) : Array Nat := Id.run do
  let mut out := Array.replicate n (4*fs.size)
  for f in [:fs.size] do
    for k in [:4] do out := out.set! fs[f]![k]! (4*f+k)
  return out

def directedDarts (fs : Array Face) : Std.HashMap (Nat × Nat) Nat := Id.run do
  let mut out : Std.HashMap (Nat × Nat) Nat := {}
  for f in [:fs.size] do
    for k in [:4] do
      out := out.insert (fs[f]![k]!, fs[f]![(k+1)%4]!) (4*f+k)
  return out

def dartTail (fs : Array Face) (d : Nat) : Nat := fs[d/4]![d%4]!
def dartHead (fs : Array Face) (d : Nat) : Nat := fs[d/4]![(d%4+1)%4]!

def cornersCheck (fs : Array Face) (n : Nat) : Bool :=
  fs.all (fun f => f.size == 4 && f.all (fun v => v < n))

def distinctCornersCheck (fs : Array Face) : Bool :=
  fs.all fun f => (Array.range 4).all fun k => (Array.range 4).all fun l =>
    k == l || f[k]! != f[l]!

def coverageCheck (fs : Array Face) (n : Nat) : Bool :=
  let witnesses := cornerDarts fs n
  (Array.range n).all fun v =>
    let d := witnesses[v]!
    d/4 < fs.size && dartTail fs d == v

def edgesCheck (fs : Array Face) (g : Graph) : Bool :=
  let witnesses := directedDarts fs
  (Array.range g.size).all fun u =>
    g[u]!.all fun v =>
      let d := witnesses.getD (u,v) (4*fs.size)
      d/4 < fs.size && dartTail fs d == u && dartHead fs d == v

/-- Unlike a report flag, these certificates exhibit the triangles containing
each region vertex and each graph edge. -/
def incidenceCheck (fs : Array Face) (g : Graph) : Bool :=
  cornersCheck fs g.size && coverageCheck fs g.size && edgesCheck fs g &&
    GraphProof.connectedCheck g (fun v => v < g.size)

end Venn17
