import Std

namespace Venn17.GraphProof

abbrev Graph := Array (Array Nat)

/-- A finite walk along actual adjacency-list entries, entirely within the
active set. Restricting the walk is essential for the curve-side statements. -/
inductive Walk (g : Graph) (active : Nat → Bool) : Nat → Nat → Prop where
  | refl (v : Nat) : active v = true → Walk g active v v
  | step {u v w : Nat} : active u = true → v ∈ g[u]! →
      Walk g active v w → Walk g active u w

/-- Every active vertex has an actual walk to one active root. -/
def ConnectedOn (g : Graph) (active : Nat → Bool) : Prop :=
  ∃ root, root < g.size ∧ active root = true ∧
    ∀ v, v < g.size → active v = true → Walk g active v root

structure Tree where
  root : Nat
  parent : Array Nat
  rank : Array Nat

/-- Propose a spanning tree. Correctness is verified separately below. -/
def proposeTree (g : Graph) (active : Nat → Bool) : Tree := Id.run do
  let mut root := g.size
  for v in [:g.size] do
    if active v then root := v
  let mut parent := Array.replicate g.size g.size
  let mut rank := Array.replicate g.size 0
  if root == g.size then return ⟨root, parent, rank⟩
  rank := rank.set! root 1
  let mut queue := #[root]
  for k in [:g.size] do
    if k < queue.size then
      let v := queue[k]!
      for w in g[v]! do
        if w < g.size && active w && rank[w]! == 0 then
          parent := parent.set! w v
          rank := rank.set! w (rank[v]! + 1)
          queue := queue.push w
  return ⟨root, parent, rank⟩

def treeCheck (g : Graph) (active : Nat → Bool) (t : Tree) : Bool :=
  t.root < g.size && active t.root &&
    (Array.range g.size).all fun v =>
      !active v || v == t.root ||
        (t.parent[v]! < g.size && active t.parent[v]! &&
         g[v]!.contains t.parent[v]! && t.rank[t.parent[v]!]! < t.rank[v]!)

/-- Kernel-checked soundness: decreasing ranks give finite paths to the root.
No assumption is made about how the proposed tree was produced. -/
theorem treeCheck_sound (g : Graph) (active : Nat → Bool) (t : Tree)
    (h : treeCheck g active t = true) : ConnectedOn g active := by
  simp only [treeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨t.root, h.1.1, h.1.2, ?_⟩
  have localStep (v : Nat) (hv : v < g.size) (ha : active v = true) :
      v = t.root ∨ (t.parent[v]! < g.size ∧ active t.parent[v]! = true ∧
        t.parent[v]! ∈ g[v]! ∧ t.rank[t.parent[v]!]! < t.rank[v]!) := by
    have step := Array.all_eq_true.mp h.2 v (by simpa using hv)
    simpa only [Array.getElem_range, ha, Bool.not_true, Bool.false_or,
      Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, Array.contains_iff_mem, and_assoc] using step
  have reach : ∀ rank v, t.rank[v]! = rank → v < g.size → active v = true →
      Walk g active v t.root := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
      intro v hr hv ha
      rcases localStep v hv ha with eq | ⟨hp, hap, hedge, hlt⟩
      · subst v
        exact Walk.refl _ ha
      · exact Walk.step ha hedge (ih _ (hr ▸ hlt) _ rfl hp hap)
  intro v hv ha
  exact reach _ v rfl hv ha

def connectedCheck (g : Graph) (active : Nat → Bool) : Bool :=
  treeCheck g active (proposeTree g active)

theorem connectedCheck_sound (g : Graph) (active : Nat → Bool)
    (h : connectedCheck g active = true) : ConnectedOn g active :=
  treeCheck_sound g active _ h

theorem degree_two (g : Graph) (f : Nat) (hf : f < g.size)
    (ha : (!g[f]!.isEmpty) = true)
    (h : g.all (fun ns => ns.isEmpty || ns.size == 2) = true) :
    g[f]!.size = 2 := by
  have hv := Array.all_eq_true.mp h f hf
  have he : g[f]! = g[f] := by simp [hf]
  rw [he] at ha ⊢
  simp_all

#print axioms treeCheck_sound

end Venn17.GraphProof
