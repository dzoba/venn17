import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Homeomorph.Lemmas
import VennCore.Connectivity

/-! An explicit geometric realization. This file does not identify it with a sphere. -/
noncomputable section

namespace Venn17.Topology

open Set

structure Quad (V F : Type*) where
  corner : F → Fin 4 → V

namespace Quad

variable {V F : Type*}

abbrev Ambient (V F : Type*) := (V ⊕ F) → ℝ

def point (a : V ⊕ F) : Ambient V F := by
  classical
  exact fun b => if b = a then 1 else 0

theorem point_injective : Function.Injective (point (V := V) (F := F)) := by
  classical
  intro a b h
  have h' := congrFun h a
  by_contra hab
  simp [point, hab] at h'

def next (k : Fin 4) : Fin 4 := ⟨(k.val + 1) % 4, Nat.mod_lt _ (by decide)⟩

def triangleVertices (q : Quad V F) (f : F) (k : Fin 4) : Set (Ambient V F) :=
  {point (.inr f), point (.inl (q.corner f k)), point (.inl (q.corner f (next k)))}

def triangle (q : Quad V F) (f : F) (k : Fin 4) : Set (Ambient V F) :=
  convexHull ℝ (q.triangleVertices f k)

def space (q : Quad V F) : Set (Ambient V F) := ⋃ f, ⋃ k, q.triangle f k

abbrev Realization (q : Quad V F) := q.space

theorem triangle_subset_space (q : Quad V F) (f : F) (k : Fin 4) :
    q.triangle f k ⊆ q.space := by
  intro x hx
  exact mem_iUnion.mpr ⟨f, mem_iUnion.mpr ⟨k, hx⟩⟩

theorem center_mem_triangle (q : Quad V F) (f : F) (k : Fin 4) :
    point (.inr f) ∈ q.triangle f k :=
  subset_convexHull ℝ _ (by simp [triangleVertices])

theorem corner_mem_triangle (q : Quad V F) (f : F) (k : Fin 4) :
    point (.inl (q.corner f k)) ∈ q.triangle f k :=
  subset_convexHull ℝ _ (by simp [triangleVertices])

theorem next_corner_mem_triangle (q : Quad V F) (f : F) (k : Fin 4) :
    point (.inl (q.corner f (next k))) ∈ q.triangle f k :=
  subset_convexHull ℝ _ (by simp [triangleVertices])

theorem triangle_compact (q : Quad V F) (f : F) (k : Fin 4) :
    IsCompact (q.triangle f k) := by
  apply Set.Finite.isCompact_convexHull
  simp [triangleVertices]

theorem space_compact [Finite F] (q : Quad V F) : IsCompact q.space :=
  isCompact_iUnion fun f => isCompact_iUnion fun k => q.triangle_compact f k

instance [Finite F] (q : Quad V F) : CompactSpace q.Realization :=
  isCompact_iff_compactSpace.mp q.space_compact

instance (q : Quad V F) : T2Space q.Realization := inferInstance

theorem triangle_pathConnected (q : Quad V F) (f : F) (k : Fin 4) :
    IsPathConnected (q.triangle f k) :=
  (convex_convexHull ℝ _).isPathConnected ⟨_, q.center_mem_triangle f k⟩

theorem adjacent_joined (q : Quad V F) (f : F) (k : Fin 4) :
    JoinedIn q.space (point (.inl (q.corner f k)))
      (point (.inl (q.corner f (next k)))) :=
  ((q.triangle_pathConnected f k).joinedIn _ (q.corner_mem_triangle f k)
    _ (q.next_corner_mem_triangle f k)).mono (q.triangle_subset_space f k)

theorem point_joined_corner (q : Quad V F) {x : Ambient V F} (hx : x ∈ q.space) :
    ∃ f, JoinedIn q.space x (point (.inl (q.corner f 0))) := by
  obtain ⟨f, k, hx⟩ := mem_iUnion.mp hx |>.imp (fun f => mem_iUnion.mp)
  refine ⟨f, ?_⟩
  have h₁ := ((q.triangle_pathConnected f k).joinedIn _ hx
    _ (q.center_mem_triangle f k)).mono (q.triangle_subset_space f k)
  have h₂ := ((q.triangle_pathConnected f 0).joinedIn _ (q.center_mem_triangle f 0)
    _ (q.corner_mem_triangle f 0)).mono (q.triangle_subset_space f 0)
  exact h₁.trans h₂

end Quad

/-- Lift finite adjacency walks to actual continuous paths. -/
theorem walk_joined {X : Type*} [TopologicalSpace X] (s : Set X)
    (g : GraphProof.Graph) (active : Nat → Bool) (anchor : Nat → X)
    (hvertex : ∀ v, active v = true → anchor v ∈ s)
    (hedge : ∀ u v, active u = true → v ∈ g[u]! → JoinedIn s (anchor u) (anchor v))
    {u v : Nat} (h : GraphProof.Walk g active u v) : JoinedIn s (anchor u) (anchor v) := by
  induction h with
  | refl v hv => exact JoinedIn.refl (hvertex v hv)
  | step hu he _ ih => exact (hedge _ _ hu he).trans ih

end Venn17.Topology
