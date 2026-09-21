import VennTopology.Stars
import Mathlib.Topology.Algebra.Module.Equiv

noncomputable section
namespace Venn19.Topology.Coordinates
open Set
open scoped Classical
variable {I J T : Type*}
local instance {α : Type*} : DecidableEq α := Classical.decEq _

def reindex (e : I ≃ J) : Point I ≃ₜ Point J := Homeomorph.piCongrLeft (Y := fun _ : J => ℝ) e

@[simp] theorem reindex_apply (e : I ≃ J) (x : Point I) (j : J) :
    reindex e x j = x (e.symm j) := by
  obtain ⟨i, rfl⟩ := e.surjective j
  simp [reindex, Homeomorph.piCongrLeft_apply_apply]

@[simp] theorem reindex_vertex (e : I ≃ J) (i : I) : reindex e (vertex i) = vertex (e i) := by
  ext j
  simp [vertex, reindex_apply, e.symm_apply_eq]

theorem reindex_simplex (e : I ≃ J) (s : Finset I) :
    reindex e '' simplex s = simplex (s.map e.toEmbedding) := by
  let f : Point I →ₗ[ℝ] Point J := (LinearEquiv.piCongrLeft ℝ (fun _ : J => ℝ) e).toLinearMap
  have he : (reindex e : Point I → Point J) = f := rfl
  rw [simplex, he, f.image_convexHull]
  unfold simplex
  congr 1
  rw [← image_comp]
  have hf : (f : Point I → Point J) ∘ vertex = vertex ∘ e := by
    funext i
    exact reindex_vertex e i
  rw [hf, image_comp]
  simp

theorem reindex_link (e : I ≃ J) (cells : T → Finset I) (a : I) :
    reindex e '' link cells a = link (fun t => (cells t).map e.toEmbedding) (e a) := by
  simp only [link, image_iUnion, reindex_simplex]
  congr 1
  funext t
  have hmem : e a ∈ (cells t).map e.toEmbedding ↔ a ∈ cells t := by simp
  by_cases ha : a ∈ cells t
  · simp only [ha, hmem.mpr ha, iUnion_true]
    congr 1
    ext j
    simp
  · simp only [ha, hmem.not.mpr ha, iUnion_false]

/-- Natural-number encoding agrees with region labels below `n` and places
face centers immediately after them. Unused region coordinates are shifted. -/
def labelEquiv (n F : Nat) : (Nat ⊕ Fin F) ≃ Nat where
  toFun a := match a with
    | .inl v => if v < n then v else v+F
    | .inr f => n+f.val
  invFun v := if h : v < n then .inl v else
    if h' : v < n+F then .inr ⟨v-n, by omega⟩ else .inl (v-F)
  left_inv := by
    intro a
    cases a with
    | inl v =>
      dsimp
      split_ifs <;> simp_all <;> omega
    | inr f =>
      dsimp
      simp only [show ¬n+f.val < n by omega, ↓reduceDIte,
        show n+f.val < n+F by omega]
      congr 1
      apply Fin.ext
      simp
  right_inv := by
    intro v
    by_cases h : v < n
    · simp [h]
    · by_cases h' : v < n+F
      · simp [h, h', Nat.add_sub_of_le (by omega : n ≤ v)]
      · have h'' : ¬v-F < n := by omega
        simp [h, h', h'']
        omega

@[simp] theorem labelEquiv_region (n F v : Nat) (hv : v < n) :
    labelEquiv n F (.inl v) = v := by simp [labelEquiv, hv]

@[simp] theorem labelEquiv_face (n F : Nat) (f : Fin F) :
    labelEquiv n F (.inr f) = n+f.val := rfl

#print axioms reindex_link
end Venn19.Topology.Coordinates
