import VennTopology.CrossingSquare
import VennTopology.ArmSymmetry

noncomputable section
namespace Venn17.Topology.Quad
open Set
open scoped Classical
variable {V F : Type*} (q : Quad V F)
local instance centerChartDecidableEq : DecidableEq (V ⊕ F) := Classical.decEq _

def centerStar (f : F) : Set q.Realization := {x | 0 < x.val (.inr f)}
def cornerWeights (f : F) (x : Ambient V F) : Fin 4 → ℝ := fun k => x (.inl (q.corner f k))

theorem centerStar_triangle (f : F) (x : q.centerStar f) :
    ∃ k, x.val.val ∈ q.triangle f k := by
  obtain ⟨g,k,hx⟩ := mem_iUnion₂.mp x.val.property
  have ht : x.val.val ∈ Coordinates.simplex (q.cellLabels (g,k)) := by
    rwa [← q.triangle_eq_simplex]
  have hm := Coordinates.positive_coordinate_in_cell q.cellLabels ht x.property
  have he : f = g := by simpa [cellLabels] using hm
  subst g
  exact ⟨k,hx⟩

theorem triangle_corner_zero (f : F) (hc : Function.Injective (q.corner f))
    {x : Ambient V F} {k j : Fin 4} (hx : x ∈ q.triangle f k)
    (hjk : j ≠ k) (hjn : j ≠ next k) : q.cornerWeights f x j = 0 := by
  apply Coordinates.simplex_zero (s := q.cellLabels (f,k))
  · rwa [← q.triangle_eq_simplex]
  · simp [cellLabels,hc.eq_iff,hjk,hjn]

theorem triangle_corner_sum (f : F) (hc : Function.Injective (q.corner f))
    {x : Ambient V F} {k : Fin 4} (hx : x ∈ q.triangle f k) :
    x (.inr f) + q.cornerWeights f x k + q.cornerWeights f x (next k) = 1 := by
  change x (.inr f) + x (.inl (q.corner f k)) + x (.inl (q.corner f (next k))) = 1
  apply Coordinates.triangle_sum (x := x) (c := .inr f) (u := .inl (q.corner f k))
    (v := .inl (q.corner f (next k))) (by simp) (by simp)
    (by simpa [hc.eq_iff] using (next_ne k).symm)
  simpa only [cellLabels] using (q.triangle_eq_simplex f k ▸ hx)

theorem centerStar_weights (f : F) (hc : Function.Injective (q.corner f)) (x : q.centerStar f) :
    (∀ k, 0 ≤ q.cornerWeights f x.val.val k) ∧
    (q.cornerWeights f x.val.val 0 = 0 ∨ q.cornerWeights f x.val.val 2 = 0) ∧
    (q.cornerWeights f x.val.val 1 = 0 ∨ q.cornerWeights f x.val.val 3 = 0) ∧
    q.cornerWeights f x.val.val 0 + q.cornerWeights f x.val.val 1 +
      q.cornerWeights f x.val.val 2 + q.cornerWeights f x.val.val 3 < 1 := by
  obtain ⟨k,hk⟩ := q.centerStar_triangle f x
  refine ⟨?_,?_⟩
  · intro j
    exact Coordinates.simplex_nonneg (q.triangle_eq_simplex f k ▸ hk) (.inl (q.corner f j))
  have hs := q.triangle_corner_sum f hc hk
  have hz (j : Fin 4) := q.triangle_corner_zero f hc (j := j) hk
  have hp : 0 < x.val.val (.inr f) := x.property
  fin_cases k
  all_goals
    dsimp [next] at hs hz
    have h0 := hz (j := 0)
    have h1 := hz (j := 1)
    have h2 := hz (j := 2)
    have h3 := hz (j := 3)
    norm_num [Fin.ext_iff] at h0 h1 h2 h3
    simp_all only [or_true,true_or,true_and]
    linarith

def liftWeights (f : F) (a : Fin 4 → ℝ) : Ambient V F :=
  (1-(a 0+a 1+a 2+a 3)) • point (.inr f) + ∑ k : Fin 4, a k • point (.inl (q.corner f k))

theorem liftWeights_center (f : F) (a : Fin 4 → ℝ) :
    q.liftWeights f a (.inr f) = 1-(a 0+a 1+a 2+a 3) := by
  simp [liftWeights,point,Finset.sum_apply]

theorem liftWeights_corner (f : F) (hc : Function.Injective (q.corner f)) (a : Fin 4 → ℝ) (j : Fin 4) :
    q.cornerWeights f (q.liftWeights f a) j = a j := by
  simp [cornerWeights,liftWeights,point,Finset.sum_apply,hc.eq_iff]

theorem triangle_combination (f : F) (k : Fin 4) (r s t : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (h : r+s+t = 1) :
    r • point (.inr f) + s • point (.inl (q.corner f k)) +
      t • point (.inl (q.corner f (next k))) ∈ q.triangle f k := by
  have H := (convex_convexHull ℝ (q.triangleVertices f k)).sum_mem
    (t := Finset.univ) (w := ![r,s,t])
    (z := ![point (.inr f),point (.inl (q.corner f k)),point (.inl (q.corner f (next k)))])
    (by intro i _; fin_cases i <;> assumption)
    (by simpa [Fin.sum_univ_succ,add_assoc] using h)
    (by intro i _; fin_cases i
        exact q.center_mem_triangle f k
        exact q.corner_mem_triangle f k
        exact q.next_corner_mem_triangle f k)
  simpa [triangle,Fin.sum_univ_succ,add_assoc] using H

theorem liftWeights_mem (f : F) (a : CrossingSquare.Weights) :
    q.liftWeights f a.val ∈ q.space := by
  have hr : 0 ≤ 1-(a.val 0+a.val 1+a.val 2+a.val 3) := by linarith [a.property.2.2.2]
  have H (k : Fin 4) := q.triangle_combination f k
    (1-(a.val 0+a.val 1+a.val 2+a.val 3)) (a.val k) (a.val (next k))
    hr (a.property.1 k) (a.property.1 (next k))
  rcases a.property.2.1 with h02 | h02 <;> rcases a.property.2.2.1 with h13 | h13
  · apply q.triangle_subset_space f 2
    simpa [liftWeights,Fin.sum_univ_succ,next,h02,h13,add_assoc] using H 2 (by dsimp [next]; rw [h02,h13]; ring)
  · apply q.triangle_subset_space f 1
    simpa [liftWeights,Fin.sum_univ_succ,next,h02,h13,add_assoc] using H 1 (by dsimp [next]; rw [h02,h13]; ring)
  · apply q.triangle_subset_space f 3
    simpa [liftWeights,Fin.sum_univ_succ,next,h02,h13,add_assoc,add_comm,add_left_comm] using H 3 (by dsimp [next]; rw [h02,h13]; ring)
  · apply q.triangle_subset_space f 0
    simpa [liftWeights,Fin.sum_univ_succ,next,h02,h13,add_assoc] using H 0 (by dsimp [next]; rw [h02,h13]; ring)

theorem sum_pair_support {M : Type*} [AddCommMonoid M] (a : Fin 4 → M) (k : Fin 4)
    (hz : ∀ j, j ≠ k → j ≠ next k → a j = 0) :
    (∑ j : Fin 4, a j) = a k + a (next k) := by
  have he := Finset.sum_subset (s₁ := {k,next k}) (s₂ := Finset.univ)
    (f := a) (by intro j _; simp) (by
      intro j _ hj
      have h : j ≠ k ∧ j ≠ next k := by simpa using hj
      exact hz j h.1 h.2)
  simpa [next_ne,(next_ne k).symm] using he.symm

theorem liftWeights_reconstruct (f : F) (hc : Function.Injective (q.corner f))
    (x : q.centerStar f) : q.liftWeights f (q.cornerWeights f x.val.val) = x.val.val := by
  obtain ⟨k,hk⟩ := q.centerStar_triangle f x
  have hs := q.triangle_corner_sum f hc hk
  have hz (j : Fin 4) := q.triangle_corner_zero f hc (j := j) hk
  have hsum := sum_pair_support (q.cornerWeights f x.val.val) k hz
  have he : 1-(q.cornerWeights f x.val.val 0+q.cornerWeights f x.val.val 1+
      q.cornerWeights f x.val.val 2+q.cornerWeights f x.val.val 3) = x.val.val (.inr f) := by
    simp [Fin.sum_univ_succ] at hsum
    linarith
  have hvec := sum_pair_support (M := Ambient V F) (fun j => q.cornerWeights f x.val.val j • point (.inl (q.corner f j))) k
    (by intro j hj hn; rw [hz j hj hn,zero_smul])
  rw [liftWeights,he,hvec]
  have hr := Coordinates.simplex_reconstruct (q.triangle_eq_simplex f k ▸ hk)
  have hne : q.corner f k ≠ q.corner f (next k) := fun h => (next_ne k) (hc h).symm
  simpa [cellLabels,coordinates_vertex_eq,hne,cornerWeights,add_assoc] using hr

def centerWeightsHomeomorph (f : F) (hc : Function.Injective (q.corner f)) :
    q.centerStar f ≃ₜ CrossingSquare.Weights where
  toFun x := ⟨q.cornerWeights f x.val.val,q.centerStar_weights f hc x⟩
  invFun a := ⟨⟨q.liftWeights f a.val,q.liftWeights_mem f a⟩,by
    change 0 < q.liftWeights f a.val (.inr f)
    rw [liftWeights_center]; linarith [a.property.2.2.2]⟩
  left_inv x := Subtype.ext (Subtype.ext (q.liftWeights_reconstruct f hc x))
  right_inv a := Subtype.ext (funext (q.liftWeights_corner f hc a.val))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    exact (continuous_apply (Sum.inl (q.corner f k) : V ⊕ F)).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have h : Continuous (q.liftWeights f) := by unfold liftWeights; fun_prop
    exact h.comp continuous_subtype_val

/-- The complete center star, including its central crossing point, has an
explicit square chart. -/
def centerSquareChart (f : F) (hc : Function.Injective (q.corner f)) :
    q.centerStar f ≃ₜ CrossingSquare.square :=
  (q.centerWeightsHomeomorph f hc).trans CrossingSquare.homeomorph

theorem centerSquareChart_center (f : F) (hc : Function.Injective (q.corner f))
    (x : q.centerStar f) (hx : x.val.val = point (.inr f)) :
    (q.centerSquareChart f hc x).val = (0,0) := by
  change CrossingSquare.flatten (q.cornerWeights f x.val.val) = (0,0)
  rw [hx]
  simp [CrossingSquare.flatten,cornerWeights,point]

#print axioms centerSquareChart
end Venn17.Topology.Quad
