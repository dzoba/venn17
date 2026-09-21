import VennTopology.CenterChart

noncomputable section
namespace Venn19.Topology
open Set

namespace CrossingSquare

def armWeights (k : Fin 4) (a : Fin 4 → ℝ) : Prop :=
  a k = a (Quad.next k) ∧ ∀ j, j ≠ k → j ≠ Quad.next k → a j = 0

theorem armWeights_even_iff (a : Weights) :
    (∃ k : Fin 4, k.val%2 = 0 ∧ armWeights k a.val) ↔ (flatten a.val).1 = 0 := by
  constructor
  · rintro ⟨k,hk,he,hz⟩
    fin_cases k <;> norm_num at hk
    all_goals
      have h0 := hz 0
      have h1 := hz 1
      have h2 := hz 2
      have h3 := hz 3
      norm_num [Quad.next,Fin.ext_iff] at he h0 h1 h2 h3
      dsimp [flatten]
      try simp only [Fin.reduceFinMk] at he
      linarith
  · intro h
    have h0 := a.property.1 0
    have h1 := a.property.1 1
    have h2 := a.property.1 2
    have h3 := a.property.1 3
    dsimp [flatten] at h
    rcases a.property.2.1 with h02 | h02 <;> rcases a.property.2.2.1 with h13 | h13
    · refine ⟨2,rfl,?_,?_⟩
      · dsimp [Quad.next]; linarith
      · intro j hj hn; fin_cases j <;> norm_num [Quad.next,Fin.ext_iff] at * <;> assumption
    · have hz0 : a.val 0 = 0 := h02
      have hz1 : a.val 1 = 0 := by linarith
      have hz2 : a.val 2 = 0 := by linarith
      refine ⟨0,rfl,by dsimp [Quad.next]; linarith,?_⟩
      intro j hj hn; fin_cases j <;> norm_num [Quad.next,Fin.ext_iff] at * <;> assumption
    · have hz0 : a.val 0 = 0 := by linarith
      have hz3 : a.val 3 = 0 := by linarith
      refine ⟨0,rfl,by dsimp [Quad.next]; linarith,?_⟩
      intro j hj hn; fin_cases j <;> norm_num [Quad.next,Fin.ext_iff] at * <;> assumption
    · refine ⟨0,rfl,by dsimp [Quad.next]; linarith,?_⟩
      intro j hj hn; fin_cases j <;> norm_num [Quad.next,Fin.ext_iff] at * <;> assumption

theorem armWeights_odd_iff (a : Weights) :
    (∃ k : Fin 4, k.val%2 = 1 ∧ armWeights k a.val) ↔ (flatten a.val).2 = 0 := by
  constructor
  · rintro ⟨k,hk,he,hz⟩
    fin_cases k <;> norm_num at hk
    all_goals
      have h0 := hz 0
      have h1 := hz 1
      have h2 := hz 2
      have h3 := hz 3
      norm_num [Quad.next,Fin.ext_iff] at he h0 h1 h2 h3
      dsimp [flatten]
      try simp only [Fin.reduceFinMk] at he
      linarith
  · intro h
    have h0 := a.property.1 0
    have h1 := a.property.1 1
    have h2 := a.property.1 2
    have h3 := a.property.1 3
    dsimp [flatten] at h
    rcases a.property.2.1 with h02 | h02 <;> rcases a.property.2.2.1 with h13 | h13
    · have hz2 : a.val 2 = 0 := by linarith
      have hz3 : a.val 3 = 0 := by linarith
      refine ⟨1,rfl,by dsimp [Quad.next]; linarith,?_⟩
      intro j hj hn; fin_cases j <;> norm_num [Quad.next,Fin.ext_iff] at * <;> assumption
    · refine ⟨1,rfl,by dsimp [Quad.next]; linarith,?_⟩
      intro j hj hn; fin_cases j <;> norm_num [Quad.next,Fin.ext_iff] at * <;> assumption
    · refine ⟨3,rfl,by dsimp [Quad.next]; linarith,?_⟩
      intro j hj hn; fin_cases j <;> norm_num [Quad.next,Fin.ext_iff] at * <;> assumption
    · have hz0 : a.val 0 = 0 := by linarith
      have hz1 : a.val 1 = 0 := by linarith
      refine ⟨1,rfl,by dsimp [Quad.next]; linarith,?_⟩
      intro j hj hn; fin_cases j <;> norm_num [Quad.next,Fin.ext_iff] at * <;> assumption

end CrossingSquare
namespace Quad
variable {V F : Type*} (q : Quad V F)

theorem arm_weight_conditions (f : F) (hc : Function.Injective (q.corner f)) (k : Fin 4)
    {x : Ambient V F} (hx : x ∈ q.arm f k) : CrossingSquare.armWeights k (q.cornerWeights f x) := by
  rw [arm,segment_eq_image_lineMap] at hx
  obtain ⟨r,_,rfl⟩ := hx
  constructor
  · simp [cornerWeights,AffineMap.lineMap_apply_module,point,hc.eq_iff,next_ne,(next_ne k).symm]
  · intro j hj hn
    simp [cornerWeights,AffineMap.lineMap_apply_module,point,hc.eq_iff,hj,hn]

theorem centerStar_arm_iff (f : F) (hc : Function.Injective (q.corner f))
    (x : q.centerStar f) (k : Fin 4) :
    x.val.val ∈ q.arm f k ↔ CrossingSquare.armWeights k (q.cornerWeights f x.val.val) := by
  constructor
  · exact q.arm_weight_conditions f hc k
  · rintro ⟨he,hz⟩
    let a := q.cornerWeights f x.val.val
    have ha := q.centerStar_weights f hc x
    have hr : 0 ≤ 1-(a 0+a 1+a 2+a 3) := by dsimp [a]; linarith [ha.2.2.2]
    have hs : 0 ≤ a k + a (next k) := add_nonneg (ha.1 k) (ha.1 (next k))
    have heq := q.liftWeights_reconstruct f hc x
    rw [← heq]
    change ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ r+s = 1 ∧
      r • point (.inr f) + s • ((1/2 : ℝ) • (point (.inl (q.corner f k)) +
        point (.inl (q.corner f (next k))))) = q.liftWeights f a
    have hz' : ∀ j, j ≠ k → j ≠ next k → a j = 0 := hz
    have hsum := sum_pair_support a k hz'
    have hvec := sum_pair_support (M := Ambient V F)
      (fun j => a j • point (.inl (q.corner f j))) k
      (by intro j hj hn; rw [hz' j hj hn,zero_smul])
    refine ⟨1-(a 0+a 1+a 2+a 3),a k+a (next k),hr,hs,?_,?_⟩
    · simp [Fin.sum_univ_succ] at hsum
      linarith
    · rw [liftWeights,hvec]
      change a k = a (next k) at he
      rw [he]
      module

theorem centerSquareChart_even_axis (f : F) (hc : Function.Injective (q.corner f))
    (x : q.centerStar f) :
    (∃ k : Fin 4, k.val%2 = 0 ∧ x.val.val ∈ q.arm f k) ↔
      ((q.centerSquareChart f hc x).val).1 = 0 := by
  simp_rw [q.centerStar_arm_iff f hc x]
  exact CrossingSquare.armWeights_even_iff (q.centerWeightsHomeomorph f hc x)

theorem centerSquareChart_odd_axis (f : F) (hc : Function.Injective (q.corner f))
    (x : q.centerStar f) :
    (∃ k : Fin 4, k.val%2 = 1 ∧ x.val.val ∈ q.arm f k) ↔
      ((q.centerSquareChart f hc x).val).2 = 0 := by
  simp_rw [q.centerStar_arm_iff f hc x]
  exact CrossingSquare.armWeights_odd_iff (q.centerWeightsHomeomorph f hc x)

#print axioms centerSquareChart_even_axis
end Quad
end Venn19.Topology
