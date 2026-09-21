import VennTopology.RigidSectorCover

/-! Distinct rigid sectors meet only along their specified meridian boundaries. -/
noncomputable section
namespace Venn19.Topology
open Set Coordinates LeanEval.Topology.ClassificationOfSurfaces

theorem sine_sector_interval {a δ : ℝ} (hδ : 0 < δ)
    (ha : a < 2 * Real.pi) (hs : 0 ≤ Real.sin a) (ht : Real.sin (a-δ) ≤ 0) :
    (0 ≤ a ∧ a ≤ δ) ∨ a ≤ -2 * Real.pi + δ := by
  by_cases h0 : 0 ≤ a
  · left
    refine ⟨h0, ?_⟩
    have hπ : a ≤ Real.pi := by
      by_contra h
      have hn := Real.sin_neg_of_neg_of_neg_pi_lt (x := a-2*Real.pi)
        (by linarith) (by linarith)
      rw [Real.sin_sub_two_pi] at hn
      linarith
    by_contra h
    have hp := Real.sin_pos_of_pos_of_lt_pi (x := a-δ) (by linarith) (by linarith)
    linarith
  · right
    have hπ : a ≤ -Real.pi := by
      by_contra h
      have hn := Real.sin_neg_of_neg_of_neg_pi_lt (x := a) (by linarith) (by linarith)
      linarith
    by_contra h
    have hp := Real.sin_pos_of_pos_of_lt_pi (x := a-δ+2*Real.pi)
      (by linarith) (by linarith)
    rw [Real.sin_add_two_pi] at hp
    linarith

theorem rigid_sector_angle_bounds (k : Fin 19) {θ : ℝ} (hθ : θ ∈ Ico 0 (2 * Real.pi))
    (hd : 0 ≤ planarCross (rigidDirection k) (Circle.exp θ))
    (he : planarCross (rigidDirection (cyclicNext k)) (Circle.exp θ) ≤ 0) :
    ((k.val : ℝ) * (2 * Real.pi / 19) ≤ θ ∧
      θ ≤ ((k.val : ℝ)+1) * (2 * Real.pi / 19)) ∨ (θ = 0 ∧ k.val = 18) := by
  rw [rigidDirection_angle, planarCross_exp] at hd
  rw [rigidDirection_next_angle, planarCross_exp] at he
  have hδ : 0 < 2 * Real.pi / 19 := by positivity
  have hk0 : 0 ≤ (k.val : ℝ) := Nat.cast_nonneg _
  have hk18 : (k.val : ℝ) ≤ 18 := by exact_mod_cast (show k.val ≤ 18 by omega)
  have ht : Real.sin ((θ-(k.val : ℝ)*(2*Real.pi/19))-(2*Real.pi/19)) ≤ 0 := by
    convert he using 2; ring
  obtain h | h := sine_sector_interval hδ
    (a := θ-(k.val : ℝ)*(2*Real.pi/19))
    (by nlinarith [hθ.2]) hd ht
  · left
    constructor <;> nlinarith
  · right
    have hzero : θ = 0 := by nlinarith [hθ.1]
    refine ⟨hzero, ?_⟩
    have heq : (k.val : ℝ) = 18 := by nlinarith [hθ.1]
    exact_mod_cast heq

theorem rigidSector_polar_bounds (k : Fin 19) (x : SphereRepresentative)
    (hx : x ∈ rigidSector k) (r θ : ℝ) (hr : 0 < r)
    (hθ : θ ∈ Ico 0 (2 * Real.pi))
    (hp : horizontal x.val = (r : ℂ) * Circle.exp θ) :
    ((k.val : ℝ) * (2 * Real.pi / 19) ≤ θ ∧
      θ ≤ ((k.val : ℝ)+1) * (2 * Real.pi / 19)) ∨ (θ = 0 ∧ k.val = 18) := by
  apply rigid_sector_angle_bounds k hθ
  · have h := hx.1
    rw [hp, planarCross_real_mul] at h
    exact nonneg_of_mul_nonneg_right h hr
  · have h := hx.2
    rw [hp, planarCross_real_mul] at h
    exact nonpos_of_mul_nonpos_right h hr

theorem rigidSectorParam_range (k : Fin 19) :
    range (rigidSectorParam k) =
      sphereMeridian (rigidDirection k) ∪ sphereMeridian (rigidDirection (cyclicNext k)) := by
  rw [rigidSectorParam, sphereLuneParam_range, sphereMeridianBoundary_range]

theorem rigidSector_polar_endpoint (k : Fin 19) (x : SphereRepresentative)
    (r θ : ℝ) (hr : 0 ≤ r) (hp : horizontal x.val = (r : ℂ) * Circle.exp θ)
    (he : θ = (k.val : ℝ) * (2 * Real.pi / 19) ∨
      θ = ((k.val : ℝ)+1) * (2 * Real.pi / 19)) : x ∈ range (rigidSectorParam k) := by
  rw [rigidSectorParam_range]
  rcases he with he | he
  · left
    refine ⟨r, hr, ?_⟩
    rw [hp, he, ← rigidDirection_angle]
  · right
    refine ⟨r, hr, ?_⟩
    rw [hp, he, ← rigidDirection_next_angle]

/-- This includes the last-to-first meridian and the two common poles. -/
theorem rigid_sector_inter_subset_boundary (k l : Fin 19) (hkl : k ≠ l) :
    rigidSector k ∩ rigidSector l ⊆ range (rigidSectorParam k) := by
  intro x hx
  by_cases hz : horizontal x.val = 0
  · rw [rigidSectorParam_range]
    exact Or.inl ⟨0, le_rfl, by simpa using hz⟩
  obtain ⟨c, hc⟩ := complex_nonnegative_radius (horizontal x.val) hz
  obtain ⟨θ, hθ, hφ⟩ := circle_positive_angle c
  rw [← hφ] at hc
  have hr : 0 < ‖horizontal x.val‖ := norm_pos_iff.mpr hz
  have hδ : 0 < 2 * Real.pi / 19 := by positivity
  obtain hk | ⟨hzero, hk⟩ := rigidSector_polar_bounds k x hx.1 _ _ hr hθ hc
  · by_cases he : θ = (k.val : ℝ) * (2 * Real.pi / 19) ∨
        θ = ((k.val : ℝ)+1) * (2 * Real.pi / 19)
    · exact rigidSector_polar_endpoint k x _ _ hr.le hc he
    have hlow : (k.val : ℝ) * (2 * Real.pi / 19) < θ := lt_of_le_of_ne hk.1
      (fun h => he (Or.inl h.symm))
    have hupp : θ < ((k.val : ℝ)+1) * (2 * Real.pi / 19) := lt_of_le_of_ne hk.2
      (fun h => he (Or.inr h))
    obtain hl | ⟨hl, _⟩ := rigidSector_polar_bounds l x hx.2 _ _ hr hθ hc
    · have hne : k.val ≠ l.val := fun h => hkl (Fin.ext h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hv : (k.val : ℝ)+1 ≤ l.val := by exact_mod_cast hlt
        nlinarith [hl.1]
      · have hv : (l.val : ℝ)+1 ≤ k.val := by exact_mod_cast hgt
        nlinarith [hl.2]
    · have hk0 : 0 ≤ (k.val : ℝ) := Nat.cast_nonneg _
      nlinarith
  · rw [rigidSectorParam_range]
    right
    refine ⟨‖horizontal x.val‖, hr.le, ?_⟩
    have hnext : cyclicNext k = (0 : Fin 19) := by
      apply Fin.ext
      simp [cyclicNext, hk]
    rw [hnext]
    simpa [hzero, rigidDirection] using hc

end Venn19.Topology
