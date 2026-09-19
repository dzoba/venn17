import VennTopology.RigidSectorDisk

/-! The explicit spherical sectors cover the entire standard sphere. -/
noncomputable section
namespace Venn17.Topology
open Set Coordinates LeanEval.Topology.ClassificationOfSurfaces

theorem circle_positive_angle (z : Circle) :
    ∃ θ ∈ Ico (0 : ℝ) (2 * Real.pi), Circle.exp θ = z := by
  by_cases h : 0 ≤ (z : ℂ).arg
  · exact ⟨(z : ℂ).arg, ⟨h, lt_of_le_of_lt (Complex.arg_le_pi _) (by linarith [Real.pi_pos])⟩,
      Circle.exp_arg z⟩
  · refine ⟨(z : ℂ).arg + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
    · linarith [Complex.neg_pi_lt_arg (z : ℂ), Real.pi_pos]
    · linarith
    · rw [Circle.exp_add_two_pi, Circle.exp_arg]

theorem planarCross_exp (θ φ : ℝ) :
    planarCross (Circle.exp θ) (Circle.exp φ) = Real.sin (φ-θ) := by
  simp [planarCross, Circle.coe_exp, Complex.exp_re, Complex.exp_im, Real.sin_sub]
  ring

theorem rigidDirection_angle (k : Fin 17) :
    rigidDirection k = Circle.exp ((k.val : ℝ) * (2 * Real.pi / 17)) := by
  rw [Circle.exp_natCast_mul]
  rfl

theorem rigidDirection_next_angle (k : Fin 17) :
    rigidDirection (cyclicNext k) = Circle.exp (((k.val : ℝ)+1) * (2 * Real.pi / 17)) := by
  rw [rigidDirection_next, rigidDirection_angle, rigidGenerator, ← Circle.exp_add]
  congr 1
  ring

theorem angle_in_rigid_sector {θ : ℝ} (hθ : θ ∈ Ico 0 (2 * Real.pi)) :
    ∃ k : Fin 17, (k.val : ℝ) * (2 * Real.pi / 17) ≤ θ ∧
      θ ≤ ((k.val : ℝ)+1) * (2 * Real.pi / 17) := by
  let a : ℝ := 2 * Real.pi / 17
  have ha : 0 < a := by dsimp [a]; positivity
  have hq : 0 ≤ θ/a := div_nonneg hθ.1 ha.le
  let n := ⌊θ/a⌋₊
  have hn : n < 17 := by
    apply (Nat.floor_lt hq).mpr
    rw [div_lt_iff₀ ha]
    dsimp [a]
    nlinarith [hθ.2]
  refine ⟨⟨n, hn⟩, ?_, ?_⟩
  · exact (le_div_iff₀ ha).mp (Nat.floor_le hq)
  · exact ((div_lt_iff₀ ha).mp (Nat.lt_floor_add_one (θ/a))).le

theorem circle_in_rigid_sector (c : Circle) :
    ∃ k : Fin 17, 0 ≤ planarCross (rigidDirection k) c ∧
      planarCross (rigidDirection (cyclicNext k)) c ≤ 0 := by
  obtain ⟨θ, hθ, rfl⟩ := circle_positive_angle c
  obtain ⟨k, hl, hu⟩ := angle_in_rigid_sector hθ
  refine ⟨k, ?_, ?_⟩
  · rw [rigidDirection_angle, planarCross_exp]
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · nlinarith [Real.pi_pos]
  · rw [rigidDirection_next_angle, planarCross_exp]
    apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
    · linarith
    · nlinarith [Real.pi_pos]

theorem complex_nonnegative_radius (z : ℂ) (hz : z ≠ 0) :
    ∃ c : Circle, z = (‖z‖ : ℂ) * c := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let c : Circle := ⟨z / (‖z‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn])⟩
  refine ⟨c, ?_⟩
  change z = (‖z‖ : ℂ) * (z / (‖z‖ : ℂ))
  field_simp [Complex.ofReal_ne_zero.mpr hn]

/-- Every point, including the poles, lies in an explicit standard sector. -/
theorem rigid_sectors_cover : (⋃ k, rigidSector k) = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hz : horizontal x.val = 0
  · apply mem_iUnion.mpr
    refine ⟨0, ?_⟩
    change 0 ≤ planarCross _ _ ∧ planarCross _ _ ≤ 0
    simp [hz, planarCross]
  · obtain ⟨c, hc⟩ := complex_nonnegative_radius (horizontal x.val) hz
    obtain ⟨k, hd, he⟩ := circle_in_rigid_sector c
    apply mem_iUnion.mpr
    refine ⟨k, ?_⟩
    change 0 ≤ planarCross _ _ ∧ planarCross _ _ ≤ 0
    rw [hc, planarCross_real_mul, planarCross_real_mul]
    exact ⟨mul_nonneg (norm_nonneg _) hd, mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) he⟩

end Venn17.Topology
