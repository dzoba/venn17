import VennTopology.MeridianBoundaryParameters

/-! Source and rigid target meridians have exactly the same parameter
identifications: their common endpoints, and equality within a single arc. -/
noncomputable section
namespace Venn17.Topology
open Set Coordinates LeanEval.Topology.ClassificationOfSurfaces
attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars

def meridianStart : MeridianParameter := ⟨0, by norm_num⟩
def meridianEnd : MeridianParameter := ⟨17, by norm_num⟩

theorem meridianCircleParameter_start : meridianCircleParameter meridianStart = 1 := by
  rw [meridianCircleParameter_exp]
  simp [meridianStart]

theorem meridianCircleParameter_end : meridianCircleParameter meridianEnd = -1 := by
  rw [meridianCircleParameter_exp]
  have he : Real.pi / 17 * meridianEnd.val = Real.pi := by simp [meridianEnd]
  rw [he]
  apply Circle.ext
  simp [Circle.coe_exp, Complex.exp_pi_mul_I]

theorem meridianCircleParameter_im_zero (t : MeridianParameter)
    (ht : (meridianCircleParameter t : ℂ).im = 0) : t = meridianStart ∨ t = meridianEnd := by
  have hn := Circle.normSq_coe (meridianCircleParameter t)
  rw [Complex.normSq_apply, ht] at hn
  have hs : (meridianCircleParameter t : ℂ).re ^ 2 = (1 : ℝ)^2 := by nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with hr | hr
  · left
    apply meridianCircleParameter_injective
    rw [meridianCircleParameter_start]
    apply Circle.ext
    apply Complex.ext <;> simp [hr, ht]
  · right
    apply meridianCircleParameter_injective
    rw [meridianCircleParameter_end]
    apply Circle.ext
    apply Complex.ext <;> simp [hr, ht]

theorem diagramMeridianMap_eq_iff (k l : Fin 17) (t u : MeridianParameter) :
    diagramMeridianMap k t = diagramMeridianMap l u ↔
      t = u ∧ (k = l ∨ t = meridianStart ∨ t = meridianEnd) := by
  constructor
  · intro h
    by_cases hk : k = l
    · subst l
      exact ⟨diagramMeridianMap_injective k h, Or.inl rfl⟩
    have ht : diagramMeridianMap k t ∈ diagramMeridian k := by
      rw [← diagramMeridianMap_range]; exact mem_range_self t
    have hu : diagramMeridianMap k t ∈ diagramMeridian l := by
      rw [h, ← diagramMeridianMap_range]; exact mem_range_self u
    have he : diagramMeridianMap k t ∈ {patternPoint 0, patternPoint 131071} :=
      diagram_meridians_inter k l hk ▸ (show _ ∈ diagramMeridian k ∩ diagramMeridian l from ⟨ht, hu⟩)
    simp only [mem_insert_iff, mem_singleton_iff] at he
    rcases he with he | he
    · have ht0 : t = meridianStart := diagramMeridianMap_injective k
        (he.trans (diagramMeridianMap_zero k).symm)
      have hu0 : u = meridianStart := diagramMeridianMap_injective l
        (h.symm.trans (he.trans (diagramMeridianMap_zero l).symm))
      exact ⟨ht0.trans hu0.symm, Or.inr (Or.inl ht0)⟩
    · have ht1 : t = meridianEnd := diagramMeridianMap_injective k
        (he.trans (diagramMeridianMap_one k).symm)
      have hu1 : u = meridianEnd := diagramMeridianMap_injective l
        (h.symm.trans (he.trans (diagramMeridianMap_one l).symm))
      exact ⟨ht1.trans hu1.symm, Or.inr (Or.inr ht1)⟩
  · rintro ⟨rfl, rfl | rfl | rfl⟩
    · rfl
    · exact (diagramMeridianMap_zero k).trans (diagramMeridianMap_zero l).symm
    · exact (diagramMeridianMap_one k).trans (diagramMeridianMap_one l).symm

def rigidMeridianMap (k : Fin 17) (t : MeridianParameter) : SphereRepresentative :=
  sphereMeridianBoundary (rigidDirection k) (rigidDirection (cyclicNext k)) (meridianCircleParameter t)

theorem rigidMeridianMap_val (k : Fin 17) (t : MeridianParameter) :
    (rigidMeridianMap k t).val =
      fromHorizontal (((meridianCircleParameter t : ℂ).im : ℂ) * rigidDirection k)
        (meridianCircleParameter t : ℂ).re := by
  have ht := meridianCircleParameter_im_nonneg t
  simp [rigidMeridianMap, sphereMeridianBoundary, sphereMeridianBoundaryVector,
    splitRay, max_eq_left ht, max_eq_right (neg_nonpos.mpr ht)]

theorem rigidMeridianMap_horizontal (k : Fin 17) (t : MeridianParameter) :
    horizontal (rigidMeridianMap k t).val =
      ((meridianCircleParameter t : ℂ).im : ℂ) * rigidDirection k := by
  rw [rigidMeridianMap_val, horizontal_fromHorizontal]

theorem rigidMeridianMap_vertical (k : Fin 17) (t : MeridianParameter) :
    vertical (rigidMeridianMap k t).val = (meridianCircleParameter t : ℂ).re := by
  rw [rigidMeridianMap_val, vertical_fromHorizontal]

theorem sphereMeridianBoundary_front (k l : Fin 17) (t : MeridianParameter) :
    sphereMeridianBoundary (rigidDirection k) (rigidDirection l) (meridianCircleParameter t) =
      rigidMeridianMap k t := by
  apply Subtype.ext
  rw [rigidMeridianMap_val]
  have ht := meridianCircleParameter_im_nonneg t
  simp [sphereMeridianBoundary, sphereMeridianBoundaryVector, splitRay,
    max_eq_left ht, max_eq_right (neg_nonpos.mpr ht)]

theorem sphereMeridianBoundary_back (k l : Fin 17) (t : MeridianParameter) :
    sphereMeridianBoundary (rigidDirection k) (rigidDirection l) (meridianCircleParameter t)⁻¹ =
      rigidMeridianMap l t := by
  apply Subtype.ext
  rw [rigidMeridianMap_val]
  have ht := meridianCircleParameter_im_nonneg t
  simp [sphereMeridianBoundary, sphereMeridianBoundaryVector, splitRay,
    max_eq_left ht, max_eq_right (neg_nonpos.mpr ht)]

theorem rigidMeridianMap_eq_iff (k l : Fin 17) (t u : MeridianParameter) :
    rigidMeridianMap k t = rigidMeridianMap l u ↔
      t = u ∧ (k = l ∨ t = meridianStart ∨ t = meridianEnd) := by
  constructor
  · intro h
    have hh := congrArg (fun x : SphereRepresentative => horizontal x.val) h
    have hv := congrArg (fun x : SphereRepresentative => vertical x.val) h
    rw [rigidMeridianMap_horizontal, rigidMeridianMap_horizontal] at hh
    rw [rigidMeridianMap_vertical, rigidMeridianMap_vertical] at hv
    have hn := congrArg norm hh
    simp only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (meridianCircleParameter_im_nonneg t),
      abs_of_nonneg (meridianCircleParameter_im_nonneg u)] at hn
    have htu : t = u := meridianCircleParameter_injective (Circle.ext (Complex.ext hv hn))
    refine ⟨htu, ?_⟩
    subst u
    by_cases hi : (meridianCircleParameter t : ℂ).im = 0
    · exact Or.inr (meridianCircleParameter_im_zero t hi)
    · left
      exact rigidDirection_injective (Circle.ext (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hi) hh))
  · rintro ⟨rfl, rfl | rfl | rfl⟩
    · rfl
    · apply Subtype.ext
      simp [rigidMeridianMap_val, meridianCircleParameter_start]
    · apply Subtype.ext
      simp [rigidMeridianMap_val, meridianCircleParameter_end]

theorem meridian_parameter_compatibility (k l : Fin 17) (t u : MeridianParameter) :
    diagramMeridianMap k t = diagramMeridianMap l u ↔ rigidMeridianMap k t = rigidMeridianMap l u := by
  rw [diagramMeridianMap_eq_iff, rigidMeridianMap_eq_iff]

end Venn17.Topology
