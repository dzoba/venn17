import VennTopology.SphereMeridians
import VennTopology.JordanDisk
import VennTopology.PlaneRealization

/-! A spherical lune is a closed disk with its explicit two-meridian boundary.
The proof uses the proved Schoenflies theorem after puncturing outside the lune. -/
noncomputable section
namespace Venn17.Topology
open Set LeanEval.Topology.ClassificationOfSurfaces

def planarCross (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

@[simp] theorem planarCross_self (z : ℂ) : planarCross z z = 0 := by
  simp [planarCross, mul_comm]
theorem planarCross_swap (z w : ℂ) : planarCross z w = -planarCross w z := by
  unfold planarCross
  ring
theorem planarCross_real_mul (z w : ℂ) (r : ℝ) :
    planarCross z ((r : ℂ)*w) = r * planarCross z w := by
  simp [planarCross, Complex.mul_re, Complex.mul_im]
  ring
@[fun_prop] theorem continuous_planarCross (z : ℂ) : Continuous (planarCross z) := by
  unfold planarCross
  fun_prop

theorem planarCross_zero (d : Circle) (w : ℂ) (h : planarCross d w = 0) :
    ∃ r : ℝ, w = (r : ℂ) * d := by
  refine ⟨(d : ℂ).re*w.re + (d : ℂ).im*w.im, ?_⟩
  have hd := Circle.normSq_coe d
  rw [Complex.normSq_apply] at hd
  dsimp [planarCross] at h
  apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  · linear_combination -w.re * hd - (d : ℂ).im * h
  · linear_combination -w.im * hd + (d : ℂ).re * h

def sphereLune (d e : Circle) : Set SphereRepresentative :=
  {x | 0 ≤ planarCross d (horizontal x.val) ∧ planarCross e (horizontal x.val) ≤ 0}

theorem sphereLune_closed (d e : Circle) : IsClosed (sphereLune d e) := by
  apply IsClosed.inter
  · exact isClosed_le continuous_const
      ((continuous_planarCross d).comp (continuous_horizontal.comp continuous_subtype_val))
  · exact isClosed_le
      ((continuous_planarCross e).comp (continuous_horizontal.comp continuous_subtype_val)) continuous_const

theorem sphereLune_compact (d e : Circle) : IsCompact (sphereLune d e) :=
  (sphereLune_closed d e).isCompact

theorem sphereLune_strict_interior (d e : Circle) (x : SphereRepresentative)
    (hd : 0 < planarCross d (horizontal x.val))
    (he : planarCross e (horizontal x.val) < 0) : x ∈ interior (sphereLune d e) := by
  let U : Set SphereRepresentative :=
    {x | 0 < planarCross d (horizontal x.val) ∧ planarCross e (horizontal x.val) < 0}
  have ho : IsOpen U := (isOpen_lt continuous_const
    ((continuous_planarCross d).comp (continuous_horizontal.comp continuous_subtype_val))).inter
    (isOpen_lt ((continuous_planarCross e).comp
      (continuous_horizontal.comp continuous_subtype_val)) continuous_const)
  exact mem_interior.mpr ⟨U, (fun _ h => ⟨h.1.le, h.2.le⟩), ho, hd, he⟩

theorem sphereLune_boundary_subset (d e : Circle) (hde : 0 < planarCross d e) :
    range (sphereMeridianBoundary d e) ⊆ sphereLune d e := by
  rw [sphereMeridianBoundary_range]
  rintro x (⟨r, hr, hx⟩ | ⟨r, hr, hx⟩)
  · constructor
    · simp [hx, planarCross_real_mul]
    · rw [hx, planarCross_real_mul, planarCross_swap]
      exact mul_nonpos_of_nonneg_of_nonpos hr (neg_nonpos.mpr hde.le)
  · constructor
    · rw [hx, planarCross_real_mul]
      exact mul_nonneg hr hde.le
    · simp [hx, planarCross_real_mul]

theorem sphereLune_frontier (d e : Circle) (hde : 0 < planarCross d e) :
    frontier (sphereLune d e) ⊆ range (sphereMeridianBoundary d e) := by
  intro x hx
  have hm := (sphereLune_closed d e).frontier_subset hx
  have hn := (mem_frontier_iff_notMem_interior hm).mp hx
  rw [sphereMeridianBoundary_range]
  by_cases hd : planarCross d (horizontal x.val) = 0
  · obtain ⟨r, hr⟩ := planarCross_zero d (horizontal x.val) hd
    left
    refine ⟨r, ?_, hr⟩
    have he := hm.2
    rw [hr, planarCross_real_mul, planarCross_swap] at he
    nlinarith
  · have he : planarCross e (horizontal x.val) = 0 := by
      by_contra he
      exact hn (sphereLune_strict_interior d e x (lt_of_le_of_ne hm.1 (Ne.symm hd))
        (lt_of_le_of_ne hm.2 he))
    obtain ⟨r, hr⟩ := planarCross_zero e (horizontal x.val) he
    right
    refine ⟨r, ?_, hr⟩
    have hd := hm.1
    rw [hr, planarCross_real_mul] at hd
    nlinarith

def sphereAbove (z : ℂ) (hz : Complex.normSq z ≤ 1) : SphereRepresentative :=
  ⟨fromHorizontal z (Real.sqrt (1-Complex.normSq z)), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    have hs : ‖fromHorizontal z (Real.sqrt (1-Complex.normSq z))‖ ^ 2 = 1 := by
      rw [norm_sq_coordinates, horizontal_fromHorizontal, vertical_fromHorizontal,
        Real.sq_sqrt (sub_nonneg.mpr hz)]
      ring
    nlinarith [norm_nonneg (fromHorizontal z (Real.sqrt (1-Complex.normSq z)))]⟩

theorem direction_midpoint_normSq (d e : Circle) :
    Complex.normSq (((d : ℂ)+(e : ℂ))/2) ≤ 1 := by
  rw [Complex.normSq_eq_norm_sq]
  have hn : ‖((d : ℂ)+(e : ℂ))/2‖ ≤ 1 := by
    rw [norm_div]
    norm_num
    have ht := norm_add_le (d : ℂ) (e : ℂ)
    simp only [Circle.norm_coe] at ht
    linarith
  nlinarith [norm_nonneg (((d : ℂ)+(e : ℂ))/2)]

def sphereLuneMidpoint (d e : Circle) : SphereRepresentative :=
  sphereAbove (((d : ℂ)+(e : ℂ))/2) (direction_midpoint_normSq d e)

theorem sphereLuneMidpoint_cross_left (d e : Circle) :
    planarCross d (horizontal (sphereLuneMidpoint d e).val) = planarCross d e / 2 := by
  simp [sphereLuneMidpoint, sphereAbove, planarCross]
  ring
theorem sphereLuneMidpoint_cross_right (d e : Circle) :
    planarCross e (horizontal (sphereLuneMidpoint d e).val) = -planarCross d e / 2 := by
  simp [sphereLuneMidpoint, sphereAbove, planarCross]
  ring

theorem sphereLune_interior_witness (d e : Circle) (hde : 0 < planarCross d e) :
    ∃ x ∈ interior (sphereLune d e), x ∉ range (sphereMeridianBoundary d e) := by
  refine ⟨sphereLuneMidpoint d e, ?_, ?_⟩
  · apply sphereLune_strict_interior
    · rw [sphereLuneMidpoint_cross_left]; positivity
    · rw [sphereLuneMidpoint_cross_right]; linarith
  · rw [sphereMeridianBoundary_range]
    rintro (⟨r, _, hr⟩ | ⟨r, _, hr⟩)
    · have hc := sphereLuneMidpoint_cross_left d e
      rw [hr, planarCross_real_mul, planarCross_self, mul_zero] at hc
      linarith
    · have hc := sphereLuneMidpoint_cross_right d e
      rw [hr, planarCross_real_mul, planarCross_self, mul_zero] at hc
      linarith

def sphereLuneOutside (d e : Circle) : SphereRepresentative :=
  ⟨-(sphereLuneMidpoint d e).val, by simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_neg]
    using (sphereLuneMidpoint d e).property⟩

theorem sphereLuneOutside_not_mem (d e : Circle) (hde : 0 < planarCross d e) :
    sphereLuneOutside d e ∉ sphereLune d e := by
  intro hx
  have hh : horizontal (sphereLuneOutside d e).val = -horizontal (sphereLuneMidpoint d e).val := rfl
  have hc := sphereLuneMidpoint_cross_left d e
  have hl := hx.1
  rw [hh] at hl
  simp only [planarCross, Complex.neg_re, Complex.neg_im] at hl hc
  dsimp [planarCross] at hde
  linarith

def sphereLuneParam (d e : Circle) : UnitCircle → SphereRepresentative :=
  sphereMeridianBoundary d e ∘ JordanCurve.Arcs.spherePlaneHomeoCircle

theorem sphereLuneParam_continuous (d e : Circle) : Continuous (sphereLuneParam d e) :=
  (sphereMeridianBoundary_continuous d e).comp JordanCurve.Arcs.spherePlaneHomeoCircle.continuous

theorem sphereLuneParam_injective (d e : Circle) (hde : 0 < planarCross d e) :
    Function.Injective (sphereLuneParam d e) := by
  apply (sphereMeridianBoundary_injective (show d ≠ e from ?_)).comp
    JordanCurve.Arcs.spherePlaneHomeoCircle.injective
  rintro rfl
  simp at hde

theorem sphereLuneParam_range (d e : Circle) :
    range (sphereLuneParam d e) = range (sphereMeridianBoundary d e) := by
  rw [sphereLuneParam, range_comp, JordanCurve.Arcs.spherePlaneHomeoCircle.surjective.range_eq,
    image_univ]

theorem sphereLuneParam_subset (d e : Circle) (hde : 0 < planarCross d e) :
    range (sphereLuneParam d e) ⊆ sphereLune d e := by
  rw [sphereLuneParam_range]
  exact sphereLune_boundary_subset d e hde

theorem sphereLuneParam_frontier (d e : Circle) (hde : 0 < planarCross d e) :
    frontier (sphereLune d e) ⊆ range (sphereLuneParam d e) := by
  rw [sphereLuneParam_range]
  exact sphereLune_frontier d e hde

theorem sphereLuneParam_interior (d e : Circle) (hde : 0 < planarCross d e) :
    ∃ x ∈ interior (sphereLune d e), x ∉ range (sphereLuneParam d e) := by
  rw [sphereLuneParam_range]
  exact sphereLune_interior_witness d e hde

/-- A disk chart for an actual spherical lune, retaining its specified boundary. -/
def sphereLuneDisk (d e : Circle) (hde : 0 < planarCross d e) :
    sphereLune d e ≃ₜ PlaneClosedDisk :=
  puncturedJordanDisk (sphereLuneOutside d e)
    (sphereWithoutPointHomeomorph (sphereLuneOutside d e))
    (sphereLune d e) (sphereLune_compact d e) (sphereLuneOutside_not_mem d e hde)
    (sphereLuneParam d e) (sphereLuneParam_continuous d e) (sphereLuneParam_injective d e hde)
    (sphereLuneParam_subset d e hde) (sphereLuneParam_frontier d e hde)
    (sphereLuneParam_interior d e hde)

theorem sphereLuneDisk_boundary (d e : Circle) (hde : 0 < planarCross d e) (z : UnitCircle) :
    (sphereLuneDisk d e hde
      ⟨sphereLuneParam d e z, sphereLuneParam_subset d e hde (mem_range_self z)⟩).val = z.val :=
  puncturedJordanDisk_boundary (sphereLuneOutside d e)
    (sphereWithoutPointHomeomorph (sphereLuneOutside d e))
    (sphereLune d e) (sphereLune_compact d e) (sphereLuneOutside_not_mem d e hde)
    (sphereLuneParam d e) (sphereLuneParam_continuous d e) (sphereLuneParam_injective d e hde)
    (sphereLuneParam_subset d e hde) (sphereLuneParam_frontier d e hde)
    (sphereLuneParam_interior d e hde) z

end Venn17.Topology
