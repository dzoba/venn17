import VennTopology.RigidSphere
import VennTopology.CyclicPolygon

/-! Standard meridian Jordan curves on the Euclidean sphere. The upper and
lower semicircles of the parameter follow the two meridians in opposite
directions. Their equivariance is with respect to a proved Euclidean isometry. -/
noncomputable section
namespace Venn17.Topology
open Set LeanEval.Topology.ClassificationOfSurfaces Coordinates

/-- Two rays joined at their common origin, parametrized by a signed real number. -/
def splitRay (d e : Circle) (t : ℝ) : ℂ :=
  (max t 0 : ℝ) * (d : ℂ) + (max (-t) 0 : ℝ) * (e : ℂ)

theorem splitRay_normSq (d e : Circle) (t : ℝ) :
    Complex.normSq (splitRay d e t) = t^2 := by
  rcases le_total 0 t with ht | ht
  · simp [splitRay, max_eq_left ht, max_eq_right (neg_nonpos.mpr ht),
      Complex.normSq_mul, Complex.normSq_ofReal, sq]
  · simp [splitRay, max_eq_right ht, max_eq_left (neg_nonneg.mpr ht),
      Complex.normSq_mul, Complex.normSq_ofReal, sq]

theorem splitRay_injective {d e : Circle} (hde : d ≠ e) :
    Function.Injective (splitRay d e) := by
  intro t s h
  have hsq := congrArg Complex.normSq h
  rw [splitRay_normSq, splitRay_normSq] at hsq
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with heq | heq
  · exact heq
  have hs : s = -t := by linarith
  subst s
  by_cases ht0 : t = 0
  · simp [ht0]
  exfalso
  apply hde
  apply Subtype.ext
  rcases le_total 0 t with ht | ht
  · have hm : (t : ℂ) * (d : ℂ) = (t : ℂ) * (e : ℂ) := by
      simpa [splitRay, max_eq_left ht, max_eq_right (neg_nonpos.mpr ht)] using h
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr ht0) hm
  · have hm : ((-t : ℝ) : ℂ) * (e : ℂ) = ((-t : ℝ) : ℂ) * (d : ℂ) := by
      simpa [splitRay, max_eq_right ht, max_eq_left (neg_nonneg.mpr ht)] using h
    exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr ht0)) hm).symm

@[fun_prop] theorem continuous_splitRay (d e : Circle) : Continuous (splitRay d e) := by
  unfold splitRay
  fun_prop

theorem splitRay_rotate (c d e : Circle) (t : ℝ) :
    splitRay (c*d) (c*e) t = (c : ℂ) * splitRay d e t := by
  simp only [splitRay, Circle.coe_mul]
  ring

def sphereMeridianBoundaryVector (d e : Circle) (z : Circle) : Space3 :=
  fromHorizontal (splitRay d e (z : ℂ).im) (z : ℂ).re

theorem sphereMeridianBoundaryVector_norm (d e z : Circle) :
    ‖sphereMeridianBoundaryVector d e z‖ = 1 := by
  have hz := Circle.normSq_coe z
  have hs : ‖sphereMeridianBoundaryVector d e z‖ ^ 2 = 1 := by
    rw [norm_sq_coordinates]
    simp only [sphereMeridianBoundaryVector, horizontal_fromHorizontal,
      vertical_fromHorizontal, splitRay_normSq]
    rw [Complex.normSq_apply] at hz
    nlinarith
  nlinarith [norm_nonneg (sphereMeridianBoundaryVector d e z)]

/-- An explicit curve in the actual Euclidean sphere, without any chosen chart. -/
def sphereMeridianBoundary (d e : Circle) (z : Circle) : SphereRepresentative :=
  ⟨sphereMeridianBoundaryVector d e z, by
    simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using
      sphereMeridianBoundaryVector_norm d e z⟩

@[fun_prop] theorem sphereMeridianBoundary_continuous (d e : Circle) :
    Continuous (sphereMeridianBoundary d e) := by
  apply Continuous.subtype_mk
  exact continuous_fromHorizontal.comp
    ((continuous_splitRay d e |>.comp (Complex.continuous_im.comp continuous_subtype_val)).prodMk
      (Complex.continuous_re.comp continuous_subtype_val))

theorem sphereMeridianBoundary_injective {d e : Circle} (hde : d ≠ e) :
    Function.Injective (sphereMeridianBoundary d e) := by
  intro z w h
  have hv := congrArg (fun x : SphereRepresentative => vertical x.val) h
  have hh := congrArg (fun x : SphereRepresentative => horizontal x.val) h
  apply Subtype.ext
  apply Complex.ext
  · exact hv
  · exact splitRay_injective hde hh

theorem sphereMeridianBoundary_rotation (c d e z : Circle) :
    rigidSphereRotation c (sphereMeridianBoundary d e z) =
      sphereMeridianBoundary (c*d) (c*e) z := by
  apply Subtype.ext
  change fromHorizontal _ _ = fromHorizontal _ _
  rw [splitRay_rotate]
  rfl

/-- The 17 equally spaced meridian directions. -/
def rigidDirection (k : Fin 17) : Circle := rigidGenerator ^ k.val

theorem rigidDirection_next (k : Fin 17) :
    rigidDirection (cyclicNext k) = rigidGenerator * rigidDirection k := by
  change rigidGenerator ^ ((k.val+1)%17) = rigidGenerator * rigidGenerator^k.val
  by_cases h : k.val + 1 < 17
  · rw [Nat.mod_eq_of_lt h, pow_succ']
  · have hk : k.val = 16 := by omega
    simp [hk, ← pow_succ', rigidGenerator_pow_seventeen]

theorem rigidDirection_injective : Function.Injective rigidDirection := by
  intro k l h
  have ha : 0 < 2 * Real.pi / 17 := by positivity
  have hm (i : Fin 17) : (i.val : ℝ) * (2 * Real.pi / 17) ∈ Ico 0 (2 * Real.pi) := by
    have hi : (i.val : ℝ) < 17 := by exact_mod_cast i.isLt
    constructor
    · positivity
    · nlinarith
  have he : Circle.exp ((k.val : ℝ) * (2 * Real.pi / 17)) =
      Circle.exp ((l.val : ℝ) * (2 * Real.pi / 17)) := by
    simpa only [Circle.exp_natCast_mul, rigidDirection, rigidGenerator] using h
  have hv := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi)
    (by linarith) (hm k) (hm l) he
  have hval : (k.val : ℝ) = l.val := mul_right_cancel₀ ha.ne' hv
  apply Fin.ext
  exact_mod_cast hval

theorem rigidDirection_ne_next (k : Fin 17) : rigidDirection k ≠ rigidDirection (cyclicNext k) := by
  intro h
  have hval := congrArg Fin.val (rigidDirection_injective h)
  change k.val = (k.val+1)%17 at hval
  omega

/-- The prescribed boundary for target sector `k`. -/
def rigidSectorBoundary (k : Fin 17) : Circle → SphereRepresentative :=
  sphereMeridianBoundary (rigidDirection k) (rigidDirection (cyclicNext k))

theorem rigidSectorBoundary_continuous (k : Fin 17) : Continuous (rigidSectorBoundary k) :=
  sphereMeridianBoundary_continuous _ _

theorem rigidSectorBoundary_injective (k : Fin 17) : Function.Injective (rigidSectorBoundary k) :=
  sphereMeridianBoundary_injective (rigidDirection_ne_next k)

theorem rigidSectorBoundary_rotation (k : Fin 17) (z : Circle) :
    rigidSphereRotation rigidGenerator (rigidSectorBoundary k z) =
      rigidSectorBoundary (cyclicNext k) z := by
  unfold rigidSectorBoundary
  rw [sphereMeridianBoundary_rotation, ← rigidDirection_next, ← rigidDirection_next]

theorem sphere_coordinates (x : SphereRepresentative) :
    Complex.normSq (horizontal x.val) + vertical x.val ^ 2 = 1 := by
  rw [← norm_sq_coordinates]
  have hn : ‖x.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using x.property
  rw [hn, one_pow]

/-- A closed half of a great circle, including both poles. -/
def sphereMeridian (d : Circle) : Set SphereRepresentative :=
  {x | ∃ r : ℝ, 0 ≤ r ∧ horizontal x.val = (r : ℂ) * d}

theorem sphereMeridianBoundary_range (d e : Circle) :
    range (sphereMeridianBoundary d e) = sphereMeridian d ∪ sphereMeridian e := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rcases le_total 0 (z : ℂ).im with hz | hz
    · left
      refine ⟨(z : ℂ).im, hz, ?_⟩
      simp [sphereMeridianBoundary, sphereMeridianBoundaryVector, splitRay,
        max_eq_left hz, max_eq_right (neg_nonpos.mpr hz)]
    · right
      refine ⟨-(z : ℂ).im, neg_nonneg.mpr hz, ?_⟩
      simp [sphereMeridianBoundary, sphereMeridianBoundaryVector, splitRay,
        max_eq_right hz, max_eq_left (neg_nonneg.mpr hz)]
  · rintro (⟨r, hr, hx⟩ | ⟨r, hr, hx⟩)
    · have hs := sphere_coordinates x
      rw [hx, Complex.normSq_mul, Circle.normSq_coe, mul_one, Complex.normSq_ofReal] at hs
      let z : Circle := ⟨⟨vertical x.val, r⟩, by
        apply mem_sphere_zero_iff_norm.mpr
        have hn : ‖(⟨vertical x.val, r⟩ : ℂ)‖ ^ 2 = 1 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          nlinarith
        nlinarith [norm_nonneg (⟨vertical x.val, r⟩ : ℂ)]⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change fromHorizontal (splitRay d e r) (vertical x.val) = x.val
      rw [splitRay, max_eq_left hr, max_eq_right (neg_nonpos.mpr hr)]
      simp only [Complex.ofReal_zero, zero_mul, add_zero, ← hx, fromHorizontal_coordinates]
    · have hs := sphere_coordinates x
      rw [hx, Complex.normSq_mul, Circle.normSq_coe, mul_one, Complex.normSq_ofReal] at hs
      let z : Circle := ⟨⟨vertical x.val, -r⟩, by
        apply mem_sphere_zero_iff_norm.mpr
        have hn : ‖(⟨vertical x.val, -r⟩ : ℂ)‖ ^ 2 = 1 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          nlinarith
        nlinarith [norm_nonneg (⟨vertical x.val, -r⟩ : ℂ)]⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change fromHorizontal (splitRay d e (-r)) (vertical x.val) = x.val
      rw [splitRay, neg_neg, max_eq_left hr, max_eq_right (neg_nonpos.mpr hr)]
      simp only [Complex.ofReal_zero, zero_mul, zero_add, ← hx, fromHorizontal_coordinates]

end Venn17.Topology
