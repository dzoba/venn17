import ClassificationOfSurfaces.Representatives
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! The target rotation is a rigid Euclidean rotation of the standard sphere.
Complex multiplication acts in the horizontal plane and fixes the vertical axis. -/
noncomputable section
namespace Venn19.Topology
open Set LeanEval.Topology.ClassificationOfSurfaces

abbrev Space3 := EuclideanSpace ℝ (Fin 3)

def horizontal (x : Space3) : ℂ := ⟨x 0, x 1⟩
def vertical (x : Space3) : ℝ := x 2
def fromHorizontal (z : ℂ) (h : ℝ) : Space3 := !₂[z.re, z.im, h]

@[simp] theorem horizontal_fromHorizontal (z : ℂ) (h : ℝ) :
    horizontal (fromHorizontal z h) = z := by rfl
@[simp] theorem vertical_fromHorizontal (z : ℂ) (h : ℝ) :
    vertical (fromHorizontal z h) = h := by rfl
@[simp] theorem fromHorizontal_coordinates (x : Space3) :
    fromHorizontal (horizontal x) (vertical x) = x := by
  ext i
  fin_cases i <;> rfl

theorem norm_sq_coordinates (x : Space3) :
    ‖x‖ ^ 2 = Complex.normSq (horizontal x) + vertical x ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [horizontal, vertical, Complex.normSq_apply, Fin.sum_univ_succ, sq]
  ring

@[fun_prop] theorem continuous_horizontal : Continuous horizontal := by
  have he : horizontal = fun x : Space3 => (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
    funext x
    apply Complex.ext <;> simp [horizontal]
  rw [he]
  fun_prop
@[fun_prop] theorem continuous_vertical : Continuous vertical := by
  unfold vertical
  fun_prop
@[fun_prop] theorem continuous_fromHorizontal :
    Continuous (fun p : ℂ × ℝ => fromHorizontal p.1 p.2) := by
  unfold fromHorizontal
  fun_prop

def axialRotationMap (c : Circle) (x : Space3) : Space3 :=
  fromHorizontal (c * horizontal x) (vertical x)

@[simp] theorem horizontal_axialRotationMap (c : Circle) (x : Space3) :
    horizontal (axialRotationMap c x) = c * horizontal x := rfl
@[simp] theorem vertical_axialRotationMap (c : Circle) (x : Space3) :
    vertical (axialRotationMap c x) = vertical x := rfl

theorem axialRotationMap_norm (c : Circle) (x : Space3) :
    ‖axialRotationMap c x‖ = ‖x‖ := by
  have h : ‖axialRotationMap c x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp [norm_sq_coordinates, Complex.normSq_mul]
  nlinarith [norm_nonneg (axialRotationMap c x), norm_nonneg x]

theorem axialRotationMap_sub (c : Circle) (x y : Space3) :
    axialRotationMap c (x-y) = axialRotationMap c x - axialRotationMap c y := by
  ext i
  fin_cases i <;>
    simp [axialRotationMap, fromHorizontal, horizontal, vertical, Complex.mul_re,
      Complex.mul_im] <;> ring

theorem axialRotationMap_isometry (c : Circle) : Isometry (axialRotationMap c) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, ← axialRotationMap_sub, axialRotationMap_norm, dist_eq_norm]

@[simp] theorem axialRotationMap_one (x : Space3) : axialRotationMap 1 x = x := by
  simp [axialRotationMap]

theorem axialRotationMap_mul (c d : Circle) (x : Space3) :
    axialRotationMap (c*d) x = axialRotationMap c (axialRotationMap d x) := by
  simp [axialRotationMap, mul_assoc]

/-- A rigid rotation of three-dimensional Euclidean space, with the standard metric. -/
def axialRotation (c : Circle) : Space3 ≃ᵢ Space3 where
  toFun := axialRotationMap c
  invFun := axialRotationMap c⁻¹
  left_inv x := by rw [← axialRotationMap_mul, inv_mul_cancel, axialRotationMap_one]
  right_inv x := by rw [← axialRotationMap_mul, mul_inv_cancel, axialRotationMap_one]
  isometry_toFun := axialRotationMap_isometry c

/-- Restriction of that rigid rotation to the actual Euclidean unit sphere. -/
def rigidSphereRotation (c : Circle) : SphereRepresentative ≃ₜ SphereRepresentative :=
  (axialRotation c).toHomeomorph.subtype (fun x => by
    simp only [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact (axialRotationMap_norm c x).symm ▸ Iff.rfl)

@[simp] theorem rigidSphereRotation_val (c : Circle) (x : SphereRepresentative) :
    (rigidSphereRotation c x).val = axialRotationMap c x.val := rfl

theorem rigidSphereRotation_mul (c d : Circle) (x : SphereRepresentative) :
    rigidSphereRotation (c*d) x = rigidSphereRotation c (rigidSphereRotation d x) := by
  apply Subtype.ext
  exact axialRotationMap_mul c d x.val

@[simp] theorem rigidSphereRotation_one (x : SphereRepresentative) :
    rigidSphereRotation 1 x = x := by
  apply Subtype.ext
  exact axialRotationMap_one x.val

/-- The required positive generator, with angle exactly `2π/19`. -/
def rigidGenerator : Circle := Circle.exp (2 * Real.pi / 19)

theorem rigidGenerator_pow_nineteen : rigidGenerator ^ 19 = 1 := by
  rw [rigidGenerator, ← Circle.exp_nsmul]
  rw [nsmul_eq_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (19 : ℝ) * (2 * Real.pi / 19) = 2 * Real.pi by ring]
  exact Circle.exp_two_pi

theorem rigidSphereRotation_iterate (c : Circle) (n : ℕ) (x : SphereRepresentative) :
    (rigidSphereRotation c)^[n] x = rigidSphereRotation (c^n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, ← rigidSphereRotation_mul, pow_succ']

theorem rigidSphereRotation_period (x : SphereRepresentative) :
    (rigidSphereRotation rigidGenerator)^[19] x = x := by
  rw [rigidSphereRotation_iterate, rigidGenerator_pow_nineteen, rigidSphereRotation_one]

end Venn19.Topology
