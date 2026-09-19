import VennTopology.RigidSphereConjugacy
import Mathlib.Analysis.Complex.Isometry

/-! Stereographic projection from the specified north pole, with a fixed
horizontal coordinate chart. It commutes with every axial rigid rotation. -/
noncomputable section
namespace Venn17.Topology
open Set LeanEval.Topology.ClassificationOfSurfaces
open scoped InnerProductSpace

theorem rigidNorth_norm : ‖rigidNorth.val‖ = 1 :=
  mem_sphere_zero_iff_norm.mp rigidNorth.property

theorem rigidNorth_inner (x : Space3) : inner ℝ rigidNorth.val x = vertical x := by
  rw [rigidNorth_val]
  simp [PiLp.inner_apply, Fin.sum_univ_succ, fromHorizontal, vertical]

abbrev HorizontalPlane := (ℝ ∙ rigidNorth.val)ᗮ

theorem mem_horizontalPlane (x : Space3) : x ∈ HorizontalPlane ↔ vertical x = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, rigidNorth_inner]

def horizontalPlaneHomeomorph : HorizontalPlane ≃ₜ ℂ where
  toFun x := horizontal x.val
  invFun z := ⟨fromHorizontal z 0, (mem_horizontalPlane _).mpr rfl⟩
  left_inv x := by
    apply Subtype.ext
    change fromHorizontal (horizontal x.val) 0 = x.val
    have hx := (mem_horizontalPlane x.val).mp x.property
    rw [← hx, fromHorizontal_coordinates]
  right_inv z := rfl
  continuous_toFun := continuous_horizontal.comp continuous_subtype_val
  continuous_invFun := (continuous_fromHorizontal.comp (continuous_id.prodMk continuous_const)).subtype_mk _

theorem horizontal_projection (x : Space3) :
    (HorizontalPlane.orthogonalProjectionOnto x).val = fromHorizontal (horizontal x) 0 := by
  change HorizontalPlane.starProjection x = _
  apply HorizontalPlane.eq_starProjection_of_mem_of_inner_eq_zero
  · exact (mem_horizontalPlane _).mpr rfl
  · intro w hw
    have hw := (mem_horizontalPlane w).mp hw
    simp [PiLp.inner_apply, Fin.sum_univ_succ, fromHorizontal, horizontal, vertical] at hw ⊢
    simp [hw]

theorem horizontal_smul (r : ℝ) (x : Space3) :
    horizontal (r • x) = (r : ℂ) * horizontal x := by
  apply Complex.ext <;> simp [horizontal, Complex.mul_re, Complex.mul_im]

abbrev NorthPuncturedSphere := {x : SphereRepresentative // x ≠ rigidNorth}

def northStereographic : NorthPuncturedSphere ≃ₜ HorizontalPlane := by
  let s := stereographic rigidNorth_norm
  have hs : {x : SphereRepresentative | x ≠ rigidNorth} = s.source := by
    ext x
    simp only [s, stereographic_source, mem_setOf_eq, mem_compl_iff, mem_singleton_iff]
  exact (Homeomorph.setCongr hs).trans
    (s.toHomeomorphSourceTarget.trans (Homeomorph.Set.univ HorizontalPlane))

def northStereographicComplex : NorthPuncturedSphere ≃ₜ ℂ :=
  northStereographic.trans horizontalPlaneHomeomorph

theorem northStereographicComplex_apply (x : NorthPuncturedSphere) :
    northStereographicComplex x =
      ((2 / (1-vertical x.val.val) : ℝ) : ℂ) * horizontal x.val.val := by
  change horizontal ((stereographic rigidNorth_norm x.val).val) = _
  rw [stereographic_apply]
  change horizontal ((2 / (1-inner ℝ rigidNorth.val x.val.val)) •
    (HorizontalPlane.orthogonalProjectionOnto x.val.val).val) = _
  rw [rigidNorth_inner, horizontal_smul, horizontal_projection, horizontal_fromHorizontal]

theorem rigidSphereRotation_north (c : Circle) : rigidSphereRotation c rigidNorth = rigidNorth := by
  apply Subtype.ext
  rw [rigidSphereRotation_val, rigidNorth_val]
  simp [axialRotationMap]

def rigidNorthPuncturedRotation (c : Circle) : NorthPuncturedSphere ≃ₜ NorthPuncturedSphere :=
  (rigidSphereRotation c).subtype (fun x => by
    have he : rigidSphereRotation c x = rigidNorth ↔ x = rigidNorth := by
      simpa only [rigidSphereRotation_north] using
        (rigidSphereRotation c).injective.eq_iff (a := x) (b := rigidNorth)
    exact not_congr he.symm)

theorem northStereographicComplex_rotation (c : Circle) (x : NorthPuncturedSphere) :
    northStereographicComplex (rigidNorthPuncturedRotation c x) =
      _root_.rotation c (northStereographicComplex x) := by
  rw [northStereographicComplex_apply, northStereographicComplex_apply, rotation_apply]
  change ((2 / (1-vertical (axialRotationMap c x.val.val)) : ℝ) : ℂ) *
    horizontal (axialRotationMap c x.val.val) = _
  rw [vertical_axialRotationMap, horizontal_axialRotationMap]
  ring

end Venn17.Topology
