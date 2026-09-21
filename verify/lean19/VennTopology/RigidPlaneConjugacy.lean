import VennTopology.EquivariantStereographic

/-! An unconditional plane realization whose actual symmetry is a rigid
rotation through exactly `2π/19`, centered at the origin. -/
noncomputable section
namespace Venn19.Topology
open Set
attribute [local irreducible] suppliedModel suppliedFaces suppliedSectorColors suppliedSectorMasks

def rigidPuncturedSphereHomeomorph : PuncturedDiagram ≃ₜ NorthPuncturedSphere :=
  rigidSphereConjugacy.subtype (fun x => by
    have he : rigidSphereConjugacy x = rigidNorth ↔ x = patternPoint 0 := by
      simpa only [rigidSphereConjugacy_zero] using
        rigidSphereConjugacy.injective.eq_iff (a := x) (b := patternPoint 0)
    exact not_congr he.symm)

theorem rigidPuncturedSphereHomeomorph_rotation (x : PuncturedDiagram) :
    rigidPuncturedSphereHomeomorph (puncturedRotation x) =
      rigidNorthPuncturedRotation rigidGenerator (rigidPuncturedSphereHomeomorph x) := by
  apply Subtype.ext
  exact rigidSphereConjugacy_rotation x.val

def rigidPlaneHomeomorph : PuncturedDiagram ≃ₜ Plane :=
  rigidPuncturedSphereHomeomorph.trans
    (northStereographicComplex.trans JordanCurve.Arcs.complexLIE.toHomeomorph)

/-- The standard positive rotation, expressed in the orthonormal coordinates of `Plane`. -/
def rigidPlaneRotation : Plane ≃ₗᵢ[ℝ] Plane :=
  JordanCurve.Arcs.complexLIE.symm.trans
    ((_root_.rotation rigidGenerator).trans JordanCurve.Arcs.complexLIE)

theorem rigidPlaneRotation_complex (z : ℂ) :
    rigidPlaneRotation (JordanCurve.Arcs.complexLIE z) =
      JordanCurve.Arcs.complexLIE ((rigidGenerator : ℂ) * z) := by
  change JordanCurve.Arcs.complexLIE
    (_root_.rotation rigidGenerator (JordanCurve.Arcs.complexLIE.symm (JordanCurve.Arcs.complexLIE z))) = _
  rw [JordanCurve.Arcs.complexLIE.symm_apply_apply, rotation_apply]

/-- The sphere conjugacy and the specified stereographic projection give the
required rigid Euclidean rotation equation on the entire plane realization. -/
theorem rigidPlaneHomeomorph_rotation (x : PuncturedDiagram) :
    rigidPlaneHomeomorph (puncturedRotation x) = rigidPlaneRotation (rigidPlaneHomeomorph x) := by
  change JordanCurve.Arcs.complexLIE (northStereographicComplex
      (rigidPuncturedSphereHomeomorph (puncturedRotation x))) =
    rigidPlaneRotation (JordanCurve.Arcs.complexLIE
      (northStereographicComplex (rigidPuncturedSphereHomeomorph x)))
  rw [rigidPlaneRotation_complex, rigidPuncturedSphereHomeomorph_rotation,
    northStereographicComplex_rotation, rotation_apply]

/-- This also conjugates the earlier arbitrary planar realization to the rigid one. -/
def planeSymmetryConjugacy : Plane ≃ₜ Plane := diagramPlaneHomeomorph.symm.trans rigidPlaneHomeomorph

end Venn19.Topology
