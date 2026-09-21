import VennTopology.PoleRotation
import VennTopology.ConeRotation
import VennTopology.FiniteTriangulation
import VennTopology.PuncturedRegions

/-! Explicit local rigid-rotation conjugacies on the closed cone disks at
both poles of the encoded diagram. These use the same coordinate action as
the global diagram symmetry. -/

noncomputable section
namespace Venn19.Topology
open Set
local instance : DecidableEq Nat := Classical.decEq _
attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars

/-- The complete geometric link, expressed in the finite natural-number encoding. -/
def poleEncodedLinkCircle (p : Fin 2) : Circle ≃ₜ
    Coordinates.link (encodedCells suppliedModel.oriented 524288) (poleIndex p).val :=
  (supplied_dart_link_circle (poleIndex p)).trans
    (Homeomorph.setCongr (encoded_link_eq_dartLink suppliedModel.oriented 524288 _
      (triangleVertices_injective _ _ supplied_corners_bounded supplied_distinct_corners_verified)).symm)

def poleRotationAngle (p : Fin 2) : ℝ := if p = 0 then 2 * Real.pi / 19 else -(2 * Real.pi / 19)

theorem pole_encoded_link_rotation (p : Fin 2) (z : Circle) :
    Coordinates.reindex encodedRotation (poleEncodedLinkCircle p z).val =
      (poleEncodedLinkCircle p (Circle.exp (poleRotationAngle p) * z)).val := by
  fin_cases p
  · exact zero_pole_link_rotation z
  · exact one_pole_link_rotation z

theorem encodedRotation_fixes_pole (p : Fin 2) : encodedRotation (poleIndex p).val = (poleIndex p).val := by
  have hb : (poleIndex p).val < 524288 + suppliedModel.oriented.size := by
    simp only [poleIndex]
    split_ifs <;> omega
  rw [encodedRotation_step _ hb]
  fin_cases p <;> norm_num [poleIndex, encodedRotationStep, encodedRotationStepWith, regionStep, rotate]

/-- A concrete disk in the encoded realization, homeomorphic to the closed
unit disk through the previously proved cone construction. -/
def poleDiskHomeomorph (p : Fin 2) : ClosedDisk ≃ₜ
    range (Coordinates.linkConeParameter (encodedCells suppliedModel.oriented 524288)
      (poleIndex p).val (poleEncodedLinkCircle p)) :=
  Coordinates.linkConeDiskHomeomorph _ _ (poleEncodedLinkCircle p)

/-- This is an actual local conjugacy to a rigid Euclidean rotation of the
disk, including its center, with the generator angle ±2π/19. -/
theorem pole_disk_rotation_conjugacy (p : Fin 2) (z : ClosedDisk) :
    Coordinates.reindex encodedRotation (poleDiskHomeomorph p z).val =
      (poleDiskHomeomorph p (closedDiskRotation (Circle.exp (poleRotationAngle p)) z)).val :=
  Coordinates.linkConeDiskHomeomorph_rotation _ _ (poleEncodedLinkCircle p) encodedRotation
    (encodedRotation_fixes_pole p) _ (pole_encoded_link_rotation p) z

theorem pole_disk_mem_realization (p : Fin 2) (z : ClosedDisk) :
    (poleDiskHomeomorph p z).val ∈ Coordinates.realization (encodedCells suppliedModel.oriented 524288) := by
  obtain ⟨q, hq⟩ := (poleDiskHomeomorph p z).property
  rw [← hq]
  exact Coordinates.mix_mem_realization _ (poleEncodedLinkCircle p q.1).property
    q.2.property.1 q.2.property.2

/-- The local conjugating disk embedded into the original diagram. -/
def poleDiskDiagram (p : Fin 2) (z : ClosedDisk) : Diagram :=
  diagramEncodedHomeomorph.symm ⟨(poleDiskHomeomorph p z).val, pole_disk_mem_realization p z⟩

theorem poleDiskDiagram_continuous (p : Fin 2) : Continuous (poleDiskDiagram p) := by
  unfold poleDiskDiagram
  fun_prop

theorem poleDiskDiagram_injective (p : Fin 2) : Function.Injective (poleDiskDiagram p) := by
  intro z w h
  apply (poleDiskHomeomorph p).injective
  apply Subtype.ext
  simpa only [poleDiskDiagram, Homeomorph.apply_symm_apply] using
    congrArg (fun x : Diagram => (diagramEncodedHomeomorph x).val) h

theorem diagram_rotation_encoded (x : Diagram) :
    (diagramEncodedHomeomorph (diagramRotation x)).val =
      Coordinates.reindex encodedRotation (diagramEncodedHomeomorph x).val := by
  change Coordinates.reindex (Coordinates.labelEquiv 524288 suppliedModel.oriented.size)
      (Quad.coordinateHomeomorph diagramAutomorphism.labels x.val) =
    Coordinates.reindex encodedRotation
      (Coordinates.reindex (Coordinates.labelEquiv 524288 suppliedModel.oriented.size) x.val)
  ext j
  simp only [Coordinates.reindex_apply, Quad.coordinateHomeomorph, encodedRotation,
    Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  rfl

/-- The restriction of the actual diagram symmetry is conjugate to the rigid
disk rotation under an injective continuous parametrization. -/
theorem diagram_pole_disk_conjugacy (p : Fin 2) (z : ClosedDisk) :
    diagramRotation (poleDiskDiagram p z) =
      poleDiskDiagram p (closedDiskRotation (Circle.exp (poleRotationAngle p)) z) := by
  apply diagramEncodedHomeomorph.injective
  apply Subtype.ext
  rw [diagram_rotation_encoded]
  change Coordinates.reindex encodedRotation
      (diagramEncodedHomeomorph (diagramEncodedHomeomorph.symm _)).val =
    (diagramEncodedHomeomorph (diagramEncodedHomeomorph.symm _)).val
  simp only [Homeomorph.apply_symm_apply]
  exact pole_disk_rotation_conjugacy p z

def polePattern (p : Fin 2) : Fin 524288 := if p = 0 then 0 else 524287

theorem poleDiskDiagram_zero (p : Fin 2) :
    poleDiskDiagram p ⟨0, by simp⟩ = patternPoint (polePattern p) := by
  apply diagramEncodedHomeomorph.injective
  apply Subtype.ext
  simp only [poleDiskDiagram, Homeomorph.apply_symm_apply, patternPoint_encoded]
  have hz : (⟨0, by simp⟩ : ClosedDisk) = diskParameter (1, ⟨1, by norm_num⟩) := by
    apply Subtype.ext
    simp [diskParameter]
  rw [hz]
  simp only [poleDiskHomeomorph, Coordinates.linkConeDiskHomeomorph,
    compactParametrizationHomeomorph_apply, Coordinates.linkConeParameter, Coordinates.mix,
    one_smul, sub_self, zero_smul, add_zero]
  congr 1
  simp only [polePattern, poleIndex]
  split_ifs <;> rfl

/-- This disk is a neighborhood of the pole, not just an invariant embedded
circle or a disk somewhere else in the surface. -/
theorem pole_disk_range_mem_nhds (p : Fin 2) :
    range (poleDiskDiagram p) ∈ nhds (patternPoint (polePattern p)) := by
  let U : Set Diagram := {x | 0 < (diagramEncodedHomeomorph x).val (poleIndex p).val}
  have hU : IsOpen U := isOpen_lt continuous_const
    ((continuous_apply _).comp (continuous_subtype_val.comp diagramEncodedHomeomorph.continuous))
  have hp : patternPoint (polePattern p) ∈ U := by
    change 0 < (diagramEncodedHomeomorph (patternPoint (polePattern p))).val (poleIndex p).val
    rw [patternPoint_encoded]
    have he : (polePattern p).val = (poleIndex p).val := by
      simp only [polePattern, poleIndex]; split_ifs <;> rfl
    rw [he, Coordinates.vertex_self]
    norm_num
  apply Filter.mem_of_superset (hU.mem_nhds hp)
  intro x hx
  have hf : ∀ t i, i ∈ encodedCells suppliedModel.oriented 524288 t →
      ((encodedCells suppliedModel.oriented 524288 t).erase i).Nonempty := by
    intro t i hi
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hi, diagram_encoded_cell_card]
    decide
  have hh := Coordinates.openStar_eq_cone (encodedCells suppliedModel.oriented 524288)
    (poleIndex p).val hf (poleEncodedLinkCircle p)
  have hc : (diagramEncodedHomeomorph x).val ∈
      range (Coordinates.linkConeParameter (encodedCells suppliedModel.oriented 524288)
        (poleIndex p).val (poleEncodedLinkCircle p)) := by
    have hm : (diagramEncodedHomeomorph x).val ∈ Coordinates.openStar
        (encodedCells suppliedModel.oriented 524288) (poleIndex p).val :=
      ⟨(diagramEncodedHomeomorph x).property, hx⟩
    rw [hh] at hm
    exact hm.1
  obtain ⟨z, hz⟩ := (poleDiskHomeomorph p).surjective ⟨(diagramEncodedHomeomorph x).val, hc⟩
  refine ⟨z, ?_⟩
  apply diagramEncodedHomeomorph.injective
  apply Subtype.ext
  change (diagramEncodedHomeomorph (diagramEncodedHomeomorph.symm _)).val = _
  rw [Homeomorph.apply_symm_apply]
  have hv := congrArg Subtype.val hz
  exact hv

#print axioms diagram_pole_disk_conjugacy
#print axioms pole_disk_range_mem_nhds
#print axioms pole_disk_rotation_conjugacy
end Venn19.Topology
