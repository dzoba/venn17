import VennTopology.ArmSymmetry
import VennTopology.RegionSymmetry
import Mathlib.Data.Nat.Bitwise

namespace Venn19.Topology
open Set

/-- Character `i` moves to `i-1` modulo 19, as specified in the input. -/
def curveRotation : Equiv.Perm (Fin 19) := Equiv.addRight 18

@[simp] theorem curveRotation_val (i : Fin 19) :
    (curveRotation i).val = (i.val+18)%19 := rfl

theorem curve_rotation_period : ∀ i : Fin 19, curveRotation^[19] i = i := by decide

theorem bit_rotation_verified : ∀ (v : Fin 524288) (i : Fin 19),
    regionStep (v.val ^^^ 2^i.val) = regionStep v.val ^^^ 2^(curveRotation i).val := by
  native_decide

theorem rotated_edge_label {u v : Nat} (hu : u < 524288) (i : Fin 19) :
    u ^^^ v = 2^i.val ↔ regionStep u ^^^ regionStep v = 2^(curveRotation i).val := by
  have h (a b c : Nat) : a ^^^ b = c ↔ b = a ^^^ c := by
    constructor
    · intro he
      rw [← he, Nat.xor_xor_cancel_left]
    · intro he
      rw [he,Nat.xor_xor_cancel_left]
  rw [h,h,← bit_rotation_verified ⟨u,hu⟩ i]
  exact regionPermutation.injective.eq_iff.symm

attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons

theorem diagram_rotated_edge_label (f : Fin suppliedModel.oriented.size) (k : Fin 4) (i : Fin 19) :
    diagramQuad.corner f k ^^^ diagramQuad.corner f (Quad.next k) = 2^i.val ↔
      diagramQuad.corner (diagramAutomorphism.faces f) (diagramAutomorphism.corners f k) ^^^
        diagramQuad.corner (diagramAutomorphism.faces f) (Quad.next (diagramAutomorphism.corners f k)) =
          2^(curveRotation i).val := by
  rw [← diagramAutomorphism.next_eq,← diagramAutomorphism.corner_eq,← diagramAutomorphism.corner_eq]
  exact rotated_edge_label (cornersCheck_sound _ _ supplied_corners_bounded f k) i

/-- The periodic surface homeomorphism permutes the actual curve sets. -/
theorem diagram_rotation_mem_curve (x : Diagram) (i : Fin 19) :
    diagramRotation x ∈ diagramCurve (curveRotation i) ↔ x ∈ diagramCurve i := by
  rw [diagramCurve_original,diagramCurve_original]
  change Quad.coordinateHomeomorph diagramAutomorphism.labels x.val ∈ _ ↔ _
  rw [← diagramAutomorphism.edgeCurve_image i.val (curveRotation i).val
    (fun f k => diagram_rotated_edge_label f k i)]
  exact (Quad.coordinateHomeomorph _).injective.mem_set_image

theorem diagram_rotation_curve_image (i : Fin 19) :
    diagramRotation '' diagramCurve i = diagramCurve (curveRotation i) := by
  ext x
  obtain ⟨y,rfl⟩ := diagramRotation.surjective x
  rw [diagramRotation.injective.mem_set_image,diagram_rotation_mem_curve]

noncomputable def diagramCurveRotation (i : Fin 19) :
    diagramCurve i ≃ₜ diagramCurve (curveRotation i) :=
  diagramRotation.subtype (fun x => (diagram_rotation_mem_curve x i).symm)

#print axioms diagram_rotation_curve_image
end Venn19.Topology
