import VennTopology.Dataset
import VennTopology.Periodic

namespace Venn19.Topology

theorem supplied_rotation_verified : faceRotationCheck suppliedModel.oriented = true := by
  native_decide

theorem supplied_graph_size : suppliedModel.graph.size = 524288 := by native_decide

attribute [local irreducible] suppliedModel suppliedFaces

noncomputable def diagramAutomorphism : diagramQuad.Automorphism :=
  rotationAutomorphism suppliedModel.oriented supplied_rotation_verified

/-- A periodic homeomorphism of the explicit realization. This does not yet
assert conjugacy to a rotation of the sphere or Euclidean plane. -/
noncomputable def diagramRotation : Diagram ≃ₜ Diagram := diagramAutomorphism.homeomorph

theorem diagram_rotation_period (x : Diagram) : diagramRotation^[19] x = x :=
  diagramAutomorphism.homeomorph_period 19 region_period
    (face_period _ supplied_rotation_verified) x

noncomputable def patternPoint (v : Fin 524288) : Diagram := by
  refine ⟨Quad.point (.inl v.val), ?_⟩
  have h := supplied_incidence_verified
  simp only [suppliedIncidenceCheck, incidenceCheck, Bool.and_eq_true] at h
  exact coverageCheck_mem_space _ _ h.1.1.2 v.val (by rw [supplied_graph_size]; exact v.isLt)

theorem patternPoint_injective : Function.Injective patternPoint := by
  intro u v h
  have h := congrArg Subtype.val h
  have h := Quad.point_injective h
  exact Fin.ext (Sum.inl.inj h)

theorem diagram_rotation_pattern (n : Nat) (v : Fin 524288) :
    (diagramRotation^[n] (patternPoint v)).val =
      Quad.point (.inl (regionStep^[n] v.val)) := by
  rw [show diagramRotation = diagramAutomorphism.homeomorph from rfl,
    diagramAutomorphism.homeomorph_iterate_val]
  change (Quad.coordinateHomeomorph diagramAutomorphism.labels)^[n]
    (Quad.point (.inl v.val)) = _
  rw [Quad.coordinate_iterate_point, diagramAutomorphism.labels_iterate_inl]
  rfl

theorem region_no_short_period :
    ∀ k : Fin 19, k.val ≠ 0 → steps regionStep k.val 1 ≠ 1 := by decide

/-- The homeomorphism has exact order 19: every smaller positive power moves
the point carrying membership pattern 1. -/
theorem diagram_rotation_no_short_period (k : Nat) (hk : 0 < k) (hk17 : k < 19) :
    diagramRotation^[k] (patternPoint 1) ≠ patternPoint 1 := by
  intro he
  have he := congrArg Subtype.val he
  rw [diagram_rotation_pattern] at he
  change Quad.point (.inl (regionStep^[k] 1)) = Quad.point (.inl 1) at he
  have he := Sum.inl.inj (Quad.point_injective he)
  exact region_no_short_period ⟨k, hk17⟩ (Nat.ne_of_gt hk)
    ((steps_eq_iterate _ _ _).trans he)

theorem diagram_rotation_fixes_zero : diagramRotation (patternPoint 0) = patternPoint 0 := by
  apply Subtype.ext
  exact diagram_rotation_pattern 1 0

theorem diagram_rotation_fixes_one :
    diagramRotation (patternPoint 524287) = patternPoint 524287 := by
  apply Subtype.ext
  exact diagram_rotation_pattern 1 524287

theorem diagram_poles_distinct : patternPoint 0 ≠ patternPoint 524287 := by
  exact fun h => (by decide : (0 : Fin 524288) ≠ 524287) (patternPoint_injective h)

#print axioms diagram_rotation_period
#print axioms diagram_rotation_no_short_period
#print axioms diagram_rotation_fixes_zero
#print axioms diagram_rotation_fixes_one

end Venn19.Topology
