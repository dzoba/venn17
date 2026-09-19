import VennTopology.FixedPoints

namespace Venn17.Topology

theorem diagram_triangles_nondegenerate (f : Fin suppliedModel.oriented.size) (k : Fin 4) :
    (diagramQuad.triangleFinset f k).card = 3 :=
  diagramQuad.triangle_card f k (diagram_corners_injective f)

/-- The initial geometric certificate. `realized_surface_verified` extends this
with the proved surface structure; sphere and planar-curve assertions remain open. -/
theorem realized_candidate_verified :
    CompactSpace Diagram ∧ T2Space Diagram ∧ PathConnectedSpace Diagram ∧
    diagramQuad.complex.faces.Finite ∧ diagramQuad.complex.space = diagramQuad.space ∧
    (∀ f k, (diagramQuad.triangleFinset f k).card = 3) ∧
    (∀ x : Diagram, diagramRotation^[17] x = x) ∧
    (∀ k : Nat, 0 < k → k < 17 → ∃ x : Diagram, diagramRotation^[k] x ≠ x) ∧
    (∀ x : Diagram, diagramRotation x = x ↔ x = patternPoint 0 ∨ x = patternPoint 131071) := by
  refine ⟨diagram_compact, diagram_hausdorff, inferInstance,
    diagramQuad.complex_faces_finite, diagramQuad.complex_space,
    diagram_triangles_nondegenerate, diagram_rotation_period, ?_, diagram_rotation_fixed_iff⟩
  intro k hk hk17
  exact ⟨patternPoint 1, diagram_rotation_no_short_period k hk hk17⟩

#print axioms realized_candidate_verified

end Venn17.Topology
