import VennTopology.Surface
import VennTopology.EulerCharacteristic

namespace Venn17.Topology

/-- The verified geometric conclusion: a compact connected surface with the
certified simplicial realization of Euler characteristic two and a
two-fixed-point action of exact order 17.
This theorem makes no unproved sphere or planar Jordan-curve assertion. -/
theorem realized_surface_verified :
    CompactSpace Diagram ∧ T2Space Diagram ∧ SecondCountableTopology Diagram ∧
    PathConnectedSpace Diagram ∧ Nonempty (ChartedSpace ℂ Diagram) ∧
    diagramQuad.complex.faces.Finite ∧ diagramQuad.complex.space = diagramQuad.space ∧
    (∀ f k, (diagramQuad.triangleFinset f k).card = 3) ∧
    (∀ x : Diagram, diagramRotation^[17] x = x) ∧
    (∀ k : Nat, 0 < k → k < 17 → ∃ x : Diagram, diagramRotation^[k] x ≠ x) ∧
    (∀ x : Diagram, diagramRotation x = x ↔ x = patternPoint 0 ∨ x = patternPoint 131071) ∧
    geometricEulerCharacteristic diagramQuad = 2 := by
  refine ⟨diagram_compact, diagram_hausdorff, diagram_second_countable, inferInstance,
    ⟨diagramChartedSpace⟩, diagramQuad.complex_faces_finite, diagramQuad.complex_space,
    diagram_triangles_nondegenerate, diagram_rotation_period, ?_, diagram_rotation_fixed_iff,
    diagram_euler_characteristic⟩
  intro k hk hk17
  exact ⟨patternPoint 1, diagram_rotation_no_short_period k hk hk17⟩

#print axioms realized_surface_verified

end Venn17.Topology
