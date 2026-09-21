import VennTopology.GeometricCounting

namespace Venn19.Topology

/-- A direct input-size certificate. All simplex counts below follow from
geometric bijections, not from a second enumeration of a drawing. -/
theorem supplied_oriented_face_count : suppliedModel.oriented.size = 524286 := by
  native_decide

noncomputable section
attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars

/-- The alternating simplex count of the realized two-dimensional complex.
`geometric_no_higher_faces` proves that higher-dimensional terms are absent. -/
def geometricEulerCharacteristic {V F : Type*} (q : Quad V F) : ℤ :=
  (Nat.card (GeometricFace q 1) : ℤ) - Nat.card (GeometricFace q 2) + Nat.card (GeometricFace q 3)

theorem diagram_geometric_vertex_count : Nat.card (GeometricFace diagramQuad 1) = 1048574 := by
  have h := geometric_vertex_count suppliedModel.oriented 524288 supplied_corners_bounded supplied_region_coverage
  exact h.trans (by rw [supplied_oriented_face_count])

theorem diagram_geometric_edge_count : Nat.card (GeometricFace diagramQuad 2) = 3145716 := by
  have h := geometric_edge_count suppliedModel.oriented 524288 suppliedLinkStars
    supplied_corners_bounded supplied_distinct_corners_verified
    (Bool.and_eq_true_iff.mp supplied_link_stars_verified).1
    (Bool.and_eq_true_iff.mp supplied_link_stars_verified).2
  exact h.trans (by rw [supplied_oriented_face_count])

theorem diagram_geometric_triangle_count : Nat.card (GeometricFace diagramQuad 3) = 2097144 := by
  have h := geometric_triangle_count suppliedModel.oriented 524288
    supplied_corners_bounded supplied_distinct_corners_verified
  exact h.trans (by rw [supplied_oriented_face_count])

/-- Euler characteristic two for the concrete geometric triangulation.
Identifying the resulting compact surface with a sphere is still a separate
classification or constructive-homeomorphism theorem. -/
theorem diagram_euler_characteristic : geometricEulerCharacteristic diagramQuad = 2 := by
  rw [geometricEulerCharacteristic,diagram_geometric_vertex_count,
    diagram_geometric_edge_count,diagram_geometric_triangle_count]
  norm_num

theorem diagram_triangulation_counts_verified :
    Nat.card (GeometricFace diagramQuad 1) = 1048574 ∧
    Nat.card (GeometricFace diagramQuad 2) = 3145716 ∧
    Nat.card (GeometricFace diagramQuad 3) = 2097144 ∧
    (∀ k : Nat, 3 < k → IsEmpty (GeometricFace diagramQuad k)) ∧
    geometricEulerCharacteristic diagramQuad = 2 :=
  ⟨diagram_geometric_vertex_count,diagram_geometric_edge_count,diagram_geometric_triangle_count,
    geometric_no_higher_faces diagramQuad,diagram_euler_characteristic⟩

#print axioms diagram_triangulation_counts_verified
end
end Venn19.Topology
