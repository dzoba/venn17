import VennTopology.PolygonVertices
import VennTopology.PolygonalModel

/-! Polygon endpoint classes map onto the geometric triangulation vertices.
This gives the lower bound needed for the genus-zero argument, without
requiring injectivity of the vertex map. -/

noncomputable section
namespace Venn17.Topology.PolygonVertices
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation

def geometricDartVertex {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)
    (d : T.toFiniteCyclicPresentation.Dart) : T.Vertex :=
  T.orientedEdgeSource (T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv.symm d)

theorem geometricDartVertex_map {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)
    (d : OrientedEdge T.Edge) :
    geometricDartVertex T (T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv d) =
      T.orientedEdgeSource d := by simp [geometricDartVertex]

theorem geometricDartVertex_flip_map {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)
    (d : OrientedEdge T.Edge) :
    geometricDartVertex T (T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv d).flip =
      T.orientedEdgeTarget d := by
  have he : (T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv d).flip =
      T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv d.flip := by cases d <;> rfl
  rw [he, geometricDartVertex_map]
  cases d <;> rfl

theorem geometricDartVertex_corner {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)
    (o : T.toFiniteCyclicPresentation.BoundaryOccurrence) :
    geometricDartVertex T o.dart.flip = geometricDartVertex T (next o).dart := by
  rcases o with ⟨f, i⟩
  obtain ⟨f, rfl⟩ := T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv.surjective f
  dsimp only [FiniteCyclicPresentation.BoundaryOccurrence.dart, next]
  rw [T.toFiniteSurfaceTriangulation.toFiniteCyclicPresentation_boundary_faceEquiv_get,
    T.toFiniteSurfaceTriangulation.toFiniteCyclicPresentation_boundary_faceEquiv_get,
    geometricDartVertex_flip_map, geometricDartVertex_map]
  dsimp only [GeometricTriangulation.toFiniteSurfaceTriangulation]
  rw [T.triangleBoundary_get_target, T.triangleBoundary_get_source]
  congr 1
  have hlen : (T.toFiniteCyclicPresentation.boundary
      (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f)).length = 3 :=
    (T.toFiniteSurfaceTriangulation.toFiniteCyclicPresentation_boundary_faceEquiv_length f).trans
      (T.triangleBoundary_length f)
  apply Fin.ext
  change (i.val + 1) % 3 = (i.val + 1) %
    (T.toFiniteCyclicPresentation.boundary (T.toFiniteSurfaceTriangulation.finiteCyclicFaceEquiv f)).length
  exact congrArg (fun n => (i.val + 1) % n) hlen.symm

/-- Corner identifications never merge different geometric vertices. -/
def geometricVertexMap {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S) :
    Vertex T.toFiniteCyclicPresentation → T.Vertex :=
  Quot.lift (geometricDartVertex T) (by
    rintro a b ⟨o, rfl, rfl⟩
    exact geometricDartVertex_corner T o)

theorem geometricVertexMap_surjective {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)
    (hcover : ∀ v : T.Vertex, ∃ f : T.Triangle, v ∈ f.val) :
    Function.Surjective (geometricVertexMap T) := by
  intro v
  obtain ⟨f, hv⟩ := hcover v
  obtain ⟨j, hj⟩ := (T.toIntrinsic.faceVertexEquiv f).surjective ⟨v, hv⟩
  let i : Fin (T.triangleBoundary f).length := Fin.cast (T.triangleBoundary_length f).symm j
  let d := (T.triangleBoundary f).get i
  refine ⟨endpoint _ (T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv d), ?_⟩
  change geometricDartVertex T (T.toFiniteSurfaceTriangulation.finiteCyclicDartEquiv d) = v
  rw [geometricDartVertex_map, T.triangleBoundary_get_source]
  simpa [Moise.IntrinsicTwoComplex.faceVertex, i] using congrArg Subtype.val hj

theorem geometric_vertex_count_le {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)
    (hcover : ∀ v : T.Vertex, ∃ f : T.Triangle, v ∈ f.val) :
    Nat.card T.Vertex ≤ Nat.card (Vertex T.toFiniteCyclicPresentation) :=
  Nat.card_le_card_of_surjective (geometricVertexMap T) (geometricVertexMap_surjective T hcover)

attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars suppliedCurvePolygons

theorem diagram_finite_vertices_covered (v : diagramFiniteTriangulation.Vertex) :
    ∃ f : diagramFiniteTriangulation.Triangle, v ∈ f.val := by
  obtain ⟨t, ht⟩ := (encoded_vertex_mem_iff _ _ supplied_corners_bounded
    supplied_region_coverage v.val).mpr v.isLt
  refine ⟨⟨Coordinates.FiniteCoordinates.cell (131072 + suppliedModel.oriented.size)
    (encodedCells suppliedModel.oriented 131072 t), ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  · exact Coordinates.FiniteCoordinates.mem_cell.mpr ht

theorem diagram_polygon_vertex_count_lower_bound : 262142 ≤ Nat.card (Vertex diagramPresentation) := by
  have h := geometric_vertex_count_le diagramFiniteTriangulation diagram_finite_vertices_covered
  rw [Nat.card_eq_fintype_card, diagram_finite_vertex_count] at h
  exact h

/-- Enough for the sphere criterion once this Euler count is proved invariant
along the stored normalization trace. That invariance is not assumed here. -/
theorem diagram_polygon_euler_lower_bound : 2 ≤ eulerCharacteristic diagramPresentation := by
  have hv := diagram_polygon_vertex_count_lower_bound
  simp only [eulerCharacteristic, diagram_presentation_edge_count, diagram_presentation_face_count]
  omega

#print axioms geometric_vertex_count_le
#print axioms diagram_polygon_euler_lower_bound
end Venn17.Topology.PolygonVertices
