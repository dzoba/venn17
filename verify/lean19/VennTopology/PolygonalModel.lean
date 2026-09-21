import VennTopology.TriangulationIncidence
import ClassificationOfSurfaces.GeometricTriangulationRealization

/-! The polygonal presentation below is geometrically tied to the original
diagram by an actual homeomorphism. Its sides are paired from triangle-edge
incidence, not from an arbitrary abstract surface model. -/

noncomputable section
namespace Venn19.Topology
open LeanEval.Topology.ClassificationOfSurfaces
open scoped Classical
attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars suppliedCurvePolygons

def diagramPresentation : FiniteCyclicPresentation :=
  diagramFiniteTriangulation.toFiniteCyclicPresentation

theorem diagram_presentation_valid : diagramPresentation.IsSurfaceValid :=
  diagramFiniteTriangulation.toFiniteCyclicPresentation_isSurfaceValid
    diagram_finite_surface_incidence

theorem diagram_presentation_connected : diagramPresentation.IsConnected :=
  diagramFiniteTriangulation.toFiniteCyclicPresentation_isConnected
    diagram_finite_surface_incidence

/-- A finite union of polygonal disks with the prescribed side identifications
is homeomorphic to the previously verified geometric diagram. -/
def diagramPolygonalHomeomorph :
    diagramPresentation.PolygonalRealization diagram_presentation_valid ≃ₜ Diagram :=
  (diagramFiniteTriangulation.polygonalRealizationHomeomorph
    diagram_presentation_valid diagram_finite_vertex_stars_connected).trans
      diagramFiniteTriangulation.homeo

theorem diagram_presentation_edge_count : diagramPresentation.edgeCount = 3145716 := by
  change Fintype.card diagramFiniteTriangulation.Edge = _
  rw [Fintype.card_coe]
  exact diagram_finite_edge_count

theorem diagram_presentation_face_count : diagramPresentation.faces.length = 2097144 := by
  have h := diagramFiniteTriangulation.toFiniteSurfaceTriangulation.toFiniteCyclicPresentation_faces_length
  change diagramPresentation.faces.length = Fintype.card diagramFiniteTriangulation.Triangle at h
  rw [Fintype.card_coe] at h
  exact h.trans diagram_finite_triangle_count

/-- Boundary occurrences of an edge are in bijection with its incident
triangles, since a triangle traverses each of its three edges exactly once. -/
def geometricEdgeOccurrenceEquiv {S : Type*} [TopologicalSpace S]
    (T : GeometricTriangulation S) (e : T.Edge) :
    {o : T.toFiniteSurfaceTriangulation.BoundaryPosition // o.edge = e} ≃
      {f : T.Triangle // e.val ⊆ f.val} :=
  Equiv.ofBijective (fun o => ⟨o.val.1, by
    have h := T.edge_subset_of_mem_triangleBoundary
      (List.get_mem (T.triangleBoundary o.val.1) o.val.2)
    change o.val.edge.val ⊆ o.val.1.val at h
    simpa only [o.property] using h⟩) (by
    constructor
    · rintro ⟨⟨f, i⟩, hi⟩ ⟨⟨g, j⟩, hj⟩ h
      have hfg : f = g := congrArg Subtype.val h
      subst g
      have hij : i = j := T.triangleBoundary_edge_get_injective f (hi.trans hj.symm)
      subst j
      rfl
    · rintro ⟨f, hf⟩
      have hm := (T.mem_map_edge_triangleBoundary_iff f e).mpr hf
      obtain ⟨oe, ho, he⟩ := List.mem_map.mp hm
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp ho
      refine ⟨⟨⟨f, i⟩, ?_⟩, rfl⟩
      change ((T.triangleBoundary f).get i).edge = e
      exact (congrArg OrientedEdge.edge hi).trans he)

theorem geometric_edge_occurrence_count {S : Type*} [TopologicalSpace S]
    (T : GeometricTriangulation S) (e : T.Edge) :
    T.toFiniteSurfaceTriangulation.edgeOccurrenceCount e =
      (T.faces.filter (fun f => e.val ⊆ f)).card := by
  classical
  have h := Fintype.card_congr (geometricEdgeOccurrenceEquiv T e)
  have he : Fintype.card {f : T.Triangle // e.val ⊆ f.val} =
      (T.faces.filter (fun f => e.val ⊆ f)).card := by
    let equiv : {f : T.Triangle // e.val ⊆ f.val} ≃
        {f // f ∈ T.faces.filter (fun f => e.val ⊆ f)} :=
      { toFun := fun f => ⟨f.val.val, Finset.mem_filter.mpr ⟨f.val.property, f.property⟩⟩
        invFun := fun f => ⟨⟨f.val, (Finset.mem_filter.mp f.property).1⟩,
          (Finset.mem_filter.mp f.property).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Fintype.card_congr equiv).trans (Fintype.card_coe _)
  have hleft : Fintype.card {o : T.toFiniteSurfaceTriangulation.BoundaryPosition // o.edge = e} =
      T.toFiniteSurfaceTriangulation.edgeOccurrenceCount e := by
    simp [FiniteSurfaceTriangulation.edgeOccurrenceCount, Fintype.card_subtype]
  exact hleft.symm.trans (h.trans he)

theorem diagram_presentation_edge_multiplicity (e : diagramPresentation.Edge) :
    diagramPresentation.edgeMultiplicity e = 2 := by
  let T := diagramFiniteTriangulation.toFiniteSurfaceTriangulation
  obtain ⟨e', rfl⟩ := T.finiteCyclicEdgeEquiv.surjective e
  exact (T.toFiniteCyclicPresentation_edgeMultiplicity e').trans
    ((geometric_edge_occurrence_count diagramFiniteTriangulation e').trans
      (diagram_finite_no_boundary_edges e'))

#print axioms diagramPolygonalHomeomorph
#print axioms diagram_presentation_edge_multiplicity
end Venn19.Topology
