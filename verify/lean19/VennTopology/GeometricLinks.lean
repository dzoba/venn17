import VennTopology.EncodedLinks
import VennTopology.CoordinateRelabel

noncomputable section
namespace Venn19.Topology
open Set
open scoped Classical
local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- The finite encoding preserves the actual three vertex labels of each triangle. -/
theorem cellLabels_encoded (fs : Array Face) (n : Nat) (hc : cornersCheck fs n = true)
    (t : Fin (4*fs.size)) :
    ((quadOfFaces fs).cellLabels (triangleFace fs t, triangleCorner fs t)).map
      (Coordinates.labelEquiv n fs.size).toEmbedding = encodedCells fs n t := by
  have h1 := cornersCheck_sound fs n hc (triangleFace fs t) (triangleCorner fs t)
  have h2 := cornersCheck_sound fs n hc (triangleFace fs t) (Quad.next (triangleCorner fs t))
  simp only [Quad.cellLabels, encodedCells, triangleVertex_zero, triangleVertex_one,
    triangleVertex_two, Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding,
    Coordinates.labelEquiv_face, Coordinates.labelEquiv_region n fs.size _ h1,
    Coordinates.labelEquiv_region n fs.size _ h2]
  ext x
  simp

theorem triangleFaceCorner_surjective (fs : Array Face) (p : Fin fs.size × Fin 4) :
    ∃ t : Fin (4*fs.size), (triangleFace fs t, triangleCorner fs t) = p := by
  refine ⟨⟨4*p.1.val+p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩, ?_⟩
  apply Prod.ext <;> apply Fin.ext <;> dsimp [triangleFace, triangleCorner] <;> omega

theorem encoded_geometric_link (fs : Array Face) (n : Nat) (hc : cornersCheck fs n = true)
    (a : Nat ⊕ Fin fs.size) :
    Coordinates.reindex (Coordinates.labelEquiv n fs.size) '' (quadOfFaces fs).geometricLink a =
      Coordinates.link (encodedCells fs n) (Coordinates.labelEquiv n fs.size a) := by
  rw [Quad.geometricLink, Coordinates.reindex_link]
  ext x
  simp only [Coordinates.link, mem_iUnion]
  constructor
  · rintro ⟨p, ha, hx⟩
    obtain ⟨t, rfl⟩ := triangleFaceCorner_surjective fs p
    rw [cellLabels_encoded fs n hc] at ha hx
    exact ⟨t, ha, hx⟩
  · rintro ⟨t, ha, hx⟩
    refine ⟨(triangleFace fs t, triangleCorner fs t), ?_, ?_⟩
    · simpa only [cellLabels_encoded fs n hc] using ha
    · simpa only [cellLabels_encoded fs n hc] using hx

def geometricLinkDartHomeomorph (fs : Array Face) (n : Nat)
    (hc : cornersCheck fs n = true) (hd : distinctCornersCheck fs = true)
    (a : Nat ⊕ Fin fs.size) :
    (quadOfFaces fs).geometricLink a ≃ₜ dartLink fs n (Coordinates.labelEquiv n fs.size a) :=
  ((Coordinates.reindex (Coordinates.labelEquiv n fs.size)).image _).trans
    (Homeomorph.setCongr ((encoded_geometric_link fs n hc a).trans
      (encoded_link_eq_dartLink fs n _ (triangleVertices_injective fs n hc hd))))

attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars

theorem supplied_corners_bounded : cornersCheck suppliedModel.oriented 524288 = true := by
  have h := supplied_incidence_verified
  simp only [suppliedIncidenceCheck, incidenceCheck, Bool.and_eq_true] at h
  simpa only [supplied_graph_size] using h.1.1.1

/-- The geometric links of all active vertices in the original realization
are topological circles. This includes region vertices and face centers. -/
def diagram_geometric_link_circle (a : Nat ⊕ Fin suppliedModel.oriented.size)
    (ha : Coordinates.labelEquiv 524288 suppliedModel.oriented.size a < suppliedLinkStars.size) :
    Circle ≃ₜ diagramQuad.geometricLink a :=
  (supplied_dart_link_circle ⟨_, ha⟩).trans
    (geometricLinkDartHomeomorph suppliedModel.oriented 524288
      supplied_corners_bounded supplied_distinct_corners_verified a).symm

/-- Each punctured open vertex star is an actual annulus. -/
def diagram_punctured_star_annulus (a : Nat ⊕ Fin suppliedModel.oriented.size)
    (ha : Coordinates.labelEquiv 524288 suppliedModel.oriented.size a < suppliedLinkStars.size) :
    {x : Quad.Ambient Nat (Fin suppliedModel.oriented.size) |
      x ∈ diagramQuad.space ∧ 0 < x a ∧ x a < 1} ≃ₜ (Circle × Ioo (0 : ℝ) 1) :=
  (diagram_punctured_star_homeomorph a).trans
    (Homeomorph.prodCongr (diagram_geometric_link_circle a ha).symm (Homeomorph.refl _))

#print axioms diagram_geometric_link_circle
#print axioms diagram_punctured_star_annulus
end Venn19.Topology
