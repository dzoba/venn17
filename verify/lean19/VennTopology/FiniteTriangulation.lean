import VennTopology.FiniteRealization
import VennTopology.EulerCharacteristic
import VennTopology.DiagramCurves

/-! A concrete finite barycentric triangulation of the verified diagram, in
the representation of the surface-classification library. -/

noncomputable section
namespace Venn19.Topology
open Set
open scoped Classical
open Coordinates
open Coordinates.FiniteCoordinates
open LeanEval.Topology.ClassificationOfSurfaces (GeometricTriangulation)

local instance finiteTriangulationFinDecidableEq (N : Nat) : DecidableEq (Fin N) :=
  Classical.decEq _

variable {T : Type*} [Fintype T]

def finiteTriangulation (cells : T → Finset Nat) (N : Nat)
    (hb : ∀ t i, i ∈ cells t → i < N) (hc : ∀ t, (cells t).card = 3) :
    GeometricTriangulation (Coordinates.realization cells) where
  Vertex := Fin N
  faces := geometricFaces (fun t => cell N (cells t))
  faces_card := by
    intro s hs
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
    exact (cell_card (hb t)).trans (hc t)
  homeo := (Homeomorph.setCongr
    (realization_eq_geometricRealization (fun t => cell N (cells t))).symm).trans
      (FiniteCoordinates.homeomorph cells N hb).symm

/-- Every lower-dimensional face is preserved by the coordinate restriction,
not just the ambient surface's homeomorphism type. -/
def finiteCellFaceEquiv (cells : T → Finset Nat) (N : Nat)
    (hb : ∀ t i, i ∈ cells t → i < N) (k : Nat) :
    CellFace (fun t => cell N (cells t)) k ≃ CellFace cells k :=
  (cellFaceMapEquiv _ Fin.valEmbedding k).trans
    (cellFaceCongr _ cells k (fun s => by simp only [map_cell (hb _)]))

def finiteTriangulationEdgeEquiv (cells : T → Finset Nat) (N : Nat)
    (hb : ∀ t i, i ∈ cells t → i < N) (hc : ∀ t, (cells t).card = 3) :
    (finiteTriangulation cells N hb hc).Edge ≃ CellFace cells 2 :=
  (Equiv.subtypeEquivRight (fun s => by
    classical
    change s ∈ (geometricFaces (fun t => cell N (cells t))).biUnion
      (fun t => t.powersetCard 2) ↔ s.card = 2 ∧ ∃ t, s ⊆ cell N (cells t)
    constructor
    · intro hs
      obtain ⟨f, hf, hfs⟩ := Finset.mem_biUnion.mp hs
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
      exact ⟨(Finset.mem_powersetCard.mp hfs).2, t, (Finset.mem_powersetCard.mp hfs).1⟩
    · rintro ⟨hk, t, hs⟩
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩,
        Finset.mem_powersetCard.mpr ⟨hs, hk⟩⟩)).trans (finiteCellFaceEquiv cells N hb 2)

theorem finiteTriangulation_faces_card (cells : T → Finset Nat) (N : Nat)
    (hb : ∀ t i, i ∈ cells t → i < N) (hc : ∀ t, (cells t).card = 3)
    (hi : Function.Injective cells) :
    (finiteTriangulation cells N hb hc).faces.card = Fintype.card T := by
  change (Finset.univ.image (fun t => cell N (cells t))).card = _
  rw [Finset.card_image_of_injective, Finset.card_univ]
  intro t u h
  apply hi
  have hh := congrArg (Finset.map Fin.valEmbedding) h
  simpa only [map_cell (hb _)] using hh

attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars suppliedCurvePolygons

theorem diagram_cells_bounded (t : Fin (4 * suppliedModel.oriented.size)) (i : Nat)
    (hi : i ∈ encodedCells suppliedModel.oriented 524288 t) :
    i < 524288 + suppliedModel.oriented.size :=
  (encoded_vertex_mem_iff _ _ supplied_corners_bounded supplied_region_coverage i).mp ⟨t, hi⟩

theorem diagram_encoded_cell_card (t : Fin (4 * suppliedModel.oriented.size)) :
    (encodedCells suppliedModel.oriented 524288 t).card = 3 :=
  encoded_cell_card _ _ (triangleVertices_injective _ _
    supplied_corners_bounded supplied_distinct_corners_verified) t

/-- The actual diagram, equipped with a finite barycentric triangulation.
The homeomorphism is the proved coordinate restriction, not a classification
assumption or an arbitrary realization field. -/
def diagramFiniteTriangulation : GeometricTriangulation Diagram :=
  let tr := finiteTriangulation (encodedCells suppliedModel.oriented 524288)
    (524288 + suppliedModel.oriented.size) diagram_cells_bounded diagram_encoded_cell_card
  { tr with homeo := tr.homeo.trans diagramEncodedHomeomorph.symm }

theorem diagram_finite_vertex_count :
    Fintype.card diagramFiniteTriangulation.Vertex = 1048574 := by
  change Fintype.card (Fin (524288 + suppliedModel.oriented.size)) = _
  rw [Fintype.card_fin, supplied_oriented_face_count]

theorem diagram_finite_edge_count : diagramFiniteTriangulation.edges.card = 3145716 := by
  have h := Nat.card_congr (finiteTriangulationEdgeEquiv
    (encodedCells suppliedModel.oriented 524288) (524288 + suppliedModel.oriented.size)
    diagram_cells_bounded diagram_encoded_cell_card)
  have he := encoded_edge_count suppliedModel.oriented 524288 suppliedLinkStars
    (Bool.and_eq_true_iff.mp supplied_link_stars_verified).1
    (Bool.and_eq_true_iff.mp supplied_link_stars_verified).2
    (triangleVertices_injective _ _ supplied_corners_bounded supplied_distinct_corners_verified)
  change Nat.card diagramFiniteTriangulation.Edge = _ at h
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at h
  exact h.trans (he.trans (by rw [supplied_oriented_face_count]))

theorem diagram_finite_triangle_count : diagramFiniteTriangulation.faces.card = 2097144 := by
  have h := finiteTriangulation_faces_card (encodedCells suppliedModel.oriented 524288)
    (524288 + suppliedModel.oriented.size) diagram_cells_bounded diagram_encoded_cell_card
    (encoded_cells_injective _ _ supplied_corners_bounded supplied_distinct_corners_verified)
  exact h.trans (by rw [Fintype.card_fin, supplied_oriented_face_count])

/-- Euler characteristic two expressed using the external library's own
vertex, edge, and triangle sets. This still requires a genus/classification
argument to construct a sphere homeomorphism. -/
theorem diagram_finite_euler_characteristic :
    (Fintype.card diagramFiniteTriangulation.Vertex : ℤ) -
      diagramFiniteTriangulation.edges.card + diagramFiniteTriangulation.faces.card = 2 := by
  rw [diagram_finite_vertex_count, diagram_finite_edge_count, diagram_finite_triangle_count]
  norm_num

#print axioms diagramFiniteTriangulation
#print axioms diagram_finite_euler_characteristic
end Venn19.Topology
