import VennTopology.MeridianCertificate
import VennTopology.PoleDiskRotation

/-! Explicit Jordan boundaries for the rotation sectors, in the original
surface. Each boundary follows one pole-to-pole meridian and returns along
another. No assertion that the enclosed sectors are disks is assumed here. -/
noncomputable section
namespace Venn19.Topology
open Set Coordinates
open scoped Classical
local instance : DecidableEq Nat := Classical.decEq _
attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars

namespace Coordinates

theorem reindex_relabel {I : Type*} {n : Nat} (e : Equiv.Perm I)
    (v : Fin n → I) (x : Point (Fin n)) :
    reindex e (relabel v x) = relabel (e ∘ v) x := by
  ext j
  simp [reindex_apply, relabel, vertex, e.symm_apply_eq]

theorem reindex_labeledPolygonMap {I : Type*} {n : Nat} (e : Equiv.Perm I)
    (v : Fin n → I) (hn : 3 ≤ n) (z : Circle) :
    reindex e (labeledPolygonMap v hn z) = labeledPolygonMap (e ∘ v) hn z :=
  reindex_relabel e v _

end Coordinates

theorem meridianBoundaryLabel_rotation (k l : Fin 19) (j : Fin 38) :
    encodedRotation (meridianBoundaryLabel k l j) =
      meridianBoundaryLabel (cyclicNext k) (cyclicNext l) j := by
  have hr (k : Fin 19) (i : Fin 20) :
      encodedRotation (meridianLabel k i) = meridianLabel (cyclicNext k) i := by
    have hb := (meridian_labels_verified.2.1 k i).1
    rw [encodedRotation_step _ (by omega)]
    simpa only [encodedRotationStep, encodedRotationStepWith, if_pos hb] using
      (meridian_labels_verified.2.1 k i).2
  unfold meridianBoundaryLabel
  split <;> exact hr _ _

theorem meridian_boundary_subset_realization (k l : Fin 19) :
    labeledPolygon (meridianBoundaryLabel k l) ⊆
      Coordinates.realization (encodedCells suppliedModel.oriented 524288) := by
  intro x hx
  obtain ⟨j, hx⟩ := mem_iUnion.mp hx
  obtain ⟨ht, he⟩ := meridian_triangles_verified k l j
  let t : Fin (4 * suppliedModel.oriented.size) := ⟨meridianBoundaryTriangle suppliedModel.oriented k l j, ht⟩
  apply mem_iUnion.mpr
  refine ⟨t, ?_⟩
  have h1 := vertex_mem_simplex (show LinkProof.triangleVertex suppliedModel.oriented
    524288 t.val 1 ∈ encodedCells suppliedModel.oriented 524288 t by simp [encodedCells])
  have h2 := vertex_mem_simplex (show LinkProof.triangleVertex suppliedModel.oriented
    524288 t.val 2 ∈ encodedCells suppliedModel.oriented 524288 t by simp [encodedCells])
  rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [show t.val = meridianBoundaryTriangle suppliedModel.oriented k l j from rfl, ha] at h1
    rw [show t.val = meridianBoundaryTriangle suppliedModel.oriented k l j from rfl, hb] at h2
    exact (convex_convexHull ℝ _).segment_subset h1 h2 hx
  · rw [show t.val = meridianBoundaryTriangle suppliedModel.oriented k l j from rfl, ha] at h1
    rw [show t.val = meridianBoundaryTriangle suppliedModel.oriented k l j from rfl, hb] at h2
    exact (convex_convexHull ℝ _).segment_subset h2 h1 hx

/-- The closed curve made from two meridians, as a subset of the actual sphere. -/
def diagramMeridianBoundary (k l : Fin 19) : Set Diagram :=
  {x | (diagramEncodedHomeomorph x).val ∈ labeledPolygon (meridianBoundaryLabel k l)}

def diagramMeridianBoundaryMap (k l : Fin 19) (z : Circle) : Diagram :=
  diagramEncodedHomeomorph.symm ⟨labeledPolygonMap (meridianBoundaryLabel k l) (by decide) z,
    meridian_boundary_subset_realization k l (by
      rw [← range_labeledPolygonMap _ (by decide)]
      exact mem_range_self z)⟩

theorem diagramMeridianBoundaryMap_continuous (k l : Fin 19) :
    Continuous (diagramMeridianBoundaryMap k l) :=
  diagramEncodedHomeomorph.symm.continuous.comp
    ((continuous_labeledPolygonMap _ _).subtype_mk _)

theorem diagramMeridianBoundaryMap_injective (k l : Fin 19) (hkl : k ≠ l) :
    Function.Injective (diagramMeridianBoundaryMap k l) := by
  intro z w h
  apply labeledPolygonMap_injective _ (meridian_labels_verified.2.2 k l hkl) (by decide)
  have he := congrArg (fun x : Diagram => (diagramEncodedHomeomorph x).val) h
  simpa only [diagramMeridianBoundaryMap, Homeomorph.apply_symm_apply] using he

theorem diagramMeridianBoundaryMap_range (k l : Fin 19) :
    range (diagramMeridianBoundaryMap k l) = diagramMeridianBoundary k l := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change (diagramEncodedHomeomorph (diagramEncodedHomeomorph.symm _)).val ∈
      labeledPolygon (meridianBoundaryLabel k l)
    simp only [Homeomorph.apply_symm_apply]
    rw [← range_labeledPolygonMap _ (by decide)]
    exact mem_range_self z
  · intro hx
    change (diagramEncodedHomeomorph x).val ∈ labeledPolygon _ at hx
    rw [← range_labeledPolygonMap _ (by decide)] at hx
    obtain ⟨z, hz⟩ := hx
    refine ⟨z, diagramEncodedHomeomorph.injective (Subtype.ext ?_)⟩
    simpa only [diagramMeridianBoundaryMap, Homeomorph.apply_symm_apply] using hz

/-- Any two distinct meridians form an embedded circle on the proved sphere. -/
theorem diagram_meridian_boundaries_are_circles (k l : Fin 19) (hkl : k ≠ l) :
    ∃ f : Circle → Diagram, Continuous f ∧ Function.Injective f ∧
      range f = diagramMeridianBoundary k l :=
  ⟨diagramMeridianBoundaryMap k l, diagramMeridianBoundaryMap_continuous k l,
    diagramMeridianBoundaryMap_injective k l hkl, diagramMeridianBoundaryMap_range k l⟩

/-- The boundary parametrizations themselves respect the actual symmetry. -/
theorem diagramMeridianBoundaryMap_rotation (k l : Fin 19) (z : Circle) :
    diagramRotation (diagramMeridianBoundaryMap k l z) =
      diagramMeridianBoundaryMap (cyclicNext k) (cyclicNext l) z := by
  apply diagramEncodedHomeomorph.injective
  apply Subtype.ext
  rw [diagram_rotation_encoded]
  simp only [diagramMeridianBoundaryMap, Homeomorph.apply_symm_apply]
  rw [reindex_labeledPolygonMap]
  congr 2
  funext j
  exact meridianBoundaryLabel_rotation k l j

theorem diagram_meridian_boundary_rotation (k l : Fin 19) :
    diagramRotation '' diagramMeridianBoundary k l =
      diagramMeridianBoundary (cyclicNext k) (cyclicNext l) := by
  rw [← diagramMeridianBoundaryMap_range, ← diagramMeridianBoundaryMap_range, ← range_comp]
  congr 1
  funext z
  exact diagramMeridianBoundaryMap_rotation k l z

#print axioms diagram_meridian_boundaries_are_circles
#print axioms diagram_meridian_boundary_rotation
end Venn19.Topology
