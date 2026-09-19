import VennTopology.SectorCertificate
import VennTopology.MeridianIntersections

/-! The certified face colors define actual closed pieces of the sphere.
Their cover, rotation, and boundary inclusions are geometric statements. -/
noncomputable section
namespace Venn17.Topology
open Set Coordinates
open scoped Classical
local instance : DecidableEq Nat := Classical.decEq _
attribute [local irreducible] suppliedModel suppliedFaces suppliedSectorColors suppliedSectorMasks

theorem sector_color_data (f : Fin suppliedModel.oriented.size) :
    suppliedSectorColors.getD f.val 17 < 17 ∧
    suppliedSectorColors.getD ((rotationWitnesses suppliedModel.oriented).getD f.val 0) 17 = (suppliedSectorColors.getD f.val 17 + 1) % 17 := by
  have hall := sector_colors_verified
  simp only [sectorColorCheck, Bool.and_eq_true] at hall
  have h := hall.2
  have hf := Array.all_eq_true.mp h f.val (by simp)
  simpa only [Array.getElem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using hf

def sectorColor (f : Fin suppliedModel.oriented.size) : Fin 17 :=
  ⟨suppliedSectorColors.getD f.val 17, (sector_color_data f).1⟩

theorem sectorColor_rotation (f : Fin suppliedModel.oriented.size) :
    sectorColor (diagramAutomorphism.faces f) = cyclicNext (sectorColor f) := by
  apply Fin.ext
  have h := (sector_color_data f).2
  change suppliedSectorColors.getD ((rotationWitnesses suppliedModel.oriented)[f.val]!) 17 = _
  simpa only [Array.getElem!_eq_getD, sectorColor, cyclicNext, show (default : Nat) = 0 from rfl] using h

def sectorSpace (k : Fin 17) : Set (Quad.Ambient Nat (Fin suppliedModel.oriented.size)) :=
  ⋃ f, ⋃ (_ : sectorColor f = k), ⋃ j, diagramQuad.triangle f j

def diagramSector (k : Fin 17) : Set Diagram := {x | x.val ∈ sectorSpace k}

def encodedSector (k : Fin 17) : Set (Point Nat) :=
  ⋃ t : Fin (4*suppliedModel.oriented.size), ⋃ (_ : sectorColor (triangleFace _ t) = k),
    simplex (encodedCells suppliedModel.oriented 131072 t)

theorem sectorSpace_subset_space (k : Fin 17) : sectorSpace k ⊆ diagramQuad.space := by
  intro x hx
  obtain ⟨f, _, j, hx⟩ := mem_iUnion.mp hx |>.imp (fun f => mem_iUnion₂.mp)
  exact diagramQuad.triangle_subset_space f j hx

theorem sectorSpace_compact (k : Fin 17) : IsCompact (sectorSpace k) :=
  isCompact_iUnion fun f => isCompact_iUnion fun _ => isCompact_iUnion fun j =>
    diagramQuad.triangle_compact f j

theorem diagramSector_closed (k : Fin 17) : IsClosed (diagramSector k) :=
  (sectorSpace_compact k).isClosed.preimage continuous_subtype_val

theorem diagramSector_compact (k : Fin 17) : IsCompact (diagramSector k) :=
  (diagramSector_closed k).isCompact

theorem diagram_sectors_cover : (⋃ k, diagramSector k) = Set.univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨f, j, hx⟩ := mem_iUnion.mp x.property |>.imp (fun _ => mem_iUnion.mp)
  exact mem_iUnion.mpr ⟨sectorColor f, mem_iUnion.mpr ⟨f, mem_iUnion₂.mpr ⟨rfl, j, hx⟩⟩⟩

theorem sector_encoded_image (k : Fin 17) :
    reindex (labelEquiv 131072 suppliedModel.oriented.size) '' sectorSpace k = encodedSector k := by
  simp only [sectorSpace, image_iUnion, Quad.triangle_eq_simplex, reindex_simplex]
  ext x
  simp only [encodedSector, mem_iUnion]
  constructor
  · rintro ⟨f, hf, j, hx⟩
    obtain ⟨t, ht⟩ := triangleFaceCorner_surjective suppliedModel.oriented (f,j)
    have he := congrArg Prod.fst ht
    dsimp only at he
    refine ⟨t, by rw [he]; exact hf, ?_⟩
    rw [← ht] at hx
    exact (cellLabels_encoded _ _ supplied_corners_bounded t) ▸ hx
  · rintro ⟨t, ht, hx⟩
    refine ⟨triangleFace _ t, ht, triangleCorner _ t, ?_⟩
    exact (cellLabels_encoded _ _ supplied_corners_bounded t).symm ▸ hx

theorem mem_diagramSector_iff_encoded (k : Fin 17) (x : Diagram) :
    x ∈ diagramSector k ↔ (diagramEncodedHomeomorph x).val ∈ encodedSector k := by
  rw [← sector_encoded_image]
  change x.val ∈ sectorSpace k ↔ reindex (labelEquiv 131072 suppliedModel.oriented.size) x.val ∈ _
  exact (reindex _).injective.mem_set_image.symm

theorem cyclicNext_injective {n : Nat} : Function.Injective (cyclicNext (n := n)) := by
  intro i j h
  have he := congrArg Fin.val h
  simp only [cyclicNext_val] at he
  apply Fin.ext
  split_ifs at he <;> omega

theorem sectorSpace_rotation (k : Fin 17) :
    Quad.coordinateHomeomorph diagramAutomorphism.labels '' sectorSpace k = sectorSpace (cyclicNext k) := by
  simp only [sectorSpace, image_iUnion, diagramAutomorphism.triangle_image]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨f, hf, j, hx⟩
    exact ⟨diagramAutomorphism.faces f, by rw [sectorColor_rotation, hf], _, hx⟩
  · rintro ⟨f, hf, j, hx⟩
    let g := diagramAutomorphism.faces.symm f
    have hg : sectorColor g = k := by
      apply cyclicNext_injective
      rw [← sectorColor_rotation]
      simpa only [g, Equiv.apply_symm_apply] using hf
    refine ⟨g, hg, (diagramAutomorphism.corners g).symm j, ?_⟩
    simpa only [g, Equiv.apply_symm_apply] using hx

theorem diagram_sector_rotation (k : Fin 17) :
    diagramRotation '' diagramSector k = diagramSector (cyclicNext k) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change Quad.coordinateHomeomorph diagramAutomorphism.labels y.val ∈ sectorSpace _
    rw [← sectorSpace_rotation]
    exact mem_image_of_mem _ hy
  · intro hx
    change x.val ∈ sectorSpace _ at hx
    rw [← sectorSpace_rotation] at hx
    obtain ⟨y, hy, he⟩ := hx
    exact ⟨⟨y, sectorSpace_subset_space k hy⟩, hy, Subtype.ext he⟩

theorem sector_boundary_subset (k : Fin 17) : diagramMeridianBoundary k (cyclicNext k) ⊆ diagramSector k := by
  intro x hx
  rw [mem_diagramSector_iff_encoded]
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  obtain ⟨ht, hk, he⟩ := sector_boundary_verified k j
  let t : Fin (4*suppliedModel.oriented.size) := ⟨sectorBoundaryTriangle _ k j, ht⟩
  refine mem_iUnion₂.mpr ⟨t, Fin.ext hk, ?_⟩
  have h1 := vertex_mem_simplex (show LinkProof.triangleVertex suppliedModel.oriented
    131072 t.val 1 ∈ encodedCells suppliedModel.oriented 131072 t by simp [encodedCells])
  have h2 := vertex_mem_simplex (show LinkProof.triangleVertex suppliedModel.oriented
    131072 t.val 2 ∈ encodedCells suppliedModel.oriented 131072 t by simp [encodedCells])
  rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [show t.val = sectorBoundaryTriangle _ k j from rfl, ha] at h1
    rw [show t.val = sectorBoundaryTriangle _ k j from rfl, hb] at h2
    exact (convex_convexHull ℝ _).segment_subset h1 h2 hj
  · rw [show t.val = sectorBoundaryTriangle _ k j from rfl, ha] at h1
    rw [show t.val = sectorBoundaryTriangle _ k j from rfl, hb] at h2
    exact (convex_convexHull ℝ _).segment_subset h2 h1 hj

theorem diagramSector_nonempty (k : Fin 17) : (diagramSector k).Nonempty := by
  refine ⟨patternPoint 0, sector_boundary_subset k ?_⟩
  rw [diagram_meridian_boundary_eq_union]
  left
  rw [← diagramMeridianMap_range]
  exact ⟨⟨0, by norm_num⟩, diagramMeridianMap_zero k⟩

#print axioms diagram_sectors_cover
#print axioms diagram_sector_rotation
#print axioms sector_boundary_subset
end Venn17.Topology
