import VennTopology.SectorGeometry

/-! Certificate soundness for geometric sector overlaps. Shared points are
proved to lie on the designated meridian boundaries, including edge interiors. -/
noncomputable section
namespace Venn17.Topology
open Set Coordinates
open scoped Classical
local instance : DecidableEq Nat := Classical.decEq _
attribute [local irreducible] suppliedModel suppliedFaces suppliedSectorColors suppliedSectorMasks

namespace Coordinates

theorem simplex_of_support {I : Type*} {s t : Finset I} {x : Point I}
    (hx : x ∈ simplex s) (hz : ∀ a ∉ t, x a = 0) : x ∈ simplex t := by
  classical
  apply mem_simplex_iff.mpr
  refine ⟨simplex_nonneg hx, ?_, hz⟩
  have hs : ∑ a ∈ s ∩ t, x a = 1 := by
    rw [Finset.sum_subset Finset.inter_subset_left]
    · exact simplex_sum hx
    · intro a ha hn
      exact hz a (fun ht => hn (Finset.mem_inter.mpr ⟨ha, ht⟩))
  rw [← hs]
  symm
  apply Finset.sum_subset Finset.inter_subset_right
  intro a ha hn
  exact simplex_zero hx (fun ht => hn (Finset.mem_inter.mpr ⟨ht, ha⟩))

end Coordinates

theorem sector_corner_support (f : Fin suppliedModel.oriented.size) (i : Fin 4) :
    let v := (suppliedModel.oriented.getD f.val #[]).getD i.val 0
    v < 131072 ∧ (suppliedSectorMasks.getD v 0).testBit (sectorColor f).val = true := by
  have h := Array.all_eq_true.mp sector_corners_verified f.val (by simp)
  have h := Array.all_eq_true.mp h i.val (by simp)
  simpa only [Array.getElem_range, Bool.and_eq_true, decide_eq_true_eq, sectorColor] using h

def sectorAllowed (k : Fin 17) (a : Nat) : Prop :=
  (a < 131072 ∧ (suppliedSectorMasks.getD a 0).testBit k.val = true) ∨
  ∃ f : Fin suppliedModel.oriented.size, a = 131072 + f.val ∧ sectorColor f = k

theorem encodedSector_positive_allowed (k : Fin 17) {x : Point Nat}
    (hx : x ∈ encodedSector k) {a : Nat} (ha : 0 < x a) : sectorAllowed k a := by
  obtain ⟨t, ht, hx⟩ := mem_iUnion₂.mp hx
  have hm : a ∈ encodedCells suppliedModel.oriented 131072 t := by
    by_contra hn
    rw [simplex_zero hx hn] at ha
    exact lt_irrefl _ ha
  simp only [encodedCells, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · right
    exact ⟨triangleFace _ t, triangleVertex_zero _ _ _, ht⟩
  · left
    have h := sector_corner_support (triangleFace _ t) (triangleCorner _ t)
    dsimp only at h
    rw [ht] at h
    simpa [LinkProof.triangleVertex, triangleFace, triangleCorner] using h
  · left
    have h := sector_corner_support (triangleFace _ t) (Quad.next (triangleCorner _ t))
    dsimp only at h
    rw [ht] at h
    simpa [LinkProof.triangleVertex, triangleFace, triangleCorner, Quad.next, Nat.mod_add_mod] using h

theorem sector_overlap_edge (t : Fin (4*suppliedModel.oriented.size)) (l : Fin 17)
    (hkl : sectorColor (triangleFace _ t) ≠ l) :
    ∃ j : Fin 34,
      let a := meridianBoundaryLabel (sectorColor (triangleFace _ t))
        (cyclicNext (sectorColor (triangleFace _ t))) j
      let b := meridianBoundaryLabel (sectorColor (triangleFace _ t))
        (cyclicNext (sectorColor (triangleFace _ t))) (cyclicNext j)
      ((suppliedSectorMasks.getD (LinkProof.triangleVertex suppliedModel.oriented 131072 t.val 1) 0).testBit l.val = true →
        LinkProof.triangleVertex suppliedModel.oriented 131072 t.val 1 = a ∨
        LinkProof.triangleVertex suppliedModel.oriented 131072 t.val 1 = b) ∧
      ((suppliedSectorMasks.getD (LinkProof.triangleVertex suppliedModel.oriented 131072 t.val 2) 0).testBit l.val = true →
        LinkProof.triangleVertex suppliedModel.oriented 131072 t.val 2 = a ∨
        LinkProof.triangleVertex suppliedModel.oriented 131072 t.val 2 = b) := by
  have hf := Array.all_eq_true.mp sector_overlaps_verified (t.val/4) (by simp; omega)
  have hi := Array.all_eq_true.mp hf (t.val%4) (by simp; omega)
  have hl := Array.all_eq_true.mp hi l.val (by simp)
  simp only [Array.getElem_range, Bool.or_eq_true, beq_iff_eq] at hl
  rcases hl with he | hl
  · exact (hkl (Fin.ext he.symm)).elim
  obtain ⟨j, hj, he⟩ := Array.any_eq_true.mp hl
  have hj' : j < 34 := by simpa using hj
  refine ⟨⟨j, hj'⟩, ?_⟩
  have hrow (i : Fin 34) :
      (sectorBoundaryRows.getD (sectorColor (triangleFace _ t)).val #[]).getD i.val 0 =
      meridianBoundaryLabel (sectorColor (triangleFace _ t))
        (cyclicNext (sectorColor (triangleFace _ t))) i := by
    simp [sectorBoundaryRows, Array.getD]
  simp only [Array.getElem_range,
    show suppliedSectorColors.getD (t.val/4) 17 = (sectorColor (triangleFace _ t)).val from rfl,
    hrow ⟨j, hj'⟩, hrow ⟨(j+1)%34, Nat.mod_lt _ (by decide)⟩, Bool.and_eq_true] at he
  constructor
  · intro hm
    simp [LinkProof.triangleVertex] at hm
    simpa [LinkProof.triangleVertex, cyclicNext, hm] using he.1
  · intro hm
    simp [LinkProof.triangleVertex] at hm
    simpa [LinkProof.triangleVertex, cyclicNext, hm, Nat.mod_add_mod] using he.2

theorem sector_inter_subset_boundary (k l : Fin 17) (hkl : k ≠ l) :
    diagramSector k ∩ diagramSector l ⊆ diagramMeridianBoundary k (cyclicNext k) := by
  intro x hx
  have hk := (mem_diagramSector_iff_encoded k x).mp hx.1
  have hl := (mem_diagramSector_iff_encoded l x).mp hx.2
  obtain ⟨t, ht, hx⟩ := mem_iUnion₂.mp hk
  obtain ⟨j, hj⟩ := sector_overlap_edge t l (ht ▸ hkl)
  rw [ht] at hj
  change (diagramEncodedHomeomorph x).val ∈ labeledPolygon _
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  have hz (a : Nat) (ha : a ∉ ({meridianBoundaryLabel k (cyclicNext k) j,
      meridianBoundaryLabel k (cyclicNext k) (cyclicNext j)} : Finset Nat)) :
      (diagramEncodedHomeomorph x).val a = 0 := by
    by_contra hn
    have hp : 0 < (diagramEncodedHomeomorph x).val a :=
      lt_of_le_of_ne (simplex_nonneg hx a) (Ne.symm hn)
    have hm : a ∈ encodedCells suppliedModel.oriented 131072 t := by
      by_contra hm
      exact hn (simplex_zero hx hm)
    have hs := encodedSector_positive_allowed l hl hp
    simp only [encodedCells, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · rw [triangleVertex_zero] at hs
      rcases hs with ⟨hb, _⟩ | ⟨f, he, hf⟩
      · omega
      · have heq : triangleFace suppliedModel.oriented t = f := Fin.ext (by omega)
        exact hkl (ht.symm.trans (heq ▸ hf))
    · have hu := (sector_corner_support (triangleFace _ t) (triangleCorner _ t)).1
      have hb : LinkProof.triangleVertex suppliedModel.oriented 131072 t.val 1 < 131072 := by
        simpa [LinkProof.triangleVertex, triangleFace, triangleCorner] using hu
      have hm := hs.resolve_right (by rintro ⟨f, he, _⟩; omega)
      exact ha (by simpa using hj.1 hm.2)
    · have hu := (sector_corner_support (triangleFace _ t) (Quad.next (triangleCorner _ t))).1
      have hb : LinkProof.triangleVertex suppliedModel.oriented 131072 t.val 2 < 131072 := by
        simpa [LinkProof.triangleVertex, triangleFace, triangleCorner, Quad.next, Nat.mod_add_mod] using hu
      have hm := hs.resolve_right (by rintro ⟨f, he, _⟩; omega)
      exact ha (by simpa using hj.2 hm.2)
  have he := simplex_of_support hx hz
  simpa [simplex, image_insert_eq, image_singleton, convexHull_pair] using he

#print axioms sector_inter_subset_boundary
end Venn17.Topology
