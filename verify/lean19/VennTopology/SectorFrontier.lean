import VennTopology.SectorIntersections
import VennTopology.SectorConnected
import VennTopology.CurveIntersections

/-! The closed pieces have nonempty interior and frontier contained in their
specified Jordan boundary. Each has an explicit point outside it, so it can
be placed compactly in a stereographic plane for Schoenflies. -/
noncomputable section
namespace Venn19.Topology
open Set Coordinates
attribute [local irreducible] suppliedModel suppliedFaces suppliedSectorColors suppliedSectorMasks

def sectorCore (k : Fin 19) : Set Diagram := (⋃ l, ⋃ (_ : l ≠ k), diagramSector l)ᶜ

theorem sectorCore_open (k : Fin 19) : IsOpen (sectorCore k) :=
  (isClosed_iUnion_of_finite fun l => isClosed_iUnion_of_finite fun _ => diagramSector_closed l).isOpen_compl

theorem sectorCore_subset (k : Fin 19) : sectorCore k ⊆ diagramSector k := by
  intro x hx
  have hc : x ∈ ⋃ l, diagramSector l := by rw [diagram_sectors_cover]; trivial
  obtain ⟨l, hl⟩ := mem_iUnion.mp hc
  by_cases he : l = k
  · exact he ▸ hl
  · exact (hx (mem_iUnion₂.mpr ⟨l, he, hl⟩)).elim

theorem sector_diff_boundary_subset_core (k : Fin 19) :
    diagramSector k \ diagramMeridianBoundary k (cyclicNext k) ⊆ sectorCore k := by
  rintro x ⟨hx, hn⟩ hm
  obtain ⟨l, hl, hx'⟩ := mem_iUnion₂.mp hm
  exact hn (sector_inter_subset_boundary k l hl.symm ⟨hx, hx'⟩)

theorem sector_frontier_subset (k : Fin 19) :
    frontier (diagramSector k) ⊆ diagramMeridianBoundary k (cyclicNext k) := by
  intro x hx
  have hm : x ∈ diagramSector k := by
    simpa only [(diagramSector_closed k).closure_eq] using hx.1
  by_contra hn
  exact hx.2 ((sectorCore_open k).subset_interior_iff.mpr (sectorCore_subset k)
    (sector_diff_boundary_subset_core k ⟨hm, hn⟩))

theorem meridianBoundaryLabel_lt (k l : Fin 19) (i : Fin 38) : meridianBoundaryLabel k l i < 524288 := by
  unfold meridianBoundaryLabel
  split <;> exact (meridian_labels_verified.2.1 _ _).1

theorem meridian_boundary_center_zero (k l : Fin 19) {x : Diagram}
    (hx : x ∈ diagramMeridianBoundary k l) (a : Nat) (ha : 524288 ≤ a) :
    (diagramEncodedHomeomorph x).val a = 0 := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  have hs : (diagramEncodedHomeomorph x).val ∈
      simplex {meridianBoundaryLabel k l i, meridianBoundaryLabel k l (cyclicNext i)} := by
    simpa [simplex, image_insert_eq, image_singleton, convexHull_pair] using hi
  apply simplex_zero hs
  have h1 := meridianBoundaryLabel_lt k l i
  have h2 := meridianBoundaryLabel_lt k l (cyclicNext i)
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem crossingPoint_not_meridian_boundary (f : Fin suppliedModel.oriented.size) (k l : Fin 19) :
    crossingPoint f ∉ diagramMeridianBoundary k l := by
  intro hx
  have h := meridian_boundary_center_zero k l hx (524288+f.val) (by omega)
  rw [crossingPoint_encoded, vertex_self] at h
  norm_num at h

theorem crossingPoint_mem_sector_iff (f : Fin suppliedModel.oriented.size) (k : Fin 19) :
    crossingPoint f ∈ diagramSector k ↔ sectorColor f = k := by
  constructor
  · intro hx
    have he := encodedSector_positive_allowed k ((mem_diagramSector_iff_encoded k _).mp hx)
      (a := 524288+f.val) (by rw [crossingPoint_encoded, vertex_self]; norm_num)
    rcases he with ⟨hb, _⟩ | ⟨g, hg, hk⟩
    · omega
    · have hfg : f = g := Fin.ext (by omega)
      exact hfg ▸ hk
  · intro hf
    exact sector_triangle_subset k f hf 0 (diagramQuad.center_mem_triangle f 0)

theorem sector_face_exists (k : Fin 19) : ∃ f, sectorColor f = k := by
  obtain ⟨root, hr, ha, _⟩ := GraphProof.connectedCheck_sound _ _ (sector_connected_verified k)
  rw [sector_dual_size] at hr
  exact ⟨⟨root, hr⟩, Fin.ext (beq_iff_eq.mp ha)⟩

theorem sector_interior_nonempty (k : Fin 19) : (interior (diagramSector k)).Nonempty := by
  obtain ⟨f, hf⟩ := sector_face_exists k
  refine ⟨crossingPoint f, (sectorCore_open k).subset_interior_iff.mpr (sectorCore_subset k) ?_⟩
  exact sector_diff_boundary_subset_core k ⟨(crossingPoint_mem_sector_iff f k).mpr hf,
    crossingPoint_not_meridian_boundary f _ _⟩

def sectorOutsidePoint (k : Fin 19) : Diagram :=
  crossingPoint (Classical.choose (sector_face_exists (cyclicNext k)))

theorem sectorOutsidePoint_not_mem (k : Fin 19) : sectorOutsidePoint k ∉ diagramSector k := by
  rw [sectorOutsidePoint, crossingPoint_mem_sector_iff,
    Classical.choose_spec (sector_face_exists (cyclicNext k))]
  exact cyclicNext_ne (by decide) k

#print axioms sector_frontier_subset
#print axioms sector_interior_nonempty
#print axioms sectorOutsidePoint_not_mem
end Venn19.Topology
