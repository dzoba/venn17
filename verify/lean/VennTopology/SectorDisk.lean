import VennTopology.SectorFrontier
import VennTopology.JordanDisk
import VennTopology.PlaneRealization

/-! Each actual closed sector is a disk. The disk chart sends its explicitly
parametrized meridian boundary to the corresponding standard-circle point,
so adjacent sector boundaries can be matched in the eventual gluing. -/
noncomputable section
namespace Venn17.Topology
open Set
attribute [local irreducible] suppliedModel suppliedFaces suppliedSectorColors suppliedSectorMasks

/-- A stereographic chart deleting any selected point of the proved sphere. -/
def diagramPuncturedAtHomeomorph (p : Diagram) : {x : Diagram // x ≠ p} ≃ₜ Plane :=
  (diagramSphereHomeomorph.subtype (fun _ => not_congr diagramSphereHomeomorph.injective.eq_iff.symm)).trans
    (sphereWithoutPointHomeomorph (diagramSphereHomeomorph p))

def sectorBoundaryParam (k : Fin 17) : UnitCircle → Diagram :=
  diagramMeridianBoundaryMap k (Coordinates.cyclicNext k) ∘ JordanCurve.Arcs.spherePlaneHomeoCircle

theorem sectorBoundaryParam_continuous (k : Fin 17) : Continuous (sectorBoundaryParam k) :=
  (diagramMeridianBoundaryMap_continuous _ _).comp JordanCurve.Arcs.spherePlaneHomeoCircle.continuous

theorem sectorBoundaryParam_injective (k : Fin 17) : Function.Injective (sectorBoundaryParam k) :=
  (diagramMeridianBoundaryMap_injective _ _ (Coordinates.cyclicNext_ne (by decide) k).symm).comp
    JordanCurve.Arcs.spherePlaneHomeoCircle.injective

theorem sectorBoundaryParam_range (k : Fin 17) :
    range (sectorBoundaryParam k) = diagramMeridianBoundary k (Coordinates.cyclicNext k) := by
  rw [sectorBoundaryParam, Set.range_comp, JordanCurve.Arcs.spherePlaneHomeoCircle.surjective.range_eq,
    image_univ, diagramMeridianBoundaryMap_range]

theorem sectorBoundaryParam_subset (k : Fin 17) : range (sectorBoundaryParam k) ⊆ diagramSector k := by
  rw [sectorBoundaryParam_range]
  exact sector_boundary_subset k

theorem sectorBoundaryParam_frontier (k : Fin 17) : frontier (diagramSector k) ⊆ range (sectorBoundaryParam k) := by
  rw [sectorBoundaryParam_range]
  exact sector_frontier_subset k

theorem sector_interior_witness (k : Fin 17) :
    ∃ x ∈ interior (diagramSector k), x ∉ range (sectorBoundaryParam k) := by
  obtain ⟨f, hf⟩ := sector_face_exists k
  have hn := crossingPoint_not_meridian_boundary f k (Coordinates.cyclicNext k)
  refine ⟨crossingPoint f, ?_, ?_⟩
  · exact (sectorCore_open k).subset_interior_iff.mpr (sectorCore_subset k)
      (sector_diff_boundary_subset_core k ⟨(crossingPoint_mem_sector_iff f k).mpr hf, hn⟩)
  · simpa only [sectorBoundaryParam_range] using hn

/-- An actual homeomorphism of each sector onto the closed Euclidean unit disk. -/
def sectorDiskHomeomorph (k : Fin 17) : diagramSector k ≃ₜ PlaneClosedDisk :=
  puncturedJordanDisk (sectorOutsidePoint k) (diagramPuncturedAtHomeomorph (sectorOutsidePoint k))
    (diagramSector k) (diagramSector_compact k) (sectorOutsidePoint_not_mem k)
    (sectorBoundaryParam k) (sectorBoundaryParam_continuous k) (sectorBoundaryParam_injective k)
    (sectorBoundaryParam_subset k) (sectorBoundaryParam_frontier k) (sector_interior_witness k)

/-- Boundary matching is part of the construction, rather than an additional
assumption about the chosen disk homeomorphisms. -/
theorem sectorDiskHomeomorph_boundary (k : Fin 17) (z : UnitCircle) :
    (sectorDiskHomeomorph k
      ⟨sectorBoundaryParam k z, sectorBoundaryParam_subset k (mem_range_self z)⟩).val = z.val :=
  puncturedJordanDisk_boundary _ _ _ _ _ _ _ _ _ _ _ z

theorem diagram_sectors_are_closed_disks :
    ∀ k : Fin 17, Nonempty (diagramSector k ≃ₜ PlaneClosedDisk) :=
  fun k => ⟨sectorDiskHomeomorph k⟩

#print axioms sectorDiskHomeomorph
#print axioms sectorDiskHomeomorph_boundary
#print axioms diagram_sectors_are_closed_disks
end Venn17.Topology
