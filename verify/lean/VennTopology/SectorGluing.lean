import VennTopology.SectorConjugacy
import VennTopology.RigidSectorIntersections
import Schoenflies.FiniteClosedCoverHomeomorph

/-! Reduction of the global sphere conjugacy to equality of boundary parameters.
This file proves the conditional gluing theorem. `RigidSphereConjugacy` proves
its compatibility hypothesis and constructs the unconditional global conjugacy. -/
noncomputable section
namespace Venn17.Topology
open Set Coordinates LeanEval.Topology.ClassificationOfSurfaces
attribute [local irreducible] suppliedModel suppliedFaces suppliedSectorColors suppliedSectorMasks
attribute [local irreducible] sectorConjugacy

/-- Boundary compatibility compares the actual constructed maps. -/
def SectorBoundaryCompatibility : Prop :=
  ∀ (k l : Fin 17) (z w : UnitCircle),
    sectorBoundaryParam k z = sectorBoundaryParam l w ↔
      rigidSectorParam k z = rigidSectorParam l w

theorem sectorConjugacy_agrees (h : SectorBoundaryCompatibility) (k l : Fin 17)
    (x : Diagram) (hk : x ∈ diagramSector k) (hl : x ∈ diagramSector l) :
    (sectorConjugacy k ⟨x, hk⟩).val = (sectorConjugacy l ⟨x, hl⟩).val := by
  by_cases he : k = l
  · subst l; rfl
  have hb := sector_inter_subset_boundary k l he ⟨hk, hl⟩
  rw [← sectorBoundaryParam_range] at hb
  obtain ⟨z, hz⟩ := hb
  have hb' := sector_inter_subset_boundary l k (Ne.symm he) ⟨hl, hk⟩
  rw [← sectorBoundaryParam_range] at hb'
  obtain ⟨w, hw⟩ := hb'
  have hv := (h k l z w).mp (hz.trans hw.symm)
  have hk' : (sectorConjugacy k ⟨x, hk⟩).val = rigidSectorParam k z := by
    cases hz; exact sectorConjugacy_boundary k z
  have hl' : (sectorConjugacy l ⟨x, hl⟩).val = rigidSectorParam l w := by
    cases hw; exact sectorConjugacy_boundary l w
  exact hk'.trans (hv.trans hl'.symm)

theorem sectorConjugacy_symm_agrees (h : SectorBoundaryCompatibility) (k l : Fin 17)
    (y : SphereRepresentative) (hk : y ∈ rigidSector k) (hl : y ∈ rigidSector l) :
    ((sectorConjugacy k).symm ⟨y, hk⟩).val = ((sectorConjugacy l).symm ⟨y, hl⟩).val := by
  by_cases he : k = l
  · subst l; rfl
  obtain ⟨z, hz⟩ := rigid_sector_inter_subset_boundary k l he ⟨hk, hl⟩
  obtain ⟨w, hw⟩ := rigid_sector_inter_subset_boundary l k (Ne.symm he) ⟨hl, hk⟩
  have hv := (h k l z w).mpr (hz.trans hw.symm)
  have hk' : ((sectorConjugacy k).symm ⟨y, hk⟩).val = sectorBoundaryParam k z := by
    cases hz; exact sectorConjugacy_symm_boundary k z
  have hl' : ((sectorConjugacy l).symm ⟨y, hl⟩).val = sectorBoundaryParam l w := by
    cases hw; exact sectorConjugacy_symm_boundary l w
  exact hk'.trans (hv.trans hl'.symm)

/-- Closed-cover gluing, continuity, bijectivity, and global equivariance follow
from the single stated compatibility condition. No global homeomorphism is assumed. -/
theorem sphere_conjugacy_of_boundary_compatibility (h : SectorBoundaryCompatibility) :
    ∃ H : Diagram ≃ₜ SphereRepresentative,
      (∀ k x (hx : x ∈ diagramSector k), H x = (sectorConjugacy k ⟨x, hx⟩).val) ∧
      (∀ x, H (diagramRotation x) = rigidSphereRotation rigidGenerator (H x)) := by
  let u : Finset (Fin 17) := Finset.univ
  let S := Schoenflies.FiniteClosedCoverHomeomorph.cover u diagramSector
  let T := Schoenflies.FiniteClosedCoverHomeomorph.cover u rigidSector
  have hS : S = univ := by
    simpa [S, u, Schoenflies.FiniteClosedCoverHomeomorph.cover] using diagram_sectors_cover
  have hT : T = univ := by
    simpa [T, u, Schoenflies.FiniteClosedCoverHomeomorph.cover] using rigid_sectors_cover
  obtain ⟨E, hE⟩ := Schoenflies.FiniteClosedCoverHomeomorph.exists_glue
    u diagramSector rigidSector (fun k _ => diagramSector_closed k) (fun k _ => rigidSector_closed k)
    sectorConjugacy (fun k _ l _ x hk hl => sectorConjugacy_agrees h k l x hk hl)
    (fun k _ l _ y hk hl => sectorConjugacy_symm_agrees h k l y hk hl)
  let H : Diagram ≃ₜ SphereRepresentative :=
    (Homeomorph.Set.univ Diagram).symm.trans
      ((Homeomorph.setCongr hS.symm).trans
        (E.trans ((Homeomorph.setCongr hT).trans (Homeomorph.Set.univ SphereRepresentative))))
  have hv (k : Fin 17) (x : Diagram) (hx : x ∈ diagramSector k) :
      H x = (sectorConjugacy k ⟨x, hx⟩).val :=
    hE k (Finset.mem_univ k) x hx
  refine ⟨H, hv, ?_⟩
  intro x
  have hx : x ∈ ⋃ k, diagramSector k := by rw [diagram_sectors_cover]; trivial
  obtain ⟨k, hk⟩ := mem_iUnion.mp hx
  have hr : diagramRotation x ∈ diagramSector (cyclicNext k) := (sectorRotatePoint k ⟨x, hk⟩).property
  rw [hv k x hk, hv (cyclicNext k) (diagramRotation x) hr]
  exact sectorConjugacy_rotation k ⟨x, hk⟩

end Venn17.Topology
