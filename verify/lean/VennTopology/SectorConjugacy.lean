import VennTopology.EquivariantSectorDisk
import VennTopology.RigidSectorDisk

/-! Actual homeomorphisms from every source sector to the corresponding
Euclidean spherical sector. They preserve the specified boundary parameters
and intertwine the diagram symmetry with the rigid rotation. Gluing these
maps across their shared boundaries is a separate remaining obligation. -/
noncomputable section
namespace Venn17.Topology
open Set Coordinates

/-- The source and target disk coordinates define an actual sector homeomorphism. -/
def sectorConjugacy (k : Fin 17) : diagramSector k ≃ₜ rigidSector k :=
  (equivariantSectorDisk k).trans (equivariantRigidSectorDisk k).symm

theorem sectorConjugacy_coordinates (k : Fin 17) (x : diagramSector k) :
    equivariantRigidSectorDisk k (sectorConjugacy k x) = equivariantSectorDisk k x :=
  (equivariantRigidSectorDisk k).apply_symm_apply _

theorem sectorConjugacy_boundary (k : Fin 17) (z : UnitCircle) :
    (sectorConjugacy k
      ⟨sectorBoundaryParam k z, sectorBoundaryParam_subset k (mem_range_self z)⟩).val =
      rigidSectorParam k z := by
  have hc : equivariantSectorDisk k
      ⟨sectorBoundaryParam k z, sectorBoundaryParam_subset k (mem_range_self z)⟩ =
      equivariantRigidSectorDisk k
        ⟨rigidSectorParam k z, rigidSectorParam_subset k (mem_range_self z)⟩ := by
    apply Subtype.ext
    rw [equivariantSectorDisk_boundary, equivariantRigidSectorDisk_boundary]
  change ((equivariantRigidSectorDisk k).symm (equivariantSectorDisk k _)).val = _
  rw [hc, Homeomorph.symm_apply_apply]

theorem sectorConjugacy_symm_boundary (k : Fin 17) (z : UnitCircle) :
    ((sectorConjugacy k).symm
      ⟨rigidSectorParam k z, rigidSectorParam_subset k (mem_range_self z)⟩).val =
      sectorBoundaryParam k z := by
  have he : sectorConjugacy k
      ⟨sectorBoundaryParam k z, sectorBoundaryParam_subset k (mem_range_self z)⟩ =
      ⟨rigidSectorParam k z, rigidSectorParam_subset k (mem_range_self z)⟩ :=
    Subtype.ext (sectorConjugacy_boundary k z)
  rw [← he, Homeomorph.symm_apply_apply]

theorem sectorConjugacy_rotation (k : Fin 17) (x : diagramSector k) :
    (sectorConjugacy (cyclicNext k) (sectorRotatePoint k x)).val =
      rigidSphereRotation rigidGenerator (sectorConjugacy k x).val := by
  have h : sectorConjugacy (cyclicNext k) (sectorRotatePoint k x) =
      rigidSectorRotatePoint k (sectorConjugacy k x) := by
    apply (equivariantRigidSectorDisk (cyclicNext k)).injective
    rw [equivariantRigidSectorDisk_rotation, sectorConjugacy_coordinates,
      sectorConjugacy_coordinates, equivariantSectorDisk_rotation]
  exact congrArg Subtype.val h

/-- Both sides are constructed, rather than supplied as assumptions. -/
theorem sectorwise_rigid_conjugacy :
    ∃ E : ∀ k : Fin 17, diagramSector k ≃ₜ rigidSector k,
      (∀ k z, (E k ⟨sectorBoundaryParam k z, sectorBoundaryParam_subset k (mem_range_self z)⟩).val =
        rigidSectorParam k z) ∧
      (∀ k x, (E (cyclicNext k) (sectorRotatePoint k x)).val =
        rigidSphereRotation rigidGenerator (E k x).val) :=
  ⟨sectorConjugacy, sectorConjugacy_boundary, sectorConjugacy_rotation⟩

end Venn17.Topology
