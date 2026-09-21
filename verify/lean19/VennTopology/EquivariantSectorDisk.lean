import VennTopology.SectorDisk
import Mathlib.Dynamics.PeriodicPts.Defs

/-! Choose one disk chart and transport it by the actual diagram symmetry.
These charts agree with the prescribed boundary parameters and conjugate the
sector-to-sector action to the identity on disk coordinates, including wraparound. -/
noncomputable section
namespace Venn19.Topology
open Set Coordinates

/-- Iteration as a homeomorphism, retaining its inverse and continuity. -/
def diagramRotationIterate : Nat → Diagram ≃ₜ Diagram
  | 0 => Homeomorph.refl _
  | n+1 => (diagramRotationIterate n).trans diagramRotation

theorem diagramRotationIterate_apply (n : Nat) (x : Diagram) :
    diagramRotationIterate n x = diagramRotation^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change diagramRotation (diagramRotationIterate n x) = _
      rw [ih, Function.iterate_succ_apply']

theorem diagram_sector_iterate (n : Nat) (k : Fin 19) :
    diagramRotationIterate n '' diagramSector k = diagramSector (cyclicNext^[n] k) := by
  induction n with
  | zero => simp [diagramRotationIterate]
  | succ n ih =>
      change (fun x => diagramRotation (diagramRotationIterate n x)) '' diagramSector k = _
      rw [← image_image, ih, diagram_sector_rotation, Function.iterate_succ_apply']

theorem sector_index_iterate (k : Fin 19) : cyclicNext^[k.val] (0 : Fin 19) = k := by
  decide +revert

def sectorFromZero (k : Fin 19) : diagramSector 0 ≃ₜ diagramSector k :=
  ((diagramRotationIterate k.val).image (diagramSector 0)).trans
    (Homeomorph.setCongr ((diagram_sector_iterate k.val 0).trans (congrArg diagramSector (sector_index_iterate k))))

theorem sectorFromZero_apply (k : Fin 19) (x : diagramSector 0) :
    (sectorFromZero k x).val = diagramRotation^[k.val] x.val :=
  diagramRotationIterate_apply _ _

theorem sectorBoundaryParam_rotation (k : Fin 19) (z : UnitCircle) :
    diagramRotation (sectorBoundaryParam k z) = sectorBoundaryParam (cyclicNext k) z :=
  diagramMeridianBoundaryMap_rotation _ _ _

theorem sectorBoundaryParam_iterate (n : Nat) (k : Fin 19) (z : UnitCircle) :
    diagramRotation^[n] (sectorBoundaryParam k z) = sectorBoundaryParam (cyclicNext^[n] k) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, sectorBoundaryParam_rotation, Function.iterate_succ_apply']

/-- The family of charts is constructed equivariantly, from just the chart at index zero. -/
def equivariantSectorDisk (k : Fin 19) : diagramSector k ≃ₜ PlaneClosedDisk :=
  (sectorFromZero k).symm.trans (sectorDiskHomeomorph 0)

theorem equivariantSectorDisk_boundary (k : Fin 19) (z : UnitCircle) :
    (equivariantSectorDisk k
      ⟨sectorBoundaryParam k z, sectorBoundaryParam_subset k (mem_range_self z)⟩).val = z.val := by
  have he : (sectorFromZero k).symm
      ⟨sectorBoundaryParam k z, sectorBoundaryParam_subset k (mem_range_self z)⟩ =
      ⟨sectorBoundaryParam 0 z, sectorBoundaryParam_subset 0 (mem_range_self z)⟩ := by
    apply (sectorFromZero k).injective
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    rw [sectorFromZero_apply, sectorBoundaryParam_iterate, sector_index_iterate]
  change (sectorDiskHomeomorph 0 ((sectorFromZero k).symm _)).val = z.val
  rw [he]
  exact sectorDiskHomeomorph_boundary 0 z

theorem sectorFromZero_next (k : Fin 19) (x : diagramSector 0) :
    (sectorFromZero (cyclicNext k) x).val = diagramRotation (sectorFromZero k x).val := by
  rw [sectorFromZero_apply, sectorFromZero_apply]
  change diagramRotation^[(k.val+1)%19] x.val = diagramRotation (diagramRotation^[k.val] x.val)
  rw [(show Function.IsPeriodicPt diagramRotation 19 x.val from diagram_rotation_period x.val).iterate_mod_apply]
  exact Function.iterate_succ_apply' _ _ _

def sectorRotatePoint (k : Fin 19) (x : diagramSector k) : diagramSector (cyclicNext k) :=
  ⟨diagramRotation x.val, by rw [← diagram_sector_rotation]; exact mem_image_of_mem _ x.property⟩

/-- The actual global symmetry preserves these disk coordinates when passing
to the next sector. Period 19 proves the last-to-first case as well. -/
theorem equivariantSectorDisk_rotation (k : Fin 19) (x : diagramSector k) :
    equivariantSectorDisk (cyclicNext k) (sectorRotatePoint k x) = equivariantSectorDisk k x := by
  change sectorDiskHomeomorph 0 ((sectorFromZero (cyclicNext k)).symm _) =
    sectorDiskHomeomorph 0 ((sectorFromZero k).symm x)
  apply congrArg (sectorDiskHomeomorph 0)
  apply (sectorFromZero (cyclicNext k)).injective
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  rw [sectorFromZero_next, Homeomorph.apply_symm_apply]
  rfl

#print axioms equivariantSectorDisk_boundary
#print axioms equivariantSectorDisk_rotation
end Venn19.Topology
