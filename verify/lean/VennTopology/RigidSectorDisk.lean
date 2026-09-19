import VennTopology.SphereLunes

/-! The 17 standard spherical sectors and equivariant disk coordinates. -/
noncomputable section
namespace Venn17.Topology
open Set Coordinates LeanEval.Topology.ClassificationOfSurfaces

theorem planarCross_rotate (c : Circle) (z w : ℂ) :
    planarCross ((c : ℂ)*z) ((c : ℂ)*w) = planarCross z w := by
  have hc := Circle.normSq_coe c
  rw [Complex.normSq_apply] at hc
  simp only [planarCross, Complex.mul_re, Complex.mul_im]
  linear_combination (z.re*w.im-z.im*w.re) * hc

theorem rigidGenerator_cross_pos : 0 < planarCross (1 : ℂ) rigidGenerator := by
  have ha : 0 < 2 * Real.pi / 17 := by positivity
  have hb : 2 * Real.pi / 17 < Real.pi := by linarith [Real.pi_pos]
  simpa [planarCross, rigidGenerator, Circle.coe_exp, Complex.exp_im] using
    Real.sin_pos_of_pos_of_lt_pi ha hb

theorem rigidDirection_cross_pos (k : Fin 17) :
    0 < planarCross (rigidDirection k) (rigidDirection (cyclicNext k)) := by
  rw [rigidDirection_next, mul_comm rigidGenerator, Circle.coe_mul]
  have he := planarCross_rotate (rigidDirection k) 1 rigidGenerator
  rw [mul_one] at he
  rw [he]
  exact rigidGenerator_cross_pos

def rigidSector (k : Fin 17) : Set SphereRepresentative :=
  sphereLune (rigidDirection k) (rigidDirection (cyclicNext k))

theorem rigidSector_closed (k : Fin 17) : IsClosed (rigidSector k) := sphereLune_closed _ _
theorem rigidSector_compact (k : Fin 17) : IsCompact (rigidSector k) := sphereLune_compact _ _

def rigidSectorParam (k : Fin 17) : UnitCircle → SphereRepresentative :=
  sphereLuneParam (rigidDirection k) (rigidDirection (cyclicNext k))

theorem rigidSectorParam_subset (k : Fin 17) : range (rigidSectorParam k) ⊆ rigidSector k :=
  sphereLuneParam_subset _ _ (rigidDirection_cross_pos k)

theorem rigidSectorParam_rotation (k : Fin 17) (z : UnitCircle) :
    rigidSphereRotation rigidGenerator (rigidSectorParam k z) = rigidSectorParam (cyclicNext k) z :=
  rigidSectorBoundary_rotation k _

def rigidSectorDisk (k : Fin 17) : rigidSector k ≃ₜ PlaneClosedDisk :=
  sphereLuneDisk _ _ (rigidDirection_cross_pos k)

theorem rigidSectorDisk_boundary (k : Fin 17) (z : UnitCircle) :
    (rigidSectorDisk k ⟨rigidSectorParam k z, rigidSectorParam_subset k (mem_range_self z)⟩).val = z.val :=
  sphereLuneDisk_boundary _ _ (rigidDirection_cross_pos k) z

theorem sphereLune_rotation_mem (c d e : Circle) (x : SphereRepresentative) :
    rigidSphereRotation c x ∈ sphereLune (c*d) (c*e) ↔ x ∈ sphereLune d e := by
  change (0 ≤ planarCross _ _ ∧ planarCross _ _ ≤ 0) ↔ _
  simp only [rigidSphereRotation_val, horizontal_axialRotationMap, Circle.coe_mul, planarCross_rotate]
  rfl

theorem sphereLune_rotation (c d e : Circle) :
    rigidSphereRotation c '' sphereLune d e = sphereLune (c*d) (c*e) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (sphereLune_rotation_mem c d e y).mpr hy
  · intro hx
    obtain ⟨y, rfl⟩ := (rigidSphereRotation c).surjective x
    exact ⟨y, (sphereLune_rotation_mem c d e y).mp hx, rfl⟩

theorem rigidSector_rotation (k : Fin 17) :
    rigidSphereRotation rigidGenerator '' rigidSector k = rigidSector (cyclicNext k) := by
  unfold rigidSector
  rw [sphereLune_rotation, ← rigidDirection_next, ← rigidDirection_next]

theorem rigidSector_from_zero (k : Fin 17) :
    rigidSphereRotation (rigidDirection k) '' rigidSector 0 = rigidSector k := by
  unfold rigidSector
  rw [sphereLune_rotation]
  have h0 : rigidDirection 0 = 1 := rfl
  have h1 : rigidDirection (cyclicNext 0) = rigidGenerator := by
    rw [rigidDirection_next, h0, mul_one]
  rw [h0, h1, mul_one, mul_comm, ← rigidDirection_next]

def rigidSectorFromZero (k : Fin 17) : rigidSector 0 ≃ₜ rigidSector k :=
  ((rigidSphereRotation (rigidDirection k)).image (rigidSector 0)).trans
    (Homeomorph.setCongr (rigidSector_from_zero k))

theorem rigidSectorFromZero_apply (k : Fin 17) (x : rigidSector 0) :
    (rigidSectorFromZero k x).val = rigidSphereRotation (rigidDirection k) x.val := rfl

theorem rigidSectorParam_from_zero (k : Fin 17) (z : UnitCircle) :
    rigidSphereRotation (rigidDirection k) (rigidSectorParam 0 z) = rigidSectorParam k z := by
  change rigidSphereRotation _ (sphereMeridianBoundary _ _ _) = sphereMeridianBoundary _ _ _
  rw [sphereMeridianBoundary_rotation]
  have h0 : rigidDirection 0 = 1 := rfl
  have h1 : rigidDirection (cyclicNext 0) = rigidGenerator := by
    rw [rigidDirection_next, h0, mul_one]
  rw [h0, h1, mul_one, mul_comm, ← rigidDirection_next]

/-- Transport a single target disk chart by the actual rigid rotations. -/
def equivariantRigidSectorDisk (k : Fin 17) : rigidSector k ≃ₜ PlaneClosedDisk :=
  (rigidSectorFromZero k).symm.trans (rigidSectorDisk 0)

theorem equivariantRigidSectorDisk_boundary (k : Fin 17) (z : UnitCircle) :
    (equivariantRigidSectorDisk k
      ⟨rigidSectorParam k z, rigidSectorParam_subset k (mem_range_self z)⟩).val = z.val := by
  have he : (rigidSectorFromZero k).symm
      ⟨rigidSectorParam k z, rigidSectorParam_subset k (mem_range_self z)⟩ =
      ⟨rigidSectorParam 0 z, rigidSectorParam_subset 0 (mem_range_self z)⟩ := by
    apply (rigidSectorFromZero k).injective
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    exact (rigidSectorParam_from_zero k z).symm
  change (rigidSectorDisk 0 ((rigidSectorFromZero k).symm _)).val = z.val
  rw [he]
  exact rigidSectorDisk_boundary 0 z

def rigidSectorRotatePoint (k : Fin 17) (x : rigidSector k) : rigidSector (cyclicNext k) :=
  ⟨rigidSphereRotation rigidGenerator x.val, by
    rw [← rigidSector_rotation]; exact mem_image_of_mem _ x.property⟩

theorem equivariantRigidSectorDisk_rotation (k : Fin 17) (x : rigidSector k) :
    equivariantRigidSectorDisk (cyclicNext k) (rigidSectorRotatePoint k x) =
      equivariantRigidSectorDisk k x := by
  change rigidSectorDisk 0 ((rigidSectorFromZero (cyclicNext k)).symm _) =
    rigidSectorDisk 0 ((rigidSectorFromZero k).symm x)
  apply congrArg (rigidSectorDisk 0)
  apply (rigidSectorFromZero (cyclicNext k)).injective
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  rw [rigidSectorFromZero_apply, rigidDirection_next, rigidSphereRotation_mul]
  change rigidSphereRotation rigidGenerator x.val =
    rigidSphereRotation rigidGenerator (rigidSectorFromZero k ((rigidSectorFromZero k).symm x)).val
  rw [Homeomorph.apply_symm_apply]

end Venn17.Topology
