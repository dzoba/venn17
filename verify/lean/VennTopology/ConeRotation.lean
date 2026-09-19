import VennTopology.ConeDisk
import VennTopology.CoordinateRelabel
import Mathlib.Analysis.Complex.Isometry

/-! An equivariant circle parametrization extends radially to an equivariant
disk homeomorphism. The target action is the actual Euclidean linear isometry
`_root_.rotation`, including at the disk center. -/

noncomputable section
namespace Venn17.Topology
open Set

/-- Restrict a rigid complex-plane rotation to the unit disk. -/
def closedDiskRotation (c : Circle) : ClosedDisk ≃ₜ ClosedDisk :=
  (_root_.rotation c).toHomeomorph.subtype (fun z => by
    change dist z 0 ≤ 1 ↔ dist ((_root_.rotation c) z) 0 ≤ 1
    simp only [dist_zero_right, LinearIsometryEquiv.norm_map])

@[simp] theorem closedDiskRotation_val (c : Circle) (z : ClosedDisk) :
    (closedDiskRotation c z).val = (c : ℂ) * z.val := rfl

theorem diskParameter_rotation (c : Circle) (p : ConeParameters) :
    closedDiskRotation c (diskParameter p) = diskParameter (c * p.1, p.2) := by
  apply Subtype.ext
  simp only [closedDiskRotation_val, diskParameter, Circle.coe_mul, Complex.real_smul]
  ring

namespace Coordinates
variable {I T : Type*}

theorem reindex_mix (e : I ≃ I) (a : I) (ha : e a = a) (r : ℝ) (x : Point I) :
    reindex e (mix a r x) = mix a r (reindex e x) := by
  have hadd (x y : Point I) : reindex e (x + y) = reindex e x + reindex e y := by
    ext j; simp [reindex_apply]
  have hsmul (r : ℝ) (x : Point I) : reindex e (r • x) = r • reindex e x := by
    ext j; simp [reindex_apply]
  simp only [mix, hadd, hsmul, reindex_vertex, ha]

/-- Radial extension preserves the specified rotation angle and its full
coordinate action, rather than just constructing an arbitrary disk chart. -/
theorem linkConeDiskHomeomorph_rotation (cells : T → Finset I) (a : I)
    (h : Circle ≃ₜ link cells a) (e : I ≃ I) (ha : e a = a) (c : Circle)
    (he : ∀ z : Circle, reindex e (h z).val = (h (c * z)).val) (z : ClosedDisk) :
    reindex e (linkConeDiskHomeomorph cells a h z).val =
      (linkConeDiskHomeomorph cells a h (closedDiskRotation c z)).val := by
  obtain ⟨p, rfl⟩ := diskParameter_surjective z
  rw [diskParameter_rotation]
  simp only [linkConeDiskHomeomorph, compactParametrizationHomeomorph_apply,
    linkConeParameter]
  rw [reindex_mix e a ha, he]

#print axioms linkConeDiskHomeomorph_rotation
end Coordinates
end Venn17.Topology
