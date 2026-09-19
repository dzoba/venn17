import VennTopology.CompactParametrization
import VennTopology.Stars
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

noncomputable section
namespace Venn17.Topology
open Set
open scoped Classical

abbrev ConeParameters := Circle × Icc (0 : ℝ) 1
abbrev ClosedDisk := Metric.closedBall (0 : ℂ) 1

def diskParameter (p : ConeParameters) : ClosedDisk :=
  ⟨(1-p.2.val) • (p.1 : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Circle.norm_coe,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr p.2.property.2), mul_one]
    linarith [p.2.property.1]⟩

@[simp] theorem norm_diskParameter (p : ConeParameters) :
    ‖(diskParameter p).val‖ = 1-p.2.val := by
  change ‖(1-p.2.val) • (p.1 : ℂ)‖ = 1-p.2.val
  rw [norm_smul, Circle.norm_coe, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr p.2.property.2), mul_one]

theorem continuous_diskParameter : Continuous diskParameter := by
  unfold diskParameter
  fun_prop

theorem diskParameter_surjective : Function.Surjective diskParameter := by
  intro z
  have hnorm : ‖z.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
  by_cases hz : z.val = 0
  · refine ⟨(1, ⟨1, by norm_num⟩), ?_⟩
    apply Subtype.ext
    simp [diskParameter, hz]
  · let c : Circle := ⟨(‖z.val‖⁻¹ : ℝ) • z.val, by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_smul, Real.norm_eq_abs, abs_inv,
        abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
    refine ⟨(c, ⟨1-‖z.val‖, by constructor <;> linarith [norm_nonneg z.val]⟩), ?_⟩
    apply Subtype.ext
    change (1-(1-‖z.val‖)) • ((‖z.val‖⁻¹ : ℝ) • z.val) = z.val
    rw [sub_sub_cancel, smul_inv_smul₀ (norm_ne_zero_iff.mpr hz)]

theorem diskParameter_eq_iff (p q : ConeParameters) :
    diskParameter p = diskParameter q ↔ p.2.val = q.2.val ∧ (p.2.val = 1 ∨ p.1 = q.1) := by
  constructor
  · intro he
    have hn := congrArg (fun z : ClosedDisk => ‖z.val‖) he
    simp only [norm_diskParameter] at hn
    have hr : p.2.val = q.2.val := by linarith
    refine ⟨hr, ?_⟩
    by_cases hp : p.2.val = 1
    · exact Or.inl hp
    · right
      apply Subtype.ext
      have he' := congrArg Subtype.val he
      change (1-p.2.val) • (p.1 : ℂ) = (1-q.2.val) • (q.1 : ℂ) at he'
      rw [← hr] at he'
      exact smul_right_injective ℂ (sub_ne_zero.mpr (Ne.symm hp)) he'
  · rintro ⟨hr, hp | hp⟩
    · apply Subtype.ext
      simp [diskParameter, ← hr, hp]
    · apply Subtype.ext
      simp [diskParameter, hr, hp]

namespace Coordinates
variable {I T : Type*} (cells : T → Finset I) (a : I)

def linkConeParameter (h : Circle ≃ₜ link cells a) (p : ConeParameters) : Point I :=
  mix a p.2.val (h p.1).val

theorem continuous_linkConeParameter (h : Circle ≃ₜ link cells a) :
    Continuous (linkConeParameter cells a h) := by
  unfold linkConeParameter mix
  fun_prop

theorem linkConeParameter_eq_iff (h : Circle ≃ₜ link cells a) (p q : ConeParameters) :
    linkConeParameter cells a h p = linkConeParameter cells a h q ↔
      p.2.val = q.2.val ∧ (p.2.val = 1 ∨ p.1 = q.1) := by
  constructor
  · intro he
    have hr : p.2.val = q.2.val := by
      have hh := congrFun he a
      simpa only [linkConeParameter, mix_coordinate cells (h p.1).property,
        mix_coordinate cells (h q.1).property] using hh
    refine ⟨hr, ?_⟩
    by_cases hp : p.2.val = 1
    · exact Or.inl hp
    · right
      apply h.injective
      apply Subtype.ext
      change p.2.val • vertex a + (1-p.2.val) • (h p.1).val =
        q.2.val • vertex a + (1-q.2.val) • (h q.1).val at he
      rw [← hr] at he
      exact smul_right_injective (Point I) (sub_ne_zero.mpr (Ne.symm hp))
        (add_left_cancel he)
  · rintro ⟨hr, hp | hp⟩
    · simp [linkConeParameter, mix, ← hr, hp]
    · simp [linkConeParameter, hr, hp]

/-- A closed cone over the geometric link is a disk, including its apex. -/
def linkConeDiskHomeomorph (h : Circle ≃ₜ link cells a) :
    ClosedDisk ≃ₜ range (linkConeParameter cells a h) :=
  compactParametrizationHomeomorph diskParameter diskParameter_surjective
    (linkConeParameter cells a h) continuous_diskParameter
    (continuous_linkConeParameter cells a h)
    (fun p q => (linkConeParameter_eq_iff cells a h p q).trans (diskParameter_eq_iff p q).symm)

theorem linkConeDiskHomeomorph_coordinate (h : Circle ≃ₜ link cells a) (z : ClosedDisk) :
    (linkConeDiskHomeomorph cells a h z).val a = 1-‖z.val‖ := by
  obtain ⟨p, rfl⟩ := diskParameter_surjective z
  rw [linkConeDiskHomeomorph, compactParametrizationHomeomorph_apply]
  simp only [linkConeParameter, mix_coordinate cells (h p.1).property, norm_diskParameter]
  ring

#print axioms linkConeDiskHomeomorph
end Coordinates
end Venn17.Topology
