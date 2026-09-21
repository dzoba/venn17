import VennTopology.ConeDisk

noncomputable section
namespace Venn19.Topology
open Set
open scoped Classical

/-- Flatten a subtype while retaining the induced topology. -/
def subtypeConjunction {X : Type*} [TopologicalSpace X] (s : Set X) (p : X → Prop) :
    {x : s // p x.val} ≃ₜ {x : X // x ∈ s ∧ p x} where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def openDiskInClosedDisk :
    Metric.ball (0 : ℂ) 1 ≃ₜ {z : ClosedDisk // ‖z.val‖ < 1} :=
  (Homeomorph.setCongr (show Metric.ball (0 : ℂ) 1 =
    {z : ℂ | z ∈ ClosedDisk ∧ ‖z‖ < 1} by
      ext z
      simp only [Metric.mem_ball, dist_zero_right, mem_setOf_eq,
        Metric.mem_closedBall]
      exact ⟨fun h => ⟨h.le, h⟩, fun h => h.2⟩)).trans
    (subtypeConjunction ClosedDisk (fun z => ‖z‖ < 1)).symm

namespace Coordinates
variable {I T : Type*} (cells : T → Finset I) (a : I)

theorem openStar_eq_cone (hf : ∀ t i, i ∈ cells t → ((cells t).erase i).Nonempty)
    (h : Circle ≃ₜ link cells a) :
    openStar cells a = {x | x ∈ range (linkConeParameter cells a h) ∧ 0 < x a} := by
  ext x
  constructor
  · rintro ⟨hx, hpos⟩
    refine ⟨?_, hpos⟩
    obtain ⟨t, ht⟩ := mem_iUnion.mp hx
    have hle := simplex_le_one ht a
    by_cases he : x a = 1
    · have hx' : x = vertex a := (coordinate_one_iff cells hf hx).mp he
      refine ⟨(1, ⟨1, by norm_num⟩), ?_⟩
      simp [linkConeParameter, mix, hx']
    · have hlt : x a < 1 := lt_of_le_of_ne hle he
      have hy := puncturedStar_decomposition cells hf ⟨hx, hpos, hlt⟩
      refine ⟨(h.symm ⟨radialProjection a x, hy⟩, ⟨x a, hpos.le, hle⟩), ?_⟩
      simpa only [linkConeParameter, Homeomorph.apply_symm_apply] using
        mix_radialProjection a x hlt
  · rintro ⟨⟨p, rfl⟩, hp⟩
    exact ⟨mix_mem_realization cells (h p.1).property p.2.property.1 p.2.property.2, hp⟩

/-- An actual open vertex star whose geometric link is a circle is an open disk.
The center is included and continuity there follows from compact quotient maps. -/
def openStarDiskHomeomorph (hf : ∀ t i, i ∈ cells t → ((cells t).erase i).Nonempty)
    (h : Circle ≃ₜ link cells a) : Metric.ball (0 : ℂ) 1 ≃ₜ openStar cells a :=
  openDiskInClosedDisk.trans
    ((linkConeDiskHomeomorph cells a h).subtype (p := fun z => ‖z.val‖ < 1)
      (q := fun x => 0 < x.val a) (by
        intro z
        rw [linkConeDiskHomeomorph_coordinate]
        exact sub_pos.symm)) |>.trans
    (subtypeConjunction (range (linkConeParameter cells a h)) (fun x => 0 < x a)) |>.trans
    (Homeomorph.setCongr (openStar_eq_cone cells a hf h).symm)

#print axioms openStarDiskHomeomorph
end Coordinates
end Venn19.Topology
