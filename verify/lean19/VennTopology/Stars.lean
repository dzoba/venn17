import VennTopology.CoordinateSimplex
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
namespace Venn19.Topology.Coordinates

open Set
open scoped Classical
variable {I T : Type*} (cells : T → Finset I)

def realization : Set (Point I) := ⋃ t, simplex (cells t)

def link (a : I) : Set (Point I) := ⋃ t, ⋃ (_ : a ∈ cells t), simplex ((cells t).erase a)

def openStar (a : I) : Set (Point I) := {x | x ∈ realization cells ∧ 0 < x a}

def puncturedStar (a : I) : Set (Point I) :=
  {x | x ∈ realization cells ∧ 0 < x a ∧ x a < 1}

theorem positive_coordinate_in_cell {t : T} {x : Point I} (hx : x ∈ simplex (cells t))
    {a : I} (ha : 0 < x a) : a ∈ cells t := by
  by_contra h
  rw [simplex_zero hx h] at ha
  exact (lt_irrefl _ ha)

theorem open_stars_cover {x : Point I} (hx : x ∈ realization cells) :
    ∃ a, x ∈ openStar cells a := by
  obtain ⟨t, ht⟩ := mem_iUnion.mp hx
  obtain ⟨a, _, ha⟩ := simplex_has_positive_coordinate ht
  exact ⟨a, hx, ha⟩

theorem openStar_isOpen (a : I) : IsOpen {x : realization cells | 0 < x.val a} :=
  isOpen_lt continuous_const ((continuous_apply a).comp continuous_subtype_val)

theorem link_coordinate_zero {a : I} {y : Point I} (hy : y ∈ link cells a) : y a = 0 := by
  obtain ⟨t, _, hy⟩ := mem_iUnion₂.mp hy
  exact simplex_zero hy (Finset.notMem_erase _ _)

theorem link_mem_realization {a : I} {y : Point I} (hy : y ∈ link cells a) :
    y ∈ realization cells := by
  obtain ⟨t, _, hy⟩ := mem_iUnion₂.mp hy
  exact mem_iUnion.mpr ⟨t, simplex_mono (Finset.erase_subset _ _) hy⟩

def mix (a : I) (r : ℝ) (y : Point I) : Point I := r • vertex a + (1-r) • y

theorem mix_coordinate {a : I} {y : Point I} (hy : y ∈ link cells a) (r : ℝ) :
    mix a r y a = r := by
  simp [mix, link_coordinate_zero cells hy]

theorem mix_mem_realization {a : I} {y : Point I} (hy : y ∈ link cells a)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : mix a r y ∈ realization cells := by
  obtain ⟨t, hat, hy⟩ := mem_iUnion₂.mp hy
  apply mem_iUnion.mpr
  refine ⟨t, (convex_convexHull ℝ _)
    (vertex_mem_simplex hat) (simplex_mono (Finset.erase_subset _ _) hy)
    hr0 (sub_nonneg.mpr hr1) (by ring)⟩

def radialProjection (a : I) (x : Point I) : Point I :=
  (1-x a)⁻¹ • (x - x a • vertex a)

theorem radialProjection_mix {a : I} {y : Point I} (hy : y ∈ link cells a)
    {r : ℝ} (hr : r < 1) : radialProjection a (mix a r y) = y := by
  unfold radialProjection
  rw [mix_coordinate cells hy]
  have he : mix a r y - r • vertex a = (1-r) • y := by unfold mix; module
  rw [he, inv_smul_smul₀ (by linarith : 1-r ≠ 0)]

theorem mix_radialProjection (a : I) (x : Point I) (hx : x a < 1) :
    mix a (x a) (radialProjection a x) = x := by
  unfold mix radialProjection
  rw [smul_inv_smul₀ (by linarith : 1-x a ≠ 0)]
  module

theorem puncturedStar_decomposition
    (hfaces : ∀ t a, a ∈ cells t → ((cells t).erase a).Nonempty)
    {a : I} {x : Point I} (hx : x ∈ puncturedStar cells a) :
    radialProjection a x ∈ link cells a := by
  obtain ⟨t, ht⟩ := mem_iUnion.mp hx.1
  have ha := positive_coordinate_in_cell cells ht hx.2.1
  obtain ⟨y, hy, r, s, hr, hs, hrs, he⟩ := simplex_split ha (hfaces t a ha) ht
  have hya : y a = 0 := simplex_zero hy (Finset.notMem_erase _ _)
  have hri : r = x a := by
    have he := congrFun he a
    simpa [hya] using he
  have hsi : s = 1-x a := by linarith
  have hym : y ∈ link cells a := mem_iUnion₂.mpr ⟨t, ha, hy⟩
  have hmix : mix a (x a) y = x := by simpa only [mix, hri, hsi] using he
  rw [← hmix, radialProjection_mix cells hym hx.2.2]
  exact hym

/-- The punctured open star has explicit radial coordinates: the geometric
link times an open interval. No manifold or circle theorem is assumed. -/
def puncturedStarHomeomorph
    (hfaces : ∀ t a, a ∈ cells t → ((cells t).erase a).Nonempty) (a : I) :
    puncturedStar cells a ≃ₜ (link cells a × Ioo (0 : ℝ) 1) where
  toFun x := (⟨radialProjection a x.val, puncturedStar_decomposition cells hfaces x.property⟩,
    ⟨x.val a, x.property.2⟩)
  invFun p := ⟨mix a p.2.val p.1.val,
    mix_mem_realization cells p.1.property p.2.property.1.le p.2.property.2.le,
    by simpa only [mix_coordinate cells p.1.property, mem_Ioo] using p.2.property⟩
  left_inv x := Subtype.ext (mix_radialProjection a x.val x.property.2.2)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (radialProjection_mix cells p.1.property p.2.property.2)
    · exact Subtype.ext (mix_coordinate cells p.1.property p.2.val)
  continuous_toFun := by
    have hc : Continuous (fun x : puncturedStar cells a => x.val a) :=
      (continuous_apply a).comp continuous_subtype_val
    have hp : Continuous (fun x : puncturedStar cells a => radialProjection a x.val) :=
      ((continuous_const.sub hc).inv₀ (fun x => by
        exact ne_of_gt (sub_pos.mpr x.property.2.2))).smul
        (continuous_subtype_val.sub (hc.smul continuous_const))
    exact (hp.subtype_mk _).prodMk (hc.subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    unfold mix
    fun_prop

theorem openStar_starConvex (a : I) : StarConvex ℝ (vertex a) (openStar cells a) := by
  intro x hx r s hr hs hrs
  obtain ⟨t, ht⟩ := mem_iUnion.mp hx.1
  have ha := positive_coordinate_in_cell cells ht hx.2
  refine ⟨mem_iUnion.mpr ⟨t, (convex_convexHull ℝ _)
    (vertex_mem_simplex ha) ht hr hs hrs⟩, ?_⟩
  change 0 < r * vertex a a + s * x a
  rw [vertex_self]
  have hp := hx.2
  by_cases hrp : 0 < r
  · positivity
  · have hr0 : r = 0 := le_antisymm (not_lt.mp hrp) hr
    have hs1 : s = 1 := by linarith
    simpa [hr0, hs1] using hp

theorem openStar_contractible (a : I) (ha : ∃ t, a ∈ cells t) :
    ContractibleSpace (openStar cells a) := by
  obtain ⟨t, ht⟩ := ha
  apply (openStar_starConvex cells a).contractibleSpace
  exact ⟨vertex a, mem_iUnion.mpr ⟨t, vertex_mem_simplex ht⟩, by simp⟩

theorem coordinate_one_iff
    (hfaces : ∀ t a, a ∈ cells t → ((cells t).erase a).Nonempty)
    {a : I} {x : Point I} (hx : x ∈ realization cells) : x a = 1 ↔ x = vertex a := by
  constructor
  · intro ha1
    obtain ⟨t, ht⟩ := mem_iUnion.mp hx
    have ha := positive_coordinate_in_cell cells ht (by rw [ha1]; norm_num)
    obtain ⟨y, hy, r, s, _, _, hrs, he⟩ := simplex_split ha (hfaces t a ha) ht
    have hya : y a = 0 := simplex_zero hy (Finset.notMem_erase _ _)
    have hr : r = 1 := by have hh := congrFun he a; simpa [hya, ha1] using hh
    have hs : s = 0 := by linarith
    simpa [hr, hs] using he.symm
  · rintro rfl
    exact vertex_self a

theorem puncturedStar_eq_delete_vertex
    (hfaces : ∀ t a, a ∈ cells t → ((cells t).erase a).Nonempty) (a : I) :
    puncturedStar cells a = openStar cells a \ {vertex a} := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨hx.1, hx.2.1⟩, ?_⟩
    simp only [mem_singleton_iff]
    intro he
    have hh := (coordinate_one_iff cells hfaces hx.1).mpr he
    exact (ne_of_lt hx.2.2) hh
  · rintro ⟨⟨hx, hp⟩, hne⟩
    obtain ⟨t, ht⟩ := mem_iUnion.mp hx
    refine ⟨hx, hp, lt_of_le_of_ne (simplex_le_one ht a) ?_⟩
    intro he
    exact hne ((coordinate_one_iff cells hfaces hx).mp he)

#print axioms puncturedStarHomeomorph

end Venn19.Topology.Coordinates
