import VennTopology.MidpointPolygon
import VennTopology.Stars

noncomputable section
namespace Venn17.Topology.Coordinates
open Set
open scoped Classical
variable {I : Type*}
local instance triangleMidlineDecidableEq : DecidableEq I := Classical.decEq _

theorem simplex_reconstruct {s : Finset I} {x : Point I} (hx : x ∈ simplex s) :
    ∑ j ∈ s, x j • vertex j = x := by
  ext k
  by_cases hk : k ∈ s
  · simp [Finset.sum_apply, vertex, hk]
  · simp [Finset.sum_apply, vertex, hk, simplex_zero hx hk]

theorem triangle_reconstruct {c u v : I} (hcu : c ≠ u) (hcv : c ≠ v) (huv : u ≠ v)
    {x : Point I} (hx : x ∈ simplex {c,u,v}) :
    x c • vertex c + x u • vertex u + x v • vertex v = x := by
  simpa [hcu,hcv,huv,add_assoc] using simplex_reconstruct hx

theorem triangle_sum {c u v : I} (hcu : c ≠ u) (hcv : c ≠ v) (huv : u ≠ v)
    {x : Point I} (hx : x ∈ simplex {c,u,v}) : x c + x u + x v = 1 := by
  simpa [hcu,hcv,huv,add_assoc] using simplex_sum hx

/-- Inside a coordinate triangle the center-to-midpoint arm is exactly the
locus where the two region coordinates agree. -/
theorem triangle_midline_iff {c u v : I} (hcu : c ≠ u) (hcv : c ≠ v) (huv : u ≠ v)
    {x : Point I} (hx : x ∈ simplex {c,u,v}) :
    x ∈ segment ℝ (vertex c) (pairPoint (u,v)) ↔ x u = x v := by
  constructor
  · intro hh
    rw [segment_eq_image_lineMap] at hh
    obtain ⟨r,_,rfl⟩ := hh
    simp [AffineMap.lineMap_apply_module, pairPoint, vertex, Ne.symm hcu, Ne.symm hcv,
      huv, Ne.symm huv]
  · intro he
    have hsum := triangle_sum hcu hcv huv hx
    have hrecon := triangle_reconstruct hcu hcv huv hx
    have hnonneg := simplex_nonneg hx c
    have hle := simplex_le_one hx c
    change ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a+b = 1 ∧ a • vertex c + b • pairPoint (u,v) = x
    refine ⟨x c, 1-x c, hnonneg, by linarith, by ring, ?_⟩
    have hv : x v = (1-x c)/2 := by linarith
    calc
      x c • vertex c + (1-x c) • pairPoint (u,v) =
          x c • vertex c + x u • vertex u + x v • vertex v := by
            rw [pairPoint,he,hv]
            module
      _ = x := hrecon

local instance triangleMidlineNatDecidableEq : DecidableEq Nat := Classical.decEq _

/-- Region labels range over `Fin n`; centers have labels outside that range. -/
def Dominates (n v : Nat) (x : Point Nat) : Prop :=
  0 < x v ∧ ∀ w : Fin n, w.val ≠ v → x w.val < x v

theorem dominates_vertex {n v : Nat} : Dominates n v (vertex v) := by
  refine ⟨by simp, ?_⟩
  intro w hw
  simp [vertex,hw]

theorem dominates_disjoint {n u v : Nat} {x : Point Nat}
    (hu : u < n) (hv : v < n) (hxu : Dominates n u x) (hxv : Dominates n v x) : u = v := by
  by_contra h
  exact (lt_asymm (hxu.2 ⟨v,hv⟩ (Ne.symm h)) (hxv.2 ⟨u,hu⟩ h))

theorem midline_not_dominates {n c u v w : Nat} (hc : n ≤ c) (hu : u < n)
    (hv : v < n) (huv : u ≠ v) (hw : w < n) {x : Point Nat}
    (hx : x ∈ segment ℝ (vertex c) (pairPoint (u,v))) : ¬ Dominates n w x := by
  intro hd
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨r,hr,rfl⟩ := hx
  have hc' : w ≠ c := by omega
  by_cases hwu : w = u
  · subst w
    have he := hd.2 ⟨v,hv⟩ (Ne.symm huv)
    have huc : u ≠ c := by omega
    have hvc : v ≠ c := by omega
    simp [AffineMap.lineMap_apply_module,pairPoint,vertex,huc,hvc,huv,Ne.symm huv] at he
  · by_cases hwv : w = v
    · subst w
      have he := hd.2 ⟨u,hu⟩ huv
      have huc : u ≠ c := by omega
      have hvc : v ≠ c := by omega
      simp [AffineMap.lineMap_apply_module,pairPoint,vertex,huc,hvc,huv,Ne.symm huv] at he
    · have he := hd.1
      simp [AffineMap.lineMap_apply_module,pairPoint,vertex,hc',hwu,hwv] at he

theorem triangle_dominates_of_lt {n c u v : Nat} (hc : n ≤ c) (_hu : u < n) (_hv : v < n)
    {x : Point Nat} (hx : x ∈ simplex {c,u,v}) (hlt : x v < x u) : Dominates n u x := by
  refine ⟨lt_of_le_of_lt (simplex_nonneg hx v) hlt, ?_⟩
  intro w hwu
  by_cases hwv : w.val = v
  · simpa only [hwv] using hlt
  · have hwc : w.val ≠ c := by have := w.isLt; omega
    have hz : x w.val = 0 := simplex_zero hx (by simp [hwu,hwv,hwc])
    rw [hz]
    exact lt_of_le_of_lt (simplex_nonneg hx v) hlt

variable {T : Type*} (cells : T → Finset Nat)

def region (n v : Nat) : Set (Point Nat) := {x | x ∈ realization cells ∧ Dominates n v x}

theorem region_starConvex (n v : Nat) : StarConvex ℝ (vertex v) (region cells n v) := by
  intro x hx r s hr hs hrs
  have hstar := openStar_starConvex cells v ⟨hx.1,hx.2.1⟩ hr hs hrs
  refine ⟨hstar.1, hstar.2, ?_⟩
  intro w hw
  change r * vertex v w.val + s * x w.val < r * vertex v v + s * x v
  simp only [vertex_other hw,vertex_self,mul_zero,zero_add,mul_one]
  have hlt := hx.2.2 w hw
  by_cases hsp : 0 < s
  · have hh := mul_lt_mul_of_pos_left hlt hsp
    linarith
  · have hs0 : s = 0 := le_antisymm (not_lt.mp hsp) hs
    have hr1 : r = 1 := by linarith
    simp [hs0,hr1]

end Venn17.Topology.Coordinates
