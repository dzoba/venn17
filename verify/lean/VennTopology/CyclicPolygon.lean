import VennTopology.CoordinateSimplex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! A finite coordinate polygon is a genuine topological circle. The proof uses
closed edge parameters, with their shared endpoints identified by `AddCircle`.
No planar embedding or surface classification is assumed. -/
noncomputable section
namespace Venn17.Topology.Coordinates

open Set
open scoped Classical

variable {n : Nat}

def cyclicNext (i : Fin n) : Fin n := ⟨(i.val+1)%n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

theorem cyclicNext_val (i : Fin n) :
    (cyclicNext i).val = if i.val+1 < n then i.val+1 else 0 := by
  unfold cyclicNext
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have he : i.val+1 = n := by omega
    simp [he]

theorem cyclicNext_ne (hn : 2 ≤ n) (i : Fin n) : cyclicNext i ≠ i := by
  intro h
  have := congrArg Fin.val h
  simp only [cyclicNext_val] at this
  split_ifs at this <;> omega

theorem cyclicNext_next_ne (hn : 3 ≤ n) (i : Fin n) :
    cyclicNext (cyclicNext i) ≠ i := by
  intro h
  have := congrArg Fin.val h
  simp only [cyclicNext_val] at this
  split_ifs at this <;> omega

abbrev EdgeParameters (n : Nat) := Fin n × Icc (0 : ℝ) 1

def edgePoint (p : EdgeParameters n) : Point (Fin n) :=
  (1-p.2.val) • vertex p.1 + p.2.val • vertex (cyclicNext p.1)

@[simp] theorem edgePoint_zero (i : Fin n) :
    edgePoint (i, ⟨0, by norm_num⟩) = vertex i := by simp [edgePoint]

@[simp] theorem edgePoint_one (i : Fin n) :
    edgePoint (i, ⟨1, by norm_num⟩) = vertex (cyclicNext i) := by simp [edgePoint]

theorem edgePoint_left (hn : 2 ≤ n) (p : EdgeParameters n) :
    edgePoint p p.1 = 1-p.2.val := by
  simp [edgePoint, vertex, (cyclicNext_ne hn p.1).symm]

theorem edgePoint_right (hn : 2 ≤ n) (p : EdgeParameters n) :
    edgePoint p (cyclicNext p.1) = p.2.val := by
  simp [edgePoint, vertex, cyclicNext_ne hn p.1]

theorem edgePoint_injective_halfOpen (hn : 3 ≤ n) (p q : EdgeParameters n)
    (hp : p.2.val < 1) (hq : q.2.val < 1) (h : edgePoint p = edgePoint q) : p = q := by
  have hs : p.1 = q.1 := by
    by_contra hne
    have h1 : p.1 = cyclicNext q.1 := by
      by_contra h'
      have he := congrFun h p.1
      rw [edgePoint_left (by omega)] at he
      simp [edgePoint, vertex, hne, h'] at he
      linarith
    have h2 : q.1 = cyclicNext p.1 := by
      by_contra h'
      have he := congrFun h q.1
      rw [edgePoint_left (by omega)] at he
      simp [edgePoint, vertex, (Ne.symm hne), h'] at he
      linarith
    exact cyclicNext_next_ne hn p.1 (by rw [← h2, ← h1])
  have ht := congrFun h p.1
  rw [edgePoint_left (by omega), hs, edgePoint_left (by omega)] at ht
  exact Prod.ext hs (Subtype.ext (by linarith))

def normalizeEdge (p : EdgeParameters n) : EdgeParameters n :=
  if p.2.val = 1 then (cyclicNext p.1, ⟨0, by norm_num⟩) else p

theorem normalizeEdge_lt (p : EdgeParameters n) : (normalizeEdge p).2.val < 1 := by
  unfold normalizeEdge
  split_ifs with h
  · norm_num
  · exact lt_of_le_of_ne p.2.property.2 h

theorem edgePoint_normalize (p : EdgeParameters n) : edgePoint (normalizeEdge p) = edgePoint p := by
  unfold normalizeEdge
  split_ifs with h
  · simp [edgePoint, h]
  · rfl

def edgePhase (p : EdgeParameters n) : AddCircle (n : ℝ) :=
  ((p.1.val : ℝ) + p.2.val : ℝ)

theorem edgePhase_normalize (p : EdgeParameters n) : edgePhase (normalizeEdge p) = edgePhase p := by
  unfold normalizeEdge
  split_ifs with h
  · by_cases hi : p.1.val+1 < n
    · simp only [edgePhase, cyclicNext, Nat.mod_eq_of_lt hi, Nat.cast_add, Nat.cast_one, add_zero, h]
    · have hi' : p.1.val+1 = n := by omega
      simp only [edgePhase, cyclicNext, hi', Nat.mod_self, Nat.cast_zero, add_zero, h]
      have he : (p.1.val : ℝ)+1 = n := by exact_mod_cast hi'
      rw [he]
      exact (AddCircle.coe_period (n : ℝ)).symm
  · rfl

theorem edgePhase_injective_halfOpen (hn : 0 < n) (p q : EdgeParameters n)
    (hp : p.2.val < 1) (hq : q.2.val < 1) (h : edgePhase p = edgePhase q) : p = q := by
  letI : Fact (0 < (n : ℝ)) := ⟨by exact_mod_cast hn⟩
  have bound (r : EdgeParameters n) (hr : r.2.val < 1) :
      (r.1.val : ℝ) + r.2.val ∈ Ico 0 (0+(n : ℝ)) := by
    have hi : (r.1.val : ℝ)+1 ≤ n := by exact_mod_cast r.1.isLt
    constructor
    · exact add_nonneg (Nat.cast_nonneg _) r.2.property.1
    · linarith [r.2.property.1]
  have he := (AddCircle.coe_eq_coe_iff_of_mem_Ico (bound p hp) (bound q hq)).mp h
  have hs : p.1 = q.1 := by
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hi : (p.1.val : ℝ)+1 ≤ q.1.val := by exact_mod_cast hlt
      linarith [q.2.property.1]
    · have hi : (q.1.val : ℝ)+1 ≤ p.1.val := by exact_mod_cast hgt
      linarith [p.2.property.1]
  exact Prod.ext hs (Subtype.ext (by rw [hs] at he; linarith))

theorem edgePoint_eq_iff_phase (hn : 3 ≤ n) (p q : EdgeParameters n) :
    edgePoint p = edgePoint q ↔ edgePhase p = edgePhase q := by
  constructor
  · intro h
    have he := edgePoint_injective_halfOpen hn (normalizeEdge p) (normalizeEdge q)
      (normalizeEdge_lt p) (normalizeEdge_lt q) (by simpa only [edgePoint_normalize] using h)
    simpa only [edgePhase_normalize] using congrArg edgePhase he
  · intro h
    have he := edgePhase_injective_halfOpen (by omega) (normalizeEdge p) (normalizeEdge q)
      (normalizeEdge_lt p) (normalizeEdge_lt q) (by simpa only [edgePhase_normalize] using h)
    simpa only [edgePoint_normalize] using congrArg edgePoint he

theorem continuous_edgePoint : Continuous (edgePoint (n := n)) := by
  unfold edgePoint
  fun_prop

theorem continuous_edgePhase : Continuous (edgePhase (n := n)) := by
  unfold edgePhase
  exact (AddCircle.continuous_mk' _).comp
    ((continuous_of_discreteTopology (f := fun i : Fin n => (i.val : ℝ))).comp
      continuous_fst |>.add continuous_snd.subtype_val)

theorem edgePhase_surjective (hn : 0 < n) : Function.Surjective (edgePhase (n := n)) := by
  letI : Fact (0 < (n : ℝ)) := ⟨by exact_mod_cast hn⟩
  intro z
  let t := AddCircle.equivIco (n : ℝ) 0 z
  have ht0 : 0 ≤ t.val := t.property.1
  have htn : t.val < (n : ℝ) := by simpa using t.property.2
  have hfloor := Nat.floor_le ht0
  have hceil := Nat.lt_floor_add_one t.val
  have hidx : ⌊t.val⌋₊ < n := by exact_mod_cast (lt_of_le_of_lt hfloor htn)
  refine ⟨(⟨⌊t.val⌋₊, hidx⟩, ⟨t.val-⌊t.val⌋₊, by constructor <;> linarith⟩), ?_⟩
  change (((⌊t.val⌋₊ : ℝ) + (t.val-⌊t.val⌋₊) : ℝ) : AddCircle (n : ℝ)) = z
  rw [add_sub_cancel]
  exact AddCircle.coe_equivIco (p := (n : ℝ)) (a := 0) (y := z)

/-- The coordinate polygon, including every closed edge. -/
def cyclicPolygon (n : Nat) : Set (Point (Fin n)) := range edgePoint

def polygonMap (hn : 0 < n) (z : AddCircle (n : ℝ)) : cyclicPolygon n :=
  ⟨edgePoint (Function.surjInv (edgePhase_surjective hn) z), ⟨_, rfl⟩⟩

theorem polygonMap_phase (hn : 3 ≤ n) (p : EdgeParameters n) :
    (polygonMap (by omega) (edgePhase p)).val = edgePoint p := by
  apply (edgePoint_eq_iff_phase hn _ _).mpr
  exact Function.surjInv_eq (edgePhase_surjective (by omega)) _

theorem continuous_polygonMap (hn : 3 ≤ n) : Continuous (polygonMap (n := n) (by omega)) := by
  apply (continuous_edgePhase.isClosedMap.isQuotientMap continuous_edgePhase
    (edgePhase_surjective (by omega))).continuous_iff.mpr
  apply Continuous.subtype_mk
  exact continuous_edgePoint.congr (fun p => (polygonMap_phase hn p).symm)

theorem polygonMap_bijective (hn : 3 ≤ n) :
    Function.Bijective (polygonMap (n := n) (by omega)) := by
  constructor
  · intro z w h
    have he := (edgePoint_eq_iff_phase hn _ _).mp (congrArg Subtype.val h)
    simpa only [Function.surjInv_eq] using he
  · rintro ⟨x, p, rfl⟩
    exact ⟨edgePhase p, Subtype.ext (polygonMap_phase hn p)⟩

/-- A cyclic coordinate polygon with at least three vertices is a circle. -/
def polygonHomeomorph (hn : 3 ≤ n) : AddCircle (n : ℝ) ≃ₜ cyclicPolygon n := by
  letI : Fact (0 < (n : ℝ)) := ⟨by exact_mod_cast (show 0 < n by omega)⟩
  exact (continuous_polygonMap hn).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (polygonMap (by omega)) (polygonMap_bijective hn))

def circlePolygonHomeomorph (hn : 3 ≤ n) : Circle ≃ₜ cyclicPolygon n :=
  (AddCircle.homeomorphCircle (by exact_mod_cast (show n ≠ 0 by omega))).symm.trans
    (polygonHomeomorph hn)

#print axioms circlePolygonHomeomorph

end Venn17.Topology.Coordinates
