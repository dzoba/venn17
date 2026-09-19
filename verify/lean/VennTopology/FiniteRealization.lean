import VennTopology.Stars
import ClassificationOfSurfaces.Moise.GeometricTriangulation

/-! Restriction to finitely many coordinates preserves the actual geometric
realization. This connects our coordinate simplices to the concrete barycentric
realizations used by the surface-classification library. -/

noncomputable section
namespace Venn17.Topology.Coordinates
open Set
open scoped Classical
local instance finiteCoordinatesDecidableEq {I : Type*} : DecidableEq I := Classical.decEq _
local instance finiteCoordinatesNatDecidableEq : DecidableEq Nat := Classical.decEq _
local instance finiteCoordinatesFinDecidableEq (N : Nat) : DecidableEq (Fin N) := Classical.decEq _

theorem mem_simplex_iff {I : Type*} {s : Finset I} {x : Point I} :
    x ∈ simplex s ↔ (∀ i, 0 ≤ x i) ∧ (∑ i ∈ s, x i = 1) ∧
      (∀ i ∉ s, x i = 0) := by
  classical
  constructor
  · intro hx
    exact ⟨simplex_nonneg hx, simplex_sum hx, fun _ hi => simplex_zero hx hi⟩
  · rintro ⟨hn, hs, hz⟩
    have h := (convex_convexHull ℝ (vertex '' (s : Set I))).sum_mem
      (fun i _ => hn i) hs (fun i hi => vertex_mem_simplex hi)
    have he : (∑ i ∈ s, x i • vertex i) = x := by
      ext j
      by_cases hj : j ∈ s
      · simp [Finset.sum_apply, vertex, hj]
      · simp [Finset.sum_apply, vertex, hj, hz j hj]
    exact he ▸ h

namespace FiniteCoordinates

def cell (N : Nat) (s : Finset Nat) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i.val ∈ s)

@[simp] theorem mem_cell {N : Nat} {s : Finset Nat} {i : Fin N} :
    i ∈ cell N s ↔ i.val ∈ s := by simp [cell]

theorem map_cell {N : Nat} {s : Finset Nat} (hs : ∀ i ∈ s, i < N) :
    (cell N s).map Fin.valEmbedding = s := by
  ext i
  simp only [Finset.mem_map, mem_cell, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hi
    exact ⟨⟨i, hs i hi⟩, hi, rfl⟩

theorem cell_card {N : Nat} {s : Finset Nat} (hs : ∀ i ∈ s, i < N) :
    (cell N s).card = s.card := by
  simpa using congrArg Finset.card (map_cell hs)

theorem cell_erase {N : Nat} (s : Finset Nat) (i : Fin N) :
    cell N (s.erase i.val) = (cell N s).erase i := by
  classical
  ext j
  simp [Finset.mem_erase, ← Fin.val_inj]

def restrict (N : Nat) (x : Point Nat) : Point (Fin N) := fun i => x i.val

def extend (N : Nat) (x : Point (Fin N)) : Point Nat :=
  fun i => if h : i < N then x ⟨i, h⟩ else 0

@[simp] theorem extend_apply {N : Nat} (x : Point (Fin N)) (i : Fin N) :
    extend N x i.val = x i := by simp [extend]

theorem restrict_mem {N : Nat} {s : Finset Nat} (hs : ∀ i ∈ s, i < N)
    {x : Point Nat} (hx : x ∈ simplex s) : restrict N x ∈ simplex (cell N s) := by
  apply mem_simplex_iff.mpr
  refine ⟨fun i => simplex_nonneg hx i.val, ?_, fun i hi => simplex_zero hx (by simpa using hi)⟩
  have h := simplex_sum hx
  rw [← map_cell hs, Finset.sum_map] at h
  exact h

theorem extend_mem {N : Nat} {s : Finset Nat} (hs : ∀ i ∈ s, i < N)
    {x : Point (Fin N)} (hx : x ∈ simplex (cell N s)) : extend N x ∈ simplex s := by
  apply mem_simplex_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro i
    dsimp [extend]
    split
    · exact simplex_nonneg hx _
    · exact le_refl 0
  · rw [← map_cell hs, Finset.sum_map]
    simpa using simplex_sum hx
  · intro i hi
    dsimp [extend]
    split
    · exact simplex_zero hx (by simpa using hi)
    · rfl

theorem continuous_restrict (N : Nat) : Continuous (restrict N) :=
  continuous_pi fun i => continuous_apply i.val

theorem continuous_extend (N : Nat) : Continuous (extend N) := by
  apply continuous_pi
  intro i
  by_cases hi : i < N
  · simpa [extend, hi] using (continuous_apply (⟨i, hi⟩ : Fin N))
  · simpa [extend, hi] using (continuous_const : Continuous (fun _ : Point (Fin N) => (0 : ℝ)))

theorem restrict_link_image {T : Type*} (cells : T → Finset Nat) (N : Nat)
    (hb : ∀ t i, i ∈ cells t → i < N) (v : Fin N) :
    restrict N '' link cells v.val = link (fun t => cell N (cells t)) v := by
  classical
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, hv, ht⟩ := mem_iUnion₂.mp hy
    refine mem_iUnion₂.mpr ⟨t, mem_cell.mpr hv, ?_⟩
    have h := restrict_mem (N := N) (s := (cells t).erase v.val)
      (fun i hi => hb t i (Finset.mem_of_mem_erase hi)) ht
    exact (cell_erase (cells t) v) ▸ h
  · intro hx
    obtain ⟨t, hv, ht⟩ := mem_iUnion₂.mp hx
    refine ⟨extend N x, mem_iUnion₂.mpr ⟨t, mem_cell.mp hv, ?_⟩, ?_⟩
    · apply extend_mem (N := N) (s := (cells t).erase v.val)
        (fun i hi => hb t i (Finset.mem_of_mem_erase hi))
      exact (cell_erase (cells t) v).symm ▸ ht
    · funext i
      exact extend_apply x i

def homeomorph {T : Type*} (cells : T → Finset Nat) (N : Nat)
    (hb : ∀ t i, i ∈ cells t → i < N) :
    realization cells ≃ₜ realization (fun t => cell N (cells t)) where
  toFun x := ⟨restrict N x.val, by
    obtain ⟨t, ht⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨t, restrict_mem (hb t) ht⟩⟩
  invFun x := ⟨extend N x.val, by
    obtain ⟨t, ht⟩ := mem_iUnion.mp x.property
    exact mem_iUnion.mpr ⟨t, extend_mem (hb t) ht⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    obtain ⟨t, ht⟩ := mem_iUnion.mp x.property
    by_cases hi : i < N
    · simp [extend, restrict, hi]
    · simp [extend, hi, simplex_zero ht (fun hm => hi (hb t i hm))]
  right_inv x := by
    apply Subtype.ext
    funext i
    exact extend_apply x.val i
  continuous_toFun := (continuous_restrict N).comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun := (continuous_extend N).comp continuous_subtype_val |>.subtype_mk _

end FiniteCoordinates

open LeanEval.Topology.ClassificationOfSurfaces

theorem simplex_eq_geometricFace {I : Type*} [Fintype I] (s : Finset I) :
    simplex s = GeometricFace I s := by
  classical
  ext x
  rw [mem_simplex_iff]
  constructor
  · rintro ⟨hn, hs, hz⟩
    refine ⟨⟨hn, ?_⟩, hz⟩
    exact (Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hz i hi)).symm.trans hs
  · rintro ⟨⟨hn, hs⟩, hz⟩
    exact ⟨hn, (Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => hz i hi)).trans hs, hz⟩

def geometricFaces {I T : Type*} [Fintype T] (cells : T → Finset I) : Finset (Finset I) :=
  Finset.univ.image cells

theorem realization_eq_geometricRealization {I T : Type*} [Fintype I] [Fintype T]
    (cells : T → Finset I) :
    realization cells = GeometricRealization I (geometricFaces cells) := by
  ext x
  simp only [realization, mem_iUnion, simplex_eq_geometricFace, GeometricFace,
    mem_setOf_eq, GeometricRealization, geometricFaces, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨t, hx, ht⟩
    exact ⟨hx, cells t, ⟨t, rfl⟩, ht⟩
  · rintro ⟨hx, _, ⟨t, rfl⟩, ht⟩
    exact ⟨t, hx, ht⟩

end Venn17.Topology.Coordinates
