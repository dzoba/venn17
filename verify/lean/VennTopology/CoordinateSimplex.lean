import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Contractible

noncomputable section
namespace Venn17.Topology.Coordinates

open Set
open scoped Classical
variable {I : Type*}

abbrev Point (I : Type*) := I → ℝ

def vertex (i : I) : Point I := by
  classical
  exact fun j => if j = i then 1 else 0

@[simp] theorem vertex_self (i : I) : vertex i i = 1 := by simp [vertex]

theorem vertex_other {i j : I} (h : j ≠ i) : vertex i j = 0 := by
  classical
  simp [vertex, h]

def simplex (s : Finset I) : Set (Point I) := convexHull ℝ (vertex '' (s : Set I))

theorem vertex_mem_simplex {s : Finset I} {i : I} (hi : i ∈ s) : vertex i ∈ simplex s :=
  subset_convexHull ℝ _ (mem_image_of_mem _ hi)

theorem simplex_mono {s t : Finset I} (h : s ⊆ t) : simplex s ⊆ simplex t :=
  convexHull_mono (image_mono h)

theorem simplex_nonneg {s : Finset I} {x : Point I} (hx : x ∈ simplex s) (i : I) :
    0 ≤ x i := by
  apply convexHull_min (t := {x : Point I | 0 ≤ x i}) _ _ hx
  · rintro _ ⟨j, _, rfl⟩
    classical
    simp only [vertex, mem_setOf_eq]
    split <;> norm_num
  · intro x hx y hy a b ha hb _
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

theorem simplex_le_one {s : Finset I} {x : Point I} (hx : x ∈ simplex s) (i : I) :
    x i ≤ 1 := by
  apply convexHull_min (t := {x : Point I | x i ≤ 1}) _ _ hx
  · rintro _ ⟨j, _, rfl⟩
    classical
    simp only [vertex, mem_setOf_eq]
    split <;> norm_num
  · intro x hx y hy a b ha hb hab
    change a * x i + b * y i ≤ 1
    change x i ≤ 1 at hx
    change y i ≤ 1 at hy
    nlinarith

theorem simplex_zero {s : Finset I} {x : Point I} (hx : x ∈ simplex s)
    {i : I} (hi : i ∉ s) : x i = 0 := by
  apply convexHull_min (t := {x : Point I | x i = 0}) _ _ hx
  · rintro _ ⟨j, hj, rfl⟩
    change j ∈ s at hj
    exact vertex_other (fun h => hi (h ▸ hj))
  · intro x hx y hy a b _ _ _
    change a * x i + b * y i = 0
    simp_all

theorem simplex_sum {s : Finset I} {x : Point I} (hx : x ∈ simplex s) :
    ∑ i ∈ s, x i = 1 := by
  classical
  apply convexHull_min (t := {x : Point I | ∑ i ∈ s, x i = 1}) _ _ hx
  · rintro _ ⟨j, hj, rfl⟩
    change j ∈ s at hj
    simp [vertex, hj]
  · intro x hx y hy a b _ _ hab
    change ∑ i ∈ s, (a * x i + b * y i) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx, hy]
    simpa using hab

theorem simplex_has_positive_coordinate {s : Finset I} {x : Point I}
    (hx : x ∈ simplex s) : ∃ i ∈ s, 0 < x i := by
  by_contra! h
  have hsum := Finset.sum_nonpos h
  rw [simplex_sum hx] at hsum
  norm_num at hsum

theorem simplex_split {s : Finset I} {i : I} (hi : i ∈ s)
    (hne : (s.erase i).Nonempty) {x : Point I} (hx : x ∈ simplex s) :
    ∃ y ∈ simplex (s.erase i), ∃ a b : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • vertex i + b • y = x := by
  classical
  have hs : (s : Set I) = insert i (s.erase i : Set I) := by simp [hi]
  unfold simplex at hx
  rw [hs, image_insert_eq, convexHull_insert (hne.to_set.image vertex),
    mem_convexJoin] at hx
  obtain ⟨_, rfl, y, hy, hxy⟩ := hx
  exact ⟨y, hy, hxy⟩

end Venn17.Topology.Coordinates
