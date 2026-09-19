import VennTopology.MeridianArcs

/-! Exact geometric intersections for the meridian system. -/
noncomputable section
namespace Venn17.Topology
open Set Coordinates
open scoped Classical

namespace Coordinates

/-- If two coordinate simplices share at most one vertex, their intersection
contains at most that vertex. This excludes intersections inside edges. -/
theorem simplex_inter_subset_vertex {I : Type*} (s t : Finset I) (p : I)
    (h : ∀ i ∈ s, i ∈ t → i = p) : simplex s ∩ simplex t ⊆ {vertex p} := by
  classical
  rintro x ⟨hs, ht⟩
  have hz (i : I) (hi : i ≠ p) : x i = 0 := by
    by_cases his : i ∈ s
    · exact simplex_zero ht (fun hit => hi (h i his hit))
    · exact simplex_zero hs his
  obtain ⟨a, ha, hpos⟩ := simplex_has_positive_coordinate hs
  have hap : a = p := by
    by_contra hn
    rw [hz a hn] at hpos
    exact lt_irrefl _ hpos
  have hp : p ∈ s := hap ▸ ha
  have hxp : x p = 1 := by
    have he := simplex_sum hs
    rw [Finset.sum_eq_single p (fun i _ hi => hz i hi) (fun hn => (hn hp).elim)] at he
    exact he
  apply mem_singleton_iff.mpr
  ext i
  by_cases hi : i = p
  · subst i; simpa using hxp
  · simp [vertex, hi, hz i hi]

end Coordinates

theorem meridianLabel_injective (k : Fin 17) : Function.Injective (meridianLabel k) := by
  intro i j h
  have hi := meridian_labels_verified.2.2 k (cyclicNext k) (cyclicNext_ne (by decide) k).symm
  have he : (⟨i.val, by omega⟩ : Fin 34) = ⟨j.val, by omega⟩ := hi (by
    simpa only [meridian_boundary_front] using h)
  have hv := congrArg Fin.val he
  exact Fin.ext hv

/-- Different meridians have only the two endpoint labels in common. -/
theorem meridianLabel_shared (k l : Fin 17) (hkl : k ≠ l) (i j : Fin 18)
    (h : meridianLabel k i = meridianLabel l j) :
    (i = 0 ∧ j = 0) ∨ (i = 17 ∧ j = 17) := by
  have hz (k : Fin 17) := (meridian_labels_verified.1 k).1
  have hn (k : Fin 17) := (meridian_labels_verified.1 k).2
  by_cases hi0 : i = 0
  · left
    refine ⟨hi0, meridianLabel_injective l ?_⟩
    simpa [hi0, hz] using h.symm
  by_cases hi17 : i = 17
  · right
    refine ⟨hi17, meridianLabel_injective l ?_⟩
    simpa [hi17, hn] using h.symm
  by_cases hj0 : j = 0
  · have he : i = 0 := meridianLabel_injective k (by simpa [hj0, hz] using h)
    exact (hi0 he).elim
  by_cases hj17 : j = 17
  · have he : i = 17 := meridianLabel_injective k (by simpa [hj17, hn] using h)
    exact (hi17 he).elim
  have hi : 0 < i.val ∧ i.val < 17 := by
    have : i.val ≠ 0 ∧ i.val ≠ 17 := ⟨fun he => hi0 (Fin.ext he), fun he => hi17 (Fin.ext he)⟩
    omega
  have hj : 0 < j.val ∧ j.val < 17 := by
    have : j.val ≠ 0 ∧ j.val ≠ 17 := ⟨fun he => hj0 (Fin.ext he), fun he => hj17 (Fin.ext he)⟩
    omega
  have he : (⟨i.val, by omega⟩ : Fin 34) = ⟨34-j.val, by omega⟩ :=
    meridian_labels_verified.2.2 k l hkl (by
      simpa [meridianBoundaryLabel, show i.val < 18 from i.isLt,
        show ¬34-j.val < 18 by omega, show 34-(34-j.val) = j.val by omega] using h)
  have hv := congrArg Fin.val he
  change i.val = 34 - j.val at hv
  omega

private theorem meridian_edge_shared (k l : Fin 17) (hkl : k ≠ l) (i j : Fin 17)
    (a : Nat)
    (ha : a = meridianLabel k ⟨i.val, by omega⟩ ∨ a = meridianLabel k ⟨i.val+1, by omega⟩)
    (hb : a = meridianLabel l ⟨j.val, by omega⟩ ∨ a = meridianLabel l ⟨j.val+1, by omega⟩) :
    a = if i.val = 0 then 0 else 131071 := by
  rcases ha with rfl | rfl
  · have he : (⟨i.val, by omega⟩ : Fin 18) = 0 := by
      rcases hb with hb | hb <;>
        rcases meridianLabel_shared k l hkl _ _ hb with h | h
      · exact h.1
      · have hv := congrArg Fin.val h.1; change i.val = 17 at hv; omega
      · exact h.1
      · have hv := congrArg Fin.val h.1; change i.val = 17 at hv; omega
    have hi : i.val = 0 := congrArg Fin.val he
    rw [he, if_pos hi, (meridian_labels_verified.1 k).1]
  · have he : (⟨i.val+1, by omega⟩ : Fin 18) = 17 := by
      rcases hb with hb | hb <;>
        rcases meridianLabel_shared k l hkl _ _ hb with h | h
      · have hv := congrArg Fin.val h.1; change i.val + 1 = 0 at hv; omega
      · exact h.1
      · have hv := congrArg Fin.val h.1; change i.val + 1 = 0 at hv; omega
      · exact h.1
    have hi : i.val ≠ 0 := by have := congrArg Fin.val he; norm_num at this; omega
    rw [he, if_neg hi, (meridian_labels_verified.1 k).2]

theorem encoded_meridians_inter_subset (k l : Fin 17) (hkl : k ≠ l) :
    encodedMeridian k ∩ encodedMeridian l ⊆ {vertex 0, vertex 131071} := by
  rintro x ⟨hk, hl⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hk
  obtain ⟨j, hj⟩ := mem_iUnion.mp hl
  have hs : x ∈ simplex {meridianLabel k ⟨i.val, by omega⟩,
      meridianLabel k ⟨i.val+1, by omega⟩} := by
    simpa [simplex, image_insert_eq, image_singleton, convexHull_pair] using hi
  have ht : x ∈ simplex {meridianLabel l ⟨j.val, by omega⟩,
      meridianLabel l ⟨j.val+1, by omega⟩} := by
    simpa [simplex, image_insert_eq, image_singleton, convexHull_pair] using hj
  have hx := simplex_inter_subset_vertex _ _ (if i.val = 0 then 0 else 131071)
    (fun a ha hb => meridian_edge_shared k l hkl i j a (by simpa using ha) (by simpa using hb))
    ⟨hs, ht⟩
  simp only [mem_singleton_iff] at hx
  rw [hx]
  split_ifs <;> simp

/-- Distinct arcs meet at exactly the two poles, including points in edge interiors. -/
theorem diagram_meridians_inter (k l : Fin 17) (hkl : k ≠ l) :
    diagramMeridian k ∩ diagramMeridian l = {patternPoint 0, patternPoint 131071} := by
  apply Subset.antisymm
  · intro x hx
    have he := encoded_meridians_inter_subset k l hkl hx
    simp only [mem_insert_iff, mem_singleton_iff] at he ⊢
    rcases he with he | he
    · left
      apply diagramEncodedHomeomorph.injective
      apply Subtype.ext
      simpa [patternPoint_encoded] using he
    · right
      apply diagramEncodedHomeomorph.injective
      apply Subtype.ext
      simpa [patternPoint_encoded] using he
  · intro x hx
    have hz (m : Fin 17) : patternPoint 0 ∈ diagramMeridian m := by
      rw [← diagramMeridianMap_range]
      exact ⟨⟨0, by norm_num⟩, diagramMeridianMap_zero m⟩
    have hn (m : Fin 17) : patternPoint 131071 ∈ diagramMeridian m := by
      rw [← diagramMeridianMap_range]
      exact ⟨⟨17, by norm_num⟩, diagramMeridianMap_one m⟩
    rcases hx with rfl | hx
    · exact ⟨hz k, hz l⟩
    · rw [mem_singleton_iff] at hx
      subst x
      exact ⟨hn k, hn l⟩

/-- The return half of a boundary is the second meridian with reversed order. -/
theorem meridian_boundary_back (k l : Fin 17) (i : Fin 18) :
    meridianBoundaryLabel k l ⟨(34-i.val)%34, Nat.mod_lt _ (by decide)⟩ =
      meridianLabel l i := by
  fin_cases i <;> simp [meridianBoundaryLabel, meridian_labels_verified.1]

private theorem meridian_boundary_first_edge (k l : Fin 17) (i : Fin 17) :
    segment ℝ (vertex (meridianBoundaryLabel k l ⟨i.val, by omega⟩))
      (vertex (meridianBoundaryLabel k l (cyclicNext ⟨i.val, by omega⟩))) =
    segment ℝ (vertex (meridianLabel k ⟨i.val, by omega⟩))
      (vertex (meridianLabel k ⟨i.val+1, by omega⟩)) := by
  have hn : cyclicNext (⟨i.val, by omega⟩ : Fin 34) = ⟨i.val+1, by omega⟩ := by
    apply Fin.ext
    change (i.val+1)%34 = i.val+1
    exact Nat.mod_eq_of_lt (by omega)
  rw [hn, meridian_boundary_front k l (⟨i.val, by omega⟩ : Fin 18),
    meridian_boundary_front k l (⟨i.val+1, by omega⟩ : Fin 18)]

private theorem meridian_boundary_second_edge (k l : Fin 17) (i : Fin 17) :
    segment ℝ (vertex (meridianBoundaryLabel k l ⟨33-i.val, by omega⟩))
      (vertex (meridianBoundaryLabel k l (cyclicNext ⟨33-i.val, by omega⟩))) =
    segment ℝ (vertex (meridianLabel l ⟨i.val, by omega⟩))
      (vertex (meridianLabel l ⟨i.val+1, by omega⟩)) := by
  have h1 : (⟨33-i.val, by omega⟩ : Fin 34) =
      ⟨(34-(i.val+1))%34, Nat.mod_lt _ (by decide)⟩ := by
    apply Fin.ext; dsimp; omega
  have h2 : cyclicNext (⟨33-i.val, by omega⟩ : Fin 34) =
      ⟨(34-i.val)%34, Nat.mod_lt _ (by decide)⟩ := by
    apply Fin.ext; change (33-i.val+1)%34 = (34-i.val)%34
    congr 1; omega
  rw [h2, h1, meridian_boundary_back k l (⟨i.val+1, by omega⟩ : Fin 18),
    meridian_boundary_back k l (⟨i.val, by omega⟩ : Fin 18), segment_symm]

theorem meridian_boundary_eq_union (k l : Fin 17) :
    labeledPolygon (meridianBoundaryLabel k l) = encodedMeridian k ∪ encodedMeridian l := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    by_cases h : j.val < 17
    · left
      exact mem_iUnion.mpr ⟨⟨j.val, h⟩,
        (meridian_boundary_first_edge k l ⟨j.val, h⟩) ▸ hj⟩
    · right
      let i : Fin 17 := ⟨33-j.val, by omega⟩
      have he : (⟨33-i.val, by omega⟩ : Fin 34) = j := by
        apply Fin.ext; dsimp [i]; omega
      exact mem_iUnion.mpr ⟨i, (meridian_boundary_second_edge k l i) ▸ (he ▸ hj)⟩
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨⟨i.val, by omega⟩, (meridian_boundary_first_edge k l i).symm ▸ hi⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨⟨33-i.val, by omega⟩, (meridian_boundary_second_edge k l i).symm ▸ hi⟩

theorem diagram_meridian_boundary_eq_union (k l : Fin 17) :
    diagramMeridianBoundary k l = diagramMeridian k ∪ diagramMeridian l := by
  ext x
  exact Iff.of_eq (congrArg (fun s => (diagramEncodedHomeomorph x).val ∈ s)
    (meridian_boundary_eq_union k l))

/-- The complete geometric boundary system for the intended sector gluing. -/
theorem diagram_meridian_system :
    (∀ k, Continuous (diagramMeridianMap k) ∧ Function.Injective (diagramMeridianMap k) ∧
      diagramMeridianMap k ⟨0, by norm_num⟩ = patternPoint 0 ∧
      diagramMeridianMap k ⟨17, by norm_num⟩ = patternPoint 131071) ∧
    (∀ k l, k ≠ l → diagramMeridian k ∩ diagramMeridian l =
      {patternPoint 0, patternPoint 131071}) ∧
    (∀ k t, diagramRotation (diagramMeridianMap k t) = diagramMeridianMap (cyclicNext k) t) ∧
    (∀ k l, k ≠ l → ∃ f : Circle → Diagram, Continuous f ∧ Function.Injective f ∧
      range f = diagramMeridian k ∪ diagramMeridian l) := by
  refine ⟨fun k => ⟨diagramMeridianMap_continuous k, diagramMeridianMap_injective k,
    diagramMeridianMap_zero k, diagramMeridianMap_one k⟩, diagram_meridians_inter,
    diagramMeridianMap_rotation, ?_⟩
  intro k l hkl
  simpa only [diagram_meridian_boundary_eq_union] using
    diagram_meridian_boundaries_are_circles k l hkl

#print axioms diagram_meridians_inter
#print axioms diagram_meridian_system
end Venn17.Topology
