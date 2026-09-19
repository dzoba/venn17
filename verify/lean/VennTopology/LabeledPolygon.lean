import VennTopology.CyclicPolygon

noncomputable section
namespace Venn17.Topology.Coordinates

open Set
open scoped Classical
variable {I : Type*} {n : Nat}

/-- Extend coordinates along an injection of the vertex labels. -/
def relabel (v : Fin n → I) (x : Point (Fin n)) : Point I :=
  ∑ j : Fin n, x j • vertex (v j)

theorem relabel_apply (v : Fin n → I) (hv : Function.Injective v)
    (x : Point (Fin n)) (j : Fin n) : relabel v x (v j) = x j := by
  classical
  simp [relabel, Finset.sum_apply, vertex, hv.eq_iff]

theorem relabel_injective (v : Fin n → I) (hv : Function.Injective v) :
    Function.Injective (relabel v) := by
  intro x y h
  funext j
  have := congrFun h (v j)
  simpa only [relabel_apply v hv] using this

theorem continuous_relabel (v : Fin n → I) : Continuous (relabel v) := by
  apply continuous_finsetSum
  intro j _
  exact (continuous_apply j).smul continuous_const

@[simp] theorem relabel_vertex (v : Fin n → I) (j : Fin n) :
    relabel v (vertex j) = vertex (v j) := by
  classical
  simp [relabel, vertex, ite_smul]

theorem relabel_edgePoint (v : Fin n → I) (p : EdgeParameters n) :
    relabel v (edgePoint p) =
      (1-p.2.val) • vertex (v p.1) + p.2.val • vertex (v (cyclicNext p.1)) := by
  have hadd (x y : Point (Fin n)) : relabel v (x+y) = relabel v x + relabel v y := by
    simp [relabel, add_smul, Finset.sum_add_distrib]
  have hsmul (r : ℝ) (x : Point (Fin n)) : relabel v (r • x) = r • relabel v x := by
    simp [relabel, Finset.smul_sum, mul_smul]
  simp only [edgePoint, hadd, hsmul, relabel_vertex]

def labeledPolygon (v : Fin n → I) : Set (Point I) :=
  ⋃ j, segment ℝ (vertex (v j)) (vertex (v (cyclicNext j)))

theorem labeledPolygon_eq_range (v : Fin n → I) :
    labeledPolygon v = range (relabel v ∘ edgePoint) := by
  ext x
  simp only [labeledPolygon, mem_iUnion, segment_eq_image_lineMap,
    mem_image, mem_range, Function.comp_apply, relabel_edgePoint,
    AffineMap.lineMap_apply_module]
  constructor
  · rintro ⟨j, t, ht, he⟩
    exact ⟨(j, ⟨t, ht⟩), he⟩
  · rintro ⟨⟨j,t⟩, he⟩
    exact ⟨j, t.val, t.property, he⟩

def labeledPolygonMap (v : Fin n → I) (hn : 3 ≤ n) (z : Circle) : Point I :=
  relabel v (circlePolygonHomeomorph hn z).val

theorem continuous_labeledPolygonMap (v : Fin n → I) (hn : 3 ≤ n) :
    Continuous (labeledPolygonMap v hn) :=
  (continuous_relabel v).comp (continuous_subtype_val.comp (circlePolygonHomeomorph hn).continuous)

theorem labeledPolygonMap_injective (v : Fin n → I) (hv : Function.Injective v) (hn : 3 ≤ n) :
    Function.Injective (labeledPolygonMap v hn) :=
  (relabel_injective v hv).comp (Subtype.val_injective.comp (circlePolygonHomeomorph hn).injective)

theorem range_labeledPolygonMap (v : Fin n → I) (hn : 3 ≤ n) :
    range (labeledPolygonMap v hn) = labeledPolygon v := by
  rw [labeledPolygon_eq_range]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨p, hp⟩ := (circlePolygonHomeomorph hn z).property
    exact ⟨p, congrArg (relabel v) hp⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨z, hz⟩ := (circlePolygonHomeomorph hn).surjective ⟨edgePoint p, ⟨p, rfl⟩⟩
    exact ⟨z, congrArg (fun y : cyclicPolygon n => relabel v y.val) hz⟩

/-- Cycles of distinct coordinate vertices are embedded circles in their actual
ambient real coordinate space. -/
def labeledPolygonHomeomorph (v : Fin n → I) (hv : Function.Injective v) (hn : 3 ≤ n) :
    Circle ≃ₜ labeledPolygon v :=
  ((continuous_labeledPolygonMap v hn).subtype_mk _).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (Set.rangeFactorization (labeledPolygonMap v hn))
      ⟨Set.rangeFactorization_injective.mpr (labeledPolygonMap_injective v hv hn),
        Set.rangeFactorization_surjective⟩) |>.trans
    (Homeomorph.setCongr (range_labeledPolygonMap v hn))

#print axioms labeledPolygonHomeomorph

end Venn17.Topology.Coordinates
