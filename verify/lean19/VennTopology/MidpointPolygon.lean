import VennTopology.LabeledPolygon
import VennTopology.CompactParametrization

noncomputable section
namespace Venn19.Topology.Coordinates
open Set
open scoped Classical
variable {I : Type*} {n : Nat}

/-- A repeated pair gives a crossing center; a distinct pair gives an arc midpoint. -/
def pairPoint (p : I × I) : Point I := (1/2 : ℝ) • (vertex p.1 + vertex p.2)

def pairRelabel (v : Fin n → I × I) (x : Point (Fin n)) : Point I :=
  ∑ j : Fin n, x j • pairPoint (v j)

/-- Distinct polygon vertices have disjoint coordinate supports. -/
def DisjointPairs (v : Fin n → I × I) : Prop :=
  ∀ j k, j ≠ k → (v j).1 ≠ (v k).1 ∧ (v j).1 ≠ (v k).2

theorem pairPoint_pivot (p : I × I) : 0 < pairPoint p p.1 := by
  classical
  by_cases h : p.1 = p.2 <;> simp [pairPoint, vertex, h]

theorem pairPoint_off (v : Fin n → I × I) (hv : DisjointPairs v)
    (j k : Fin n) (h : j ≠ k) : pairPoint (v k) (v j).1 = 0 := by
  obtain ⟨h1,h2⟩ := hv j k h
  simp [pairPoint, vertex, h1, h2]

theorem pairRelabel_pivot (v : Fin n → I × I) (hv : DisjointPairs v)
    (x : Point (Fin n)) (j : Fin n) :
    pairRelabel v x (v j).1 = x j * pairPoint (v j) (v j).1 := by
  classical
  simp only [pairRelabel, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_single j
  · intro k _ hk
    rw [pairPoint_off v hv j k (Ne.symm hk), mul_zero]
  · simp

theorem pairRelabel_injective (v : Fin n → I × I) (hv : DisjointPairs v) :
    Function.Injective (pairRelabel v) := by
  intro x y he
  funext j
  have h := congrFun he (v j).1
  rw [pairRelabel_pivot v hv, pairRelabel_pivot v hv] at h
  exact mul_right_cancel₀ (ne_of_gt (pairPoint_pivot (v j))) h

theorem continuous_pairRelabel (v : Fin n → I × I) : Continuous (pairRelabel v) := by
  apply continuous_finsetSum
  intro j _
  exact (continuous_apply j).smul continuous_const

@[simp] theorem pairRelabel_vertex (v : Fin n → I × I) (j : Fin n) :
    pairRelabel v (vertex j) = pairPoint (v j) := by
  classical
  simp [pairRelabel, vertex, ite_smul]

theorem pairRelabel_edgePoint (v : Fin n → I × I) (p : EdgeParameters n) :
    pairRelabel v (edgePoint p) =
      (1-p.2.val) • pairPoint (v p.1) + p.2.val • pairPoint (v (cyclicNext p.1)) := by
  have hadd (x y : Point (Fin n)) : pairRelabel v (x+y) = pairRelabel v x + pairRelabel v y := by
    simp [pairRelabel, add_smul, Finset.sum_add_distrib]
  have hsmul (r : ℝ) (x : Point (Fin n)) : pairRelabel v (r • x) = r • pairRelabel v x := by
    simp [pairRelabel, Finset.smul_sum, mul_smul]
  simp only [edgePoint, hadd, hsmul, pairRelabel_vertex]

def pairPolygon (v : Fin n → I × I) : Set (Point I) :=
  ⋃ j, segment ℝ (pairPoint (v j)) (pairPoint (v (cyclicNext j)))

theorem pairPolygon_eq_range (v : Fin n → I × I) :
    pairPolygon v = range (pairRelabel v ∘ edgePoint) := by
  ext x
  simp only [pairPolygon, mem_iUnion, segment_eq_image_lineMap, mem_image, mem_range,
    Function.comp_apply, pairRelabel_edgePoint, AffineMap.lineMap_apply_module]
  constructor
  · rintro ⟨j,t,ht,he⟩; exact ⟨(j,⟨t,ht⟩),he⟩
  · rintro ⟨⟨j,t⟩,he⟩; exact ⟨j,t.val,t.property,he⟩

/-- The midpoint polygon is a topological circle, with injectivity proved from
its disjoint coordinate supports. This includes the actual curve midpoints. -/
def pairPolygonHomeomorph (v : Fin n → I × I) (hv : DisjointPairs v) (hn : 3 ≤ n) :
    Circle ≃ₜ pairPolygon v := by
  letI : CompactSpace (cyclicPolygon n) :=
    isCompact_iff_compactSpace.mp (isCompact_range (continuous_edgePoint (n := n)))
  let f := fun p : EdgeParameters n => (⟨edgePoint p, ⟨p,rfl⟩⟩ : cyclicPolygon n)
  have hf : Function.Surjective f := by rintro ⟨x,p,rfl⟩; exact ⟨p,rfl⟩
  have he : ∀ p q, (pairRelabel v ∘ edgePoint) p = (pairRelabel v ∘ edgePoint) q ↔ f p = f q := by
    intro p q
    constructor
    · intro h; exact Subtype.ext (pairRelabel_injective v hv h)
    · intro h; exact congrArg (pairRelabel v) (congrArg Subtype.val h)
  exact (circlePolygonHomeomorph hn).trans
    (compactParametrizationHomeomorph f hf (pairRelabel v ∘ edgePoint)
      (continuous_edgePoint.subtype_mk _) ((continuous_pairRelabel v).comp continuous_edgePoint) he) |>.trans
      (Homeomorph.setCongr (pairPolygon_eq_range v).symm)

#print axioms pairPolygonHomeomorph
end Venn19.Topology.Coordinates
