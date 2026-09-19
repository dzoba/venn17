import VennTopology.CurveLevelSet
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace Venn17.Topology
open Set
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

theorem diagram_region_field_ne_zero (i : Fin 17) (v : Fin 131072)
    {x : Diagram} (hx : x ∈ diagramRegion v) : diagramBitField i x ≠ 0 := by
  intro hz
  exact region_subset_complement v hx
    (mem_iUnion.mpr ⟨i,(diagram_curve_iff_field_zero i x).mpr hz⟩)

/-- Throughout a region, every geometric bit field has the sign of its
certified pattern. -/
theorem diagram_region_field_sign (i : Fin 17) (v : Fin 131072)
    {x : Diagram} (hx : x ∈ diagramRegion v) :
    0 < bitSign i.val v.val * diagramBitField i x := by
  let g : Diagram → ℝ := fun y => bitSign i.val v.val * diagramBitField i y
  have hg : Continuous g := continuous_const.mul (diagramBitField_continuous i)
  have hp : g (patternPoint v) = 1 := by
    dsimp [g]; rw [diagramBitField_pattern,bitSign_sq]
  by_contra! h
  obtain ⟨y,hy,he⟩ := (diagramRegion_pathConnected v).isConnected.isPreconnected.intermediate_value
    hx (patternPoint_mem_region v) hg.continuousOn (show (0 : ℝ) ∈ Icc (g x) (g (patternPoint v)) from
      ⟨h,by rw [hp]; norm_num⟩)
  have hn := diagram_region_field_ne_zero i v hy
  have hs := bitSign_sq i.val v.val
  dsimp [g] at he
  rcases mul_eq_zero.mp he with he | he
  · rw [he] at hs; norm_num at hs
  · exact hn he

theorem diagram_region_positive_iff (i : Fin 17) (v : Fin 131072)
    {x : Diagram} (hx : x ∈ diagramRegion v) :
    0 < diagramBitField i x ↔ v.val.testBit i.val = true := by
  have h := diagram_region_field_sign i v hx
  unfold bitSign at h
  cases hb : v.val.testBit i.val
  · simp only [hb,Bool.false_eq_true,ite_false,neg_one_mul] at h ⊢
    constructor
    · intro hh; linarith
    · intro hh; exact False.elim hh
  · simp only [hb,ite_true,one_mul] at h
    exact ⟨fun _ => rfl,fun _ => h⟩

#print axioms diagram_region_positive_iff
end Venn17.Topology
