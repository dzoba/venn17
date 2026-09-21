import VennTopology.CrossingCharts
import VennTopology.PuncturedArrangement

noncomputable section
namespace Venn19.Topology
open Set
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

def puncturedCenterStar (f : Fin suppliedModel.oriented.size) : Set PuncturedDiagram :=
  Subtype.val ⁻¹' diagramQuad.centerStar f

/-- Deleting the all-zero region vertex does not affect any crossing star. -/
def puncturedCenterStarHomeomorph (f : Fin suppliedModel.oriented.size) :
    puncturedCenterStar f ≃ₜ diagramQuad.centerStar f where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,by
    intro he
    have hp : 0 < x.val.val (.inr f) := x.property
    rw [he] at hp
    simp [patternPoint,Quad.point] at hp⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def puncturedCrossingChart (f : Fin suppliedModel.oriented.size) :
    puncturedCenterStar f ≃ₜ CrossingSquare.square :=
  (puncturedCenterStarHomeomorph f).trans
    (diagramQuad.centerSquareChart f (diagram_corners_injective f))

theorem punctured_transverse_crossing (f : Fin suppliedModel.oriented.size) :
    ∃ i j : Fin 19, i ≠ j ∧ CrossingSquare.HasCrossingChart
      (puncturedCurve i) (puncturedCurve j) (puncturedCrossingPoint f) := by
  obtain ⟨i,j,hij,hi,hj⟩ := crossing_labels_alternate suppliedModel.oriented 524288 19
    supplied_curve_labels_verified supplied_crossing_labels_verified f
  refine ⟨i,j,hij,puncturedCenterStar f,
    (diagramQuad.open_star_isOpen (.inr f)).preimage continuous_subtype_val,?_,
    puncturedCrossingChart f,?_,?_,?_⟩
  · change 0 < Quad.point (.inr f) (.inr f)
    simp [Quad.point]
  · intro x hx
    apply diagramQuad.centerSquareChart_center f (diagram_corners_injective f)
      (puncturedCenterStarHomeomorph f x)
    exact congrArg (fun z : PuncturedDiagram => z.val.val) hx
  · intro x
    change (puncturedCenterStarHomeomorph f x).val ∈ diagramCurve i ↔ _
    rw [diagramCurve_original,Quad.centerStar_curve_iff]
    apply Iff.trans (exists_congr (fun k => and_congr (hi k) Iff.rfl))
    exact diagramQuad.centerSquareChart_even_axis f (diagram_corners_injective f)
      (puncturedCenterStarHomeomorph f x)
  · intro x
    change (puncturedCenterStarHomeomorph f x).val ∈ diagramCurve j ↔ _
    rw [diagramCurve_original,Quad.centerStar_curve_iff]
    apply Iff.trans (exists_congr (fun k => and_congr (hj k) Iff.rfl))
    exact diagramQuad.centerSquareChart_odd_axis f (diagram_corners_injective f)
      (puncturedCenterStarHomeomorph f x)

#print axioms punctured_transverse_crossing
end Venn19.Topology
