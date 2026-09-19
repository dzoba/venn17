import VennTopology.ArrangementCertificate
import VennTopology.PuncturedCrossings
import VennTopology.PuncturedSides

namespace Venn17.Topology
open Set

/-- The arrangement and its symmetry survive deleting the all-zero pole.
The plane homeomorphism and Euclidean rotation conjugacy are not
assumptions or conclusions of this theorem. -/
theorem punctured_arrangement_verified :
    (∀ i : Fin 17, ∃ f : Circle → PuncturedDiagram,
      Continuous f ∧ Function.Injective f ∧ Set.range f = puncturedCurve i) ∧
    (∀ v : Fin 131072, IsPathConnected (puncturedRegion v)) ∧
    (∀ x : PuncturedDiagram, x ∈ puncturedComplement ↔ ∃! v : Fin 131072, x ∈ puncturedRegion v) ∧
    Nat.card (ConnectedComponents puncturedComplement) = 131072 ∧
    (∀ i j k : Fin 17, i ≠ j → i ≠ k → j ≠ k → ∀ x : PuncturedDiagram,
      x ∈ puncturedCurve i → x ∈ puncturedCurve j → x ∉ puncturedCurve k) ∧
    (∀ x : PuncturedDiagram,
      (∃ i j : Fin 17, i ≠ j ∧ x ∈ puncturedCurve i ∧ x ∈ puncturedCurve j) ↔
        ∃ f : Fin suppliedModel.oriented.size, x = puncturedCrossingPoint f) ∧
    (∀ i : Fin 17, puncturedRotation '' puncturedCurve i = puncturedCurve (curveRotation i)) ∧
    (∀ v : Fin 131072, puncturedRotation '' puncturedRegion v = puncturedRegion (patternRotation v)) ∧
    (∀ x : PuncturedDiagram, puncturedRotation^[17] x = x) ∧
    (∀ k : Nat, 0 < k → k < 17 → ∃ x : PuncturedDiagram, puncturedRotation^[k] x ≠ x) ∧
    (∀ x : PuncturedDiagram, puncturedRotation x = x ↔ x.val = patternPoint 131071) ∧
    (∀ f : Fin suppliedModel.oriented.size, ∃ i j : Fin 17, i ≠ j ∧
      CrossingSquare.HasCrossingChart (puncturedCurve i) (puncturedCurve j) (puncturedCrossingPoint f)) ∧
    (∀ i : Fin 17, Nat.card (ConnectedComponents (puncturedCurveComplement i)) = 2 ∧
      ∀ b : Bool, IsOpen (puncturedSide i b) ∧ IsPathConnected (puncturedSide i b)) ∧
    (∀ v : Fin 131072, puncturedRegion v = ⋂ i : Fin 17, puncturedSide i (v.val.testBit i.val)) :=
  ⟨punctured_curves_are_embedded_circles,puncturedRegion_pathConnected,
    punctured_complement_unique_region,punctured_complement_component_count,
    punctured_no_triple_intersections,punctured_crossing_iff,
    punctured_rotation_curve_image,punctured_rotation_region_image,
    punctured_rotation_period,punctured_rotation_no_short_period,punctured_rotation_fixed_iff,
    punctured_transverse_crossing,
    fun i => ⟨punctured_curve_complement_component_count i,
      fun b => ⟨puncturedSide_isOpen i b,puncturedSide_pathConnected i b⟩⟩,
    puncturedRegion_eq_sides⟩

#print axioms punctured_arrangement_verified
end Venn17.Topology
