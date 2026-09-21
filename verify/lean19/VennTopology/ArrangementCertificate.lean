import VennTopology.SurfaceCertificate
import VennTopology.SideComponents

namespace Venn19.Topology

/-- The concrete labelled arrangement now has embedded circles, exactly one
connected complementary region per pattern, and exactly the specified double
intersection points, each with a transverse-crossing chart. Each circle has
exactly two path-connected sides and regions are exactly their bit-selected
intersections. This is a theorem
on the constructed surface; it does not assume or assert the missing sphere
homeomorphism or planar rotation. -/
theorem realized_arrangement_verified :
    (∀ i : Fin 19, ∃ f : Circle → Diagram,
      Continuous f ∧ Function.Injective f ∧ Set.range f = diagramCurve i) ∧
    (∀ v : Fin 524288, patternPoint v ∈ diagramRegion v ∧ IsPathConnected (diagramRegion v)) ∧
    (∀ x : Diagram, x ∉ ⋃ i : Fin 19, diagramCurve i ↔ ∃! v : Fin 524288, x ∈ diagramRegion v) ∧
    Nat.card (ConnectedComponents diagramComplement) = 524288 ∧
    (∀ i j k : Fin 19, i ≠ j → i ≠ k → j ≠ k → ∀ x : Diagram,
      x ∈ diagramCurve i → x ∈ diagramCurve j → x ∉ diagramCurve k) ∧
    (∀ x : Diagram, (∃ i j : Fin 19, i ≠ j ∧ x ∈ diagramCurve i ∧ x ∈ diagramCurve j) ↔
      ∃ f : Fin suppliedModel.oriented.size, x = crossingPoint f) ∧
    (∀ f : Fin suppliedModel.oriented.size, ∃ i j : Fin 19, i ≠ j ∧ ∀ k : Fin 19,
      crossingPoint f ∈ diagramCurve k ↔ k = i ∨ k = j) ∧
    (∀ f : Fin suppliedModel.oriented.size, ∃ i j : Fin 19, i ≠ j ∧
      CrossingSquare.HasCrossingChart (diagramCurve i) (diagramCurve j) (crossingPoint f)) ∧
    (∀ i : Fin 19, Nat.card (ConnectedComponents (diagramCurveComplement i)) = 2 ∧
      ∀ b : Bool, IsOpen (diagramSide i b) ∧ IsPathConnected (diagramSide i b)) ∧
    (∀ v : Fin 524288, diagramRegion v = ⋂ i : Fin 19, diagramSide i (v.val.testBit i.val)) :=
  ⟨diagram_curves_are_embedded_circles,
    fun v => ⟨patternPoint_mem_region v,diagramRegion_pathConnected v⟩,
    diagram_complement_unique_region,diagram_complement_component_count,
    diagram_no_triple_intersections,diagram_crossing_iff,diagram_crossing_exactly_two,
    diagram_transverse_crossing,
    fun i => ⟨diagram_curve_complement_component_count i,
      fun b => ⟨diagramSide_isOpen i b,diagramSide_pathConnected i b⟩⟩,
    diagramRegion_eq_sides⟩

#print axioms realized_arrangement_verified

end Venn19.Topology
