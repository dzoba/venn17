import VennTopology.CurveGeometry
import VennTopology.Surface

noncomputable section
namespace Venn19.Topology
open Set
open scoped Classical
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons

def diagramEncodedHomeomorph : Diagram ≃ₜ Coordinates.realization (encodedCells suppliedModel.oriented 524288) :=
  encodedSpaceHomeomorph _ _ supplied_corners_bounded

/-- Curve `i` consists exactly of the arms of every triangle whose region edge
flips bit `i`. This is a subset of the original geometric surface. -/
def diagramCurve (i : Fin 19) : Set Diagram :=
  {x | (diagramEncodedHomeomorph x).val ∈ encodedCurve suppliedModel.oriented 524288 i.val}

def curveInSurfaceHomeomorph (fs : Array Face) (n i : Nat) :
    {x : Coordinates.realization (encodedCells fs n) // x.val ∈ encodedCurve fs n i} ≃ₜ encodedCurve fs n i :=
  (subtypeConjunction _ (fun x => x ∈ encodedCurve fs n i)).trans
    (Homeomorph.setCongr (by
      ext x
      exact ⟨fun h => h.2, fun h => ⟨encodedCurve_subset_space fs n i h,h⟩⟩))

/-- An actual circle homeomorphism for each of the 19 labelled curves. The range
covers all of that label's center-to-midpoint arms, with none omitted. -/
def diagramCurveHomeomorph (i : Fin 19) : Circle ≃ₜ diagramCurve i :=
  (encodedCurveHomeomorph suppliedModel.oriented 524288 i.val
    (suppliedCurvePolygons.getD i.val default) (each_curve_polygon_verified i).1).trans
    (curveInSurfaceHomeomorph _ _ _).symm |>.trans
    (diagramEncodedHomeomorph.subtype (p := fun x => x ∈ diagramCurve i)
      (q := fun x => x.val ∈ encodedCurve suppliedModel.oriented 524288 i.val)
      (fun _ => Iff.rfl)).symm

def diagramCurveMap (i : Fin 19) (z : Circle) : Diagram := (diagramCurveHomeomorph i z).val

theorem diagramCurveMap_continuous (i : Fin 19) : Continuous (diagramCurveMap i) :=
  continuous_subtype_val.comp (diagramCurveHomeomorph i).continuous

theorem diagramCurveMap_injective (i : Fin 19) : Function.Injective (diagramCurveMap i) :=
  Subtype.val_injective.comp (diagramCurveHomeomorph i).injective

theorem diagramCurveMap_range (i : Fin 19) : Set.range (diagramCurveMap i) = diagramCurve i := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩; exact (diagramCurveHomeomorph i z).property
  · intro hx
    obtain ⟨z,hz⟩ := (diagramCurveHomeomorph i).surjective ⟨x,hx⟩
    exact ⟨z,congrArg Subtype.val hz⟩

theorem diagramCurve_compact (i : Fin 19) : IsCompact (diagramCurve i) := by
  rw [← diagramCurveMap_range]
  exact isCompact_range (diagramCurveMap_continuous i)

theorem diagramCurve_closed (i : Fin 19) : IsClosed (diagramCurve i) :=
  (diagramCurve_compact i).isClosed

/-- All 19 concrete labelled curve sets are simple closed curves on `Diagram`.
Moving them to the plane still requires the global sphere/plane theorem. -/
theorem diagram_curves_are_embedded_circles :
    ∀ i : Fin 19, ∃ f : Circle → Diagram,
      Continuous f ∧ Function.Injective f ∧ Set.range f = diagramCurve i :=
  fun i => ⟨diagramCurveMap i, diagramCurveMap_continuous i,
    diagramCurveMap_injective i, diagramCurveMap_range i⟩

#print axioms diagram_curves_are_embedded_circles
end Venn19.Topology
