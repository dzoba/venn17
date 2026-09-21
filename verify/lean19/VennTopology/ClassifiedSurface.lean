import VennTopology.PolygonalModel
import VennTopology.ClosedNormalization

noncomputable section
namespace Venn19.Topology
open LeanEval.Topology.ClassificationOfSurfaces

/-- Retain the normalization trace for the pending Euler-invariance argument,
rather than only exposing the classification disjunction. -/
def diagramNormalization :
    FiniteCyclicPresentation.NormalizationResult ⟨diagramPresentation, diagram_presentation_valid⟩ :=
  FiniteCyclicPresentation.normalizeConnectedToCanonical
    ⟨diagramPresentation, diagram_presentation_valid⟩ diagram_presentation_connected

def diagramCanonicalHomeomorph : Diagram ≃ₜ
    diagramNormalization.normalForm.canonicalPresentation.PolygonalRealization
      (diagramNormalization.normalForm.canonicalPresentation_isSurfaceValid
        diagramNormalization.admissible) :=
  diagramPolygonalHomeomorph.symm.trans diagramNormalization.realizationHomeomorph

theorem diagram_normal_form_closed :
    PresentationClosedness.EdgeClosed diagramNormalization.normalForm.canonicalPresentation :=
  PresentationClosedness.normalForm_closed diagramNormalization diagram_presentation_edge_multiplicity

/-- Actual global surface classification for this diagram. The non-spherical
alternatives are closed and have positive genus. Excluding those alternatives
using the proved Euler characteristic is still a separate obligation. -/
theorem diagram_closed_classification :
    Nonempty (Diagram ≃ₜ SphereRepresentative) ∨
      (∃ p, 1 ≤ p ∧ Nonempty (Diagram ≃ₜ Quot (OrientableRel p 0))) ∨
      (∃ p, 1 ≤ p ∧ Nonempty (Diagram ≃ₜ Quot (NonOrientableRel p 0))) := by
  have h := PresentationClosedness.closed_classification diagramPresentation
    diagram_presentation_valid diagram_presentation_connected diagram_presentation_edge_multiplicity
  rcases h with hs | ⟨p, hp, ⟨e⟩⟩ | ⟨p, hp, ⟨e⟩⟩
  · obtain ⟨e⟩ := hs
    exact Or.inl ⟨diagramPolygonalHomeomorph.symm.trans e⟩
  · exact Or.inr (Or.inl ⟨p, hp, ⟨diagramPolygonalHomeomorph.symm.trans e⟩⟩)
  · exact Or.inr (Or.inr ⟨p, hp, ⟨diagramPolygonalHomeomorph.symm.trans e⟩⟩)

/-- This packages the two proved facts without silently identifying the
simplicial Euler count with an invariant of a normal-form representative. -/
theorem diagram_classification_and_euler_verified :
    geometricEulerCharacteristic diagramQuad = 2 ∧
    (Nonempty (Diagram ≃ₜ SphereRepresentative) ∨
      (∃ p, 1 ≤ p ∧ Nonempty (Diagram ≃ₜ Quot (OrientableRel p 0))) ∨
      (∃ p, 1 ≤ p ∧ Nonempty (Diagram ≃ₜ Quot (NonOrientableRel p 0)))) :=
  ⟨diagram_euler_characteristic, diagram_closed_classification⟩

#print axioms diagram_closed_classification
#print axioms diagramCanonicalHomeomorph
#print axioms diagram_classification_and_euler_verified
end Venn19.Topology
