import VennTopology.ClassifiedSurface
import VennTopology.PolygonEulerLowerBound
import VennTopology.EulerSphereCriterion
import VennTopology.NormalizationEuler

/-! The certified diagram is homeomorphic to the metric two-sphere.
The endpoint Euler count is preserved along the actual normalization trace,
and excludes every positive-genus closed canonical model. -/

noncomputable section
namespace Venn19.Topology
open LeanEval.Topology.ClassificationOfSurfaces

theorem diagram_normal_form_eq_sphere_of_euler_preserved
    (h : PolygonVertices.eulerCharacteristic diagramPresentation =
      PolygonVertices.eulerCharacteristic diagramNormalization.normalForm.canonicalPresentation) :
    diagramNormalization.normalForm = .sphere :=
  PolygonVertices.normalForm_eq_sphere_of_euler_ge_two _ diagramNormalization.admissible
    diagram_normal_form_closed (h ▸ PolygonVertices.diagram_polygon_euler_lower_bound)

def canonicalSphereHomeomorphOfEq (N : NormalForm) (ha : N.IsEvalAdmissible) (h : N = .sphere) :
    N.canonicalPresentation.PolygonalRealization (N.canonicalPresentation_isSurfaceValid ha) ≃ₜ
      SphereRepresentative := by
  subst N
  exact NormalForm.canonicalSphereRealizationHomeomorph

/-- The intermediate construction from a normalization-invariance
equality. It is instantiated below by
the proved normalization-invariance theorem. -/
def diagramSphereHomeomorphOfEulerPreserved
    (h : PolygonVertices.eulerCharacteristic diagramPresentation =
      PolygonVertices.eulerCharacteristic diagramNormalization.normalForm.canonicalPresentation) :
    Diagram ≃ₜ SphereRepresentative :=
  diagramCanonicalHomeomorph.trans (canonicalSphereHomeomorphOfEq _ diagramNormalization.admissible
    (diagram_normal_form_eq_sphere_of_euler_preserved h))

/-- Euler characteristic is preserved along this diagram's actual certified trace. -/
theorem diagram_normalization_euler_preserved :
    PolygonVertices.eulerCharacteristic diagramPresentation =
      PolygonVertices.eulerCharacteristic diagramNormalization.normalForm.canonicalPresentation :=
  PolygonVertices.eulerCharacteristic_normalForm diagramNormalization

theorem diagram_normal_form_eq_sphere : diagramNormalization.normalForm = .sphere :=
  diagram_normal_form_eq_sphere_of_euler_preserved diagram_normalization_euler_preserved

/-- Unconditional global sphere homeomorphism for the certified input diagram. -/
def diagramSphereHomeomorph : Diagram ≃ₜ SphereRepresentative :=
  diagramSphereHomeomorphOfEulerPreserved diagram_normalization_euler_preserved

theorem diagram_polygon_euler_characteristic :
    PolygonVertices.eulerCharacteristic diagramPresentation = 2 := by
  rw [diagram_normalization_euler_preserved, diagram_normal_form_eq_sphere]
  exact PolygonVertices.sphere_euler_characteristic

theorem diagram_polygon_vertex_count :
    Nat.card (PolygonVertices.Vertex diagramPresentation) = 1048574 := by
  have h := diagram_polygon_euler_characteristic
  have he := diagram_presentation_edge_count
  have hf := diagram_presentation_face_count
  unfold PolygonVertices.eulerCharacteristic at h
  omega

#print axioms diagramSphereHomeomorph
end Venn19.Topology
