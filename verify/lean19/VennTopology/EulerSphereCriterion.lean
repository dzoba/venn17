import VennTopology.CanonicalEuler
import VennTopology.ClosedNormalization

namespace Venn19.Topology.PolygonVertices
open LeanEval.Topology.ClassificationOfSurfaces

/-- Among the admissible closed canonical quotients, Euler characteristic at
least two forces the sphere. The count uses the proved endpoint quotient
cardinality and the actual stored edges and faces. -/
theorem normalForm_eq_sphere_of_euler_ge_two (N : NormalForm)
    (ha : N.IsEvalAdmissible) (hc : PresentationClosedness.EdgeClosed N.canonicalPresentation)
    (he : 2 ≤ eulerCharacteristic N.canonicalPresentation) : N = .sphere := by
  cases N with
  | sphere => rfl
  | orientable p n =>
      have hn := PresentationClosedness.orientable_boundary_zero p n hc
      subst n
      have hp : 0 < p := by
        simp only [NormalForm.IsEvalAdmissible] at ha
        omega
      rw [orientable_euler_characteristic p hp] at he
      omega
  | nonOrientable p n =>
      have hn := PresentationClosedness.nonOrientable_boundary_zero p n hc
      subst n
      have hp : 0 < p := ha
      rw [nonOrientable_euler_characteristic p hp] at he
      omega

theorem closed_canonical_euler_two_iff (N : NormalForm)
    (ha : N.IsEvalAdmissible) (hc : PresentationClosedness.EdgeClosed N.canonicalPresentation) :
    eulerCharacteristic N.canonicalPresentation = 2 ↔ N = .sphere := by
  constructor
  · intro he
    exact normalForm_eq_sphere_of_euler_ge_two N ha hc he.ge
  · rintro rfl
    exact sphere_euler_characteristic

#print axioms normalForm_eq_sphere_of_euler_ge_two
end Venn19.Topology.PolygonVertices
