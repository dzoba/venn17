import VennTopology.UnorientedEuler
import VennTopology.P1Euler
import VennTopology.P2Euler
import ClassificationOfSurfaces.NormalForm

/-! Euler characteristic is invariant under every validity-safe move used by
the certified surface normalization algorithm. -/

namespace Venn19.Topology.PolygonVertices
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation

theorem eulerCharacteristic_subdivisionStep {P Q : FiniteCyclicPresentation}
    (h : SubdivisionStep P Q) (valid : P.IsSurfaceValid) :
    eulerCharacteristic P = eulerCharacteristic Q := by
  have validQ := h.isSurfaceValid valid
  rcases h with hiso | hp1 | hp2
  · obtain ⟨e⟩ := hiso
    exact eulerCharacteristic_signedIso e validQ
  · obtain ⟨a, ⟨e⟩⟩ := hp1
    exact (eulerCharacteristic_expand P valid a).symm.trans
      (eulerCharacteristic_signedIso e validQ)
  · obtain ⟨cut, _, ⟨e⟩⟩ := hp2
    exact (eulerCharacteristic_split P valid cut).symm.trans
      (eulerCharacteristic_signedIso e validQ)

theorem eulerCharacteristic_subdivides {P Q : FiniteCyclicPresentation}
    (h : Subdivides P Q) (valid : P.IsSurfaceValid) :
    eulerCharacteristic P = eulerCharacteristic Q := by
  induction h with
  | refl => rfl
  | tail h hstep ih =>
    exact ih.trans (eulerCharacteristic_subdivisionStep hstep (Subdivides.isSurfaceValid h valid))

theorem eulerCharacteristic_commonSubdivision {P Q : FiniteCyclicPresentation}
    (h : HasCommonSubdivision P Q) (validP : P.IsSurfaceValid) (validQ : Q.IsSurfaceValid) :
    eulerCharacteristic P = eulerCharacteristic Q := by
  obtain ⟨R, hp, hq⟩ := h
  exact (eulerCharacteristic_subdivides hp validP).trans
    (eulerCharacteristic_subdivides hq validQ).symm

theorem eulerCharacteristic_normalizationStep {P Q : ValidPresentation}
    (h : NormalizationStep P Q) :
    eulerCharacteristic P.presentation = eulerCharacteristic Q.presentation := by
  cases h with
  | commonSubdivision h => exact eulerCharacteristic_commonSubdivision h P.valid Q.valid
  | unoriented h =>
    rcases h with hf | hb
    · obtain ⟨e⟩ := hf
      exact eulerCharacteristic_unorientedIso e Q.valid
    · obtain ⟨e⟩ := hb
      exact (eulerCharacteristic_unorientedIso e P.valid).symm
  | oneSidedP2 cut _ => exact (eulerCharacteristic_split _ P.valid cut).symm

theorem eulerCharacteristic_normalizationEquivalent {P Q : ValidPresentation}
    (h : NormalizationEquivalent P Q) :
    eulerCharacteristic P.presentation = eulerCharacteristic Q.presentation := by
  induction h with
  | rel _ _ h => exact eulerCharacteristic_normalizationStep h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem eulerCharacteristic_normalForm {P : ValidPresentation} (result : NormalizationResult P) :
    eulerCharacteristic P.presentation = eulerCharacteristic result.normalForm.canonicalPresentation :=
  eulerCharacteristic_normalizationEquivalent
    (Q := canonicalValidPresentation result.normalForm result.admissible) result.equivalent

#print axioms eulerCharacteristic_normalForm
end Venn19.Topology.PolygonVertices
