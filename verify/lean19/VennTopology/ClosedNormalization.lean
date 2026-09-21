import ClassificationOfSurfaces.NormalForm

/-! Closedness is preserved by the actual normalization moves. This excludes
all positive-boundary normal forms without assuming an Euler-invariance or
surface-classification uniqueness theorem. -/

namespace Venn19.Topology.PresentationClosedness
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation

/-- Every edge is paired twice in the polygonal presentation. -/
def EdgeClosed (P : FiniteCyclicPresentation) : Prop := ∀ e, P.edgeMultiplicity e = 2

theorem of_edgeEquiv {P Q : FiniteCyclicPresentation} (e : P.Edge ≃ Q.Edge)
    (h : ∀ a, P.edgeMultiplicity a = Q.edgeMultiplicity (e a)) :
    EdgeClosed P ↔ EdgeClosed Q := by
  constructor
  · intro hp b
    obtain ⟨a, rfl⟩ := e.surjective b
    exact (h a).symm.trans (hp a)
  · intro hq a
    exact (h a).trans (hq (e a))

theorem signedIso_iff {P Q : FiniteCyclicPresentation} (e : SignedPresentationIso P Q) :
    EdgeClosed P ↔ EdgeClosed Q := of_edgeEquiv e.edgeEquiv e.edgeMultiplicity_eq

theorem unorientedIso_iff {P Q : FiniteCyclicPresentation} (e : UnorientedPresentationIso P Q) :
    EdgeClosed P ↔ EdgeClosed Q := of_edgeEquiv e.edgeEquiv e.edgeMultiplicity_eq

theorem expand_iff (P : FiniteCyclicPresentation) (a : P.Edge) :
    EdgeClosed P ↔ EdgeClosed (P1.expand P a) := by
  constructor
  · intro h e
    refine Fin.lastCases ?_ (fun b => ?_) e
    · exact (P1.edgeMultiplicity_expand_freshEdge P a).symm.trans (h a)
    · exact (P1.edgeMultiplicity_expand_castSucc P a b).symm.trans (h b)
  · intro h b
    exact (P1.edgeMultiplicity_expand_castSucc P a b).trans (h b.castSucc)

theorem split_iff (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    EdgeClosed P ↔ EdgeClosed (P2.split P cut) := by
  constructor
  · intro h e
    refine Fin.lastCases ?_ (fun b => ?_) e
    · exact P2.edgeMultiplicity_split_freshEdge P cut
    · exact (P2.edgeMultiplicity_split_castSucc P cut b).symm.trans (h b)
  · intro h b
    exact (P2.edgeMultiplicity_split_castSucc P cut b).trans (h b.castSucc)

theorem subdivisionStep_iff {P Q : FiniteCyclicPresentation} (h : SubdivisionStep P Q) :
    EdgeClosed P ↔ EdgeClosed Q := by
  rcases h with hiso | hp1 | hp2
  · obtain ⟨e⟩ := hiso
    exact signedIso_iff e
  · obtain ⟨a, ⟨e⟩⟩ := hp1
    exact (expand_iff P a).trans (signedIso_iff e)
  · obtain ⟨cut, _, ⟨e⟩⟩ := hp2
    exact (split_iff P cut).trans (signedIso_iff e)

theorem subdivides_iff {P Q : FiniteCyclicPresentation} (h : Subdivides P Q) :
    EdgeClosed P ↔ EdgeClosed Q := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (subdivisionStep_iff h)

theorem commonSubdivision_iff {P Q : FiniteCyclicPresentation} (h : HasCommonSubdivision P Q) :
    EdgeClosed P ↔ EdgeClosed Q := by
  obtain ⟨R, hp, hq⟩ := h
  exact (subdivides_iff hp).trans (subdivides_iff hq).symm

theorem normalizationStep_iff {P Q : ValidPresentation} (h : NormalizationStep P Q) :
    EdgeClosed P.presentation ↔ EdgeClosed Q.presentation := by
  cases h with
  | commonSubdivision h => exact commonSubdivision_iff h
  | unoriented h =>
      rcases h with hf | hb
      · obtain ⟨e⟩ := hf
        exact unorientedIso_iff e
      · obtain ⟨e⟩ := hb
        exact (unorientedIso_iff e).symm
  | oneSidedP2 cut _ => exact split_iff _ cut

theorem normalizationEquivalent_iff {P Q : ValidPresentation} (h : NormalizationEquivalent P Q) :
    EdgeClosed P.presentation ↔ EdgeClosed Q.presentation := by
  induction h with
  | rel _ _ h => exact normalizationStep_iff h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem normalForm_closed {P : ValidPresentation} (result : NormalizationResult P)
    (h : EdgeClosed P.presentation) : EdgeClosed result.normalForm.canonicalPresentation :=
  (normalizationEquivalent_iff result.equivalent).mp h

theorem orientable_boundary_zero (p n : Nat)
    (h : EdgeClosed (NormalForm.orientable p n).canonicalPresentation) : n = 0 := by
  classical
  by_contra hn
  let j : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let e : NormalForm.OrientableEdge p n := .h j
  have hc := h (ofOneFaceWordEdgeEquiv (NormalForm.orientableBoundaryWord p n) e)
  change (ofOneFaceWord (NormalForm.orientableBoundaryWord p n)).edgeMultiplicity _ = 2 at hc
  rw [ofOneFaceWord_edgeMultiplicity, map_edgeOfDart_eq_map_edgeName] at hc
  have hm := NormalForm.orientableBoundaryWord_edge_occurrences p n e
  rw [SurfaceCellComplex.wordEdgeOccurrences_card_eq_count_edgeName] at hm
  change ((NormalForm.orientableBoundaryWord p n).map SurfaceCellComplex.SignedDart.edgeName).count e = 1 at hm
  omega

theorem nonOrientable_boundary_zero (p n : Nat)
    (h : EdgeClosed (NormalForm.nonOrientable p n).canonicalPresentation) : n = 0 := by
  classical
  by_contra hn
  let j : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let e : NormalForm.NonOrientableEdge p n := .h j
  have hc := h (ofOneFaceWordEdgeEquiv (NormalForm.nonOrientableBoundaryWord p n) e)
  change (ofOneFaceWord (NormalForm.nonOrientableBoundaryWord p n)).edgeMultiplicity _ = 2 at hc
  rw [ofOneFaceWord_edgeMultiplicity, map_edgeOfDart_eq_map_edgeName] at hc
  have hm := NormalForm.nonOrientableBoundaryWord_edge_occurrences p n e
  rw [SurfaceCellComplex.wordEdgeOccurrences_card_eq_count_edgeName] at hm
  change ((NormalForm.nonOrientableBoundaryWord p n).map SurfaceCellComplex.SignedDart.edgeName).count e = 1 at hm
  omega

/-- A closed valid connected polygon quotient is a sphere, a positive-genus
closed orientable normal form, or a closed nonorientable normal form. -/
theorem closed_classification (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid)
    (connected : P.IsConnected) (closed : EdgeClosed P) :
    Nonempty (P.PolygonalRealization valid ≃ₜ SphereRepresentative) ∨
      (∃ p, 1 ≤ p ∧ Nonempty (P.PolygonalRealization valid ≃ₜ Quot (OrientableRel p 0))) ∨
      (∃ p, 1 ≤ p ∧ Nonempty (P.PolygonalRealization valid ≃ₜ Quot (NonOrientableRel p 0))) := by
  obtain ⟨N, ha, hPN⟩ := normalizeConnectedToCanonical ⟨P, valid⟩ connected
  have hc := (normalizationEquivalent_iff hPN).mp closed
  obtain ⟨e⟩ := hPN.polygonallyEquivalent
  change EdgeClosed N.canonicalPresentation at hc
  change P.PolygonalRealization valid ≃ₜ
    N.canonicalPresentation.PolygonalRealization (N.canonicalPresentation_isSurfaceValid ha) at e
  cases N with
  | sphere =>
      exact Or.inl ⟨e.trans NormalForm.canonicalSphereRealizationHomeomorph⟩
  | orientable p n =>
      have hz := orientable_boundary_zero p n hc
      subst n
      have hp : 1 ≤ p := by simpa [NormalForm.IsEvalAdmissible] using ha
      exact Or.inr (Or.inl ⟨p, hp, ⟨e.trans (NormalForm.canonicalOrientableRealizationHomeomorph ha)⟩⟩)
  | nonOrientable p n =>
      have hz := nonOrientable_boundary_zero p n hc
      subst n
      exact Or.inr (Or.inr ⟨p, ha, ⟨e.trans (NormalForm.canonicalNonOrientableRealizationHomeomorph ha)⟩⟩)

#print axioms normalizationEquivalent_iff
#print axioms closed_classification
end Venn19.Topology.PresentationClosedness
