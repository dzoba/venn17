import VennTopology.PolygonVertices
import ClassificationOfSurfaces.FiniteCyclicUnorientedRealization

/-! Independent reversal of polygon boundary traversals preserves the actual
vertex quotient and hence the polygon Euler characteristic. -/

noncomputable section
namespace Venn17.Topology.PolygonVertices
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex

private theorem next_surjective (P : FiniteCyclicPresentation) :
    Function.Surjective (@next P) := by
  apply Finite.surjective_of_injective
  rintro ⟨f, i⟩ ⟨g, j⟩ h
  have hfg : f = g := congrArg Sigma.fst h
  subst g
  have hij := congrArg (fun o : P.BoundaryOccurrence => o.2.val) h
  change (i.val + 1) % (P.boundary f).length =
    (j.val + 1) % (P.boundary f).length at hij
  have hm := Nat.ModEq.add_right_cancel' 1 hij
  have hi := i.isLt
  have hj := j.isLt
  have heq : i = j := by
    apply Fin.ext
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hm
  subst j
  rfl

theorem unoriented_mapOccurrence_next_false {P Q : FiniteCyclicPresentation}
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (h : e.reverseFace o.1 = false) :
    e.mapOccurrence validQ (next o) = next (e.mapOccurrence validQ o) := by
  rcases o with ⟨f, i⟩
  dsimp only [UnorientedPresentationIso.mapOccurrence, next]
  congr 1
  apply Fin.ext
  simp only [UnorientedPresentationIso.sideIndex, UnorientedPresentationIso.orientedSideIndex,
    h, Bool.false_eq_true, ↓reduceIte, Fin.val_cast, orientedBoundary_length]
  generalize i.val = k
  rw [e.boundary_length_eq]
  simp only [Nat.mod_add_mod]
  congr 1
  omega

theorem unoriented_next_mapOccurrence_next_true {P Q : FiniteCyclicPresentation}
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (h : e.reverseFace o.1 = true) :
    next (e.mapOccurrence validQ (next o)) = e.mapOccurrence validQ o := by
  rcases o with ⟨f, i⟩
  dsimp only [UnorientedPresentationIso.mapOccurrence, next]
  congr 1
  apply Fin.ext
  simp only [UnorientedPresentationIso.sideIndex, UnorientedPresentationIso.orientedSideIndex,
    h, ↓reduceIte, Fin.val_rev, Fin.val_cast, orientedBoundary_length]
  generalize i.val = k
  rw [e.boundary_length_eq]
  simp only [Nat.mod_add_mod]
  have hn := List.length_pos_of_ne_nil (validQ.2.1 (e.faceEquiv f))
  have hm := Nat.mod_lt (k + e.faceRotation f) hn
  have hm' := Nat.mod_lt (k + 1 + e.faceRotation f) hn
  have hs : k + 1 + e.faceRotation f = k + e.faceRotation f + 1 := by omega
  rw [hs]
  rw [← Nat.mod_add_mod (k + e.faceRotation f) (Q.boundary (e.faceEquiv f)).length 1]
  by_cases he : (k + e.faceRotation f) % (Q.boundary (e.faceEquiv f)).length + 1 =
      (Q.boundary (e.faceEquiv f)).length
  · simp only [he, Nat.mod_self]
    rw [show (Q.boundary (e.faceEquiv f)).length - (0 + 1) + 1 =
      (Q.boundary (e.faceEquiv f)).length by omega, Nat.mod_self]
    omega
  · have ht : (k + e.faceRotation f) % (Q.boundary (e.faceEquiv f)).length + 1 <
        (Q.boundary (e.faceEquiv f)).length := by omega
    rw [Nat.mod_eq_of_lt ht]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem unoriented_corner_eq {P Q : FiniteCyclicPresentation}
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) :
    endpoint Q (e.edgeRelabeling.mapDart o.dart.flip) =
      endpoint Q (e.edgeRelabeling.mapDart (next o).dart) := by
  cases h : e.reverseFace o.1 with
  | false =>
    have hc := corner_eq (e.mapOccurrence validQ o)
    rw [← unoriented_mapOccurrence_next_false e validQ o h] at hc
    simpa only [e.mapOccurrence_dart, next, h, Bool.false_eq_true, ↓reduceIte,
      EdgeRelabeling.mapDart_flip] using hc
  | true =>
    have hc := corner_eq (e.mapOccurrence validQ (next o))
    rw [unoriented_next_mapOccurrence_next_true e validQ o h] at hc
    simpa only [e.mapOccurrence_dart, next, h, ↓reduceIte, SignedDart.flip_flip,
      EdgeRelabeling.mapDart_flip] using hc.symm

theorem unoriented_inverse_corner_eq {P Q : FiniteCyclicPresentation}
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    endpoint P (e.edgeRelabeling.dartEquiv.symm o.dart.flip) =
      endpoint P (e.edgeRelabeling.dartEquiv.symm (next o).dart) := by
  obtain ⟨q, rfl⟩ := (e.occurrenceEquiv validQ).surjective o
  change endpoint P (e.edgeRelabeling.dartEquiv.symm
      (e.mapOccurrence validQ q).dart.flip) =
    endpoint P (e.edgeRelabeling.dartEquiv.symm (next (e.mapOccurrence validQ q)).dart)
  cases h : e.reverseFace q.1 with
  | false =>
    rw [← unoriented_mapOccurrence_next_false e validQ q h]
    simpa only [e.mapOccurrence_dart, next, h, Bool.false_eq_true, ↓reduceIte,
      ← EdgeRelabeling.dartEquiv_apply, ← EdgeRelabeling.dartEquiv_flip,
      Equiv.symm_apply_apply] using corner_eq q
  | true =>
    obtain ⟨p, hp⟩ := next_surjective P q
    have hpf := congrArg (fun o : P.BoundaryOccurrence => o.1) hp
    change p.1 = q.1 at hpf
    have hr : e.reverseFace p.1 = true := hpf ▸ h
    have he := unoriented_next_mapOccurrence_next_true e validQ p hr
    rw [hp] at he
    rw [he, e.mapOccurrence_dart, e.mapOccurrence_dart]
    simp only [h, hr, ↓reduceIte, SignedDart.flip_flip,
      ← EdgeRelabeling.dartEquiv_apply, ← EdgeRelabeling.dartEquiv_flip,
      Equiv.symm_apply_apply]
    exact (hp ▸ corner_eq p).symm

/-- Face traversal reversal preserves the equivalence classes of endpoints. -/
def unorientedIsoVertexEquiv {P Q : FiniteCyclicPresentation}
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid) : Vertex P ≃ Vertex Q where
  toFun := Quot.lift (fun d => endpoint Q (e.edgeRelabeling.dartEquiv d)) (by
    rintro a b ⟨o, rfl, rfl⟩
    exact unoriented_corner_eq e validQ o)
  invFun := Quot.lift (fun d => endpoint P (e.edgeRelabeling.dartEquiv.symm d)) (by
    rintro a b ⟨o, rfl, rfl⟩
    exact unoriented_inverse_corner_eq e validQ o)
  left_inv := by
    intro v
    induction v using Quot.inductionOn with | _ d =>
      change endpoint P (e.edgeRelabeling.dartEquiv.symm (e.edgeRelabeling.dartEquiv d)) = _
      rw [Equiv.symm_apply_apply]
      rfl
  right_inv := by
    intro v
    induction v using Quot.inductionOn with | _ d =>
      change endpoint Q (e.edgeRelabeling.dartEquiv (e.edgeRelabeling.dartEquiv.symm d)) = _
      rw [Equiv.apply_symm_apply]
      rfl

theorem eulerCharacteristic_unorientedIso {P Q : FiniteCyclicPresentation}
    (e : UnorientedPresentationIso P Q) (validQ : Q.IsSurfaceValid) :
    eulerCharacteristic P = eulerCharacteristic Q := by
  have hv := Nat.card_congr (unorientedIsoVertexEquiv e validQ)
  have he := Fintype.card_congr e.edgeEquiv
  have hf := Fintype.card_congr e.faceEquiv
  change Fintype.card (Fin P.edgeCount) = Fintype.card (Fin Q.edgeCount) at he
  change Fintype.card (Fin P.faces.length) = Fintype.card (Fin Q.faces.length) at hf
  simp only [Fintype.card_fin] at he hf
  simp only [eulerCharacteristic, hv, he, hf]

#print axioms eulerCharacteristic_unorientedIso
end Venn17.Topology.PolygonVertices
