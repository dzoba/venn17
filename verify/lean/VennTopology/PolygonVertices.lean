import ClassificationOfSurfaces.FiniteCyclicSignedRealization
import Mathlib.SetTheory.Cardinal.Finite

/-! Vertices of a polygon presentation are equivalence classes of edge
endpoints. A positive dart names the initial endpoint of its oriented edge;
the negative dart names the other endpoint. Consecutive sides of each face
identify the terminal endpoint of one side with the initial endpoint of the
next, including the last-to-first identification of a monogon. -/

noncomputable section
namespace Venn17.Topology.PolygonVertices
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation

def next {P : FiniteCyclicPresentation} (o : P.BoundaryOccurrence) : P.BoundaryOccurrence :=
  ⟨o.1, ⟨(o.2.val + 1) % (P.boundary o.1).length, Nat.mod_lt _ o.2.pos⟩⟩

def CornerRel (P : FiniteCyclicPresentation) (a b : P.Dart) : Prop :=
  ∃ o : P.BoundaryOccurrence, a = o.dart.flip ∧ b = (next o).dart

abbrev Vertex (P : FiniteCyclicPresentation) := Quot (CornerRel P)

def endpoint (P : FiniteCyclicPresentation) (d : P.Dart) : Vertex P := Quot.mk _ d

theorem corner_eq {P : FiniteCyclicPresentation} (o : P.BoundaryOccurrence) :
    endpoint P o.dart.flip = endpoint P (next o).dart :=
  Quot.sound ⟨o, rfl, rfl⟩

/-- An actual finite quotient cardinality, not an assigned genus formula. -/
def eulerCharacteristic (P : FiniteCyclicPresentation) : ℤ :=
  (Nat.card (Vertex P) : ℤ) - P.edgeCount + P.faces.length

theorem mapOccurrence_next {P Q : FiniteCyclicPresentation} (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    e.mapOccurrence validQ (next o) = next (e.mapOccurrence validQ o) := by
  rcases o with ⟨f, i⟩
  dsimp only [SignedPresentationIso.mapOccurrence, next]
  congr 1
  apply Fin.ext
  change (((i.val + 1) % (P.boundary f).length) + e.faceRotation f) %
      (Q.boundary (e.faceEquiv f)).length =
    ((i.val + e.faceRotation f) % (Q.boundary (e.faceEquiv f)).length + 1) %
      (Q.boundary (e.faceEquiv f)).length
  generalize i.val = k
  rw [e.boundary_length_eq]
  simp only [Nat.mod_add_mod]
  congr 1
  omega

theorem cornerRel_signedIso_iff {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid) (a b : P.Dart) :
    CornerRel P a b ↔ CornerRel Q (e.edgeRelabeling.dartEquiv a) (e.edgeRelabeling.dartEquiv b) := by
  constructor
  · rintro ⟨o, rfl, rfl⟩
    refine ⟨e.mapOccurrence validQ o, ?_, ?_⟩
    · simp only [EdgeRelabeling.dartEquiv_apply, EdgeRelabeling.mapDart_flip,
        e.mapOccurrence_dart]
    · rw [← mapOccurrence_next, e.mapOccurrence_dart]
      rfl
  · rintro ⟨o, ha, hb⟩
    obtain ⟨p, rfl⟩ := (e.occurrenceEquiv validQ).surjective o
    change e.edgeRelabeling.dartEquiv a = (e.mapOccurrence validQ p).dart.flip at ha
    change e.edgeRelabeling.dartEquiv b = (next (e.mapOccurrence validQ p)).dart at hb
    refine ⟨p, e.edgeRelabeling.dartEquiv.injective ?_, e.edgeRelabeling.dartEquiv.injective ?_⟩
    · simpa only [EdgeRelabeling.dartEquiv_apply, EdgeRelabeling.mapDart_flip,
        e.mapOccurrence_dart] using ha
    · simpa only [← mapOccurrence_next, e.mapOccurrence_dart,
        EdgeRelabeling.dartEquiv_apply] using hb

/-- Signed edge relabeling and cyclic rotation preserve the actual endpoint
equivalence classes, including when edge orientations are reversed. -/
def signedIsoVertexEquiv {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid) : Vertex P ≃ Vertex Q :=
  Quot.congr e.edgeRelabeling.dartEquiv (cornerRel_signedIso_iff e validQ)

theorem eulerCharacteristic_signedIso {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid) :
    eulerCharacteristic P = eulerCharacteristic Q := by
  have hv := Nat.card_congr (signedIsoVertexEquiv e validQ)
  have he := Fintype.card_congr e.edgeEquiv
  have hf := Fintype.card_congr e.faceEquiv
  change Fintype.card (Fin P.edgeCount) = Fintype.card (Fin Q.edgeCount) at he
  change Fintype.card (Fin P.faces.length) = Fintype.card (Fin Q.faces.length) at hf
  simp only [Fintype.card_fin] at he hf
  simp only [eulerCharacteristic, hv, he, hf]

#print axioms eulerCharacteristic_signedIso
end Venn17.Topology.PolygonVertices
