import VennTopology.PolygonWordWalk
import ClassificationOfSurfaces.FiniteCyclicP2

/-! Face subdivision adds one edge and one face, and induces an equivalence
of the actual endpoint quotients. Empty pieces are allowed as long as the
source face itself is nonempty. -/

noncomputable section
namespace Venn19.Topology.PolygonVertices
open LeanEval.Topology.ClassificationOfSurfaces SurfaceCellComplex
open FiniteCyclicPresentation

variable {β : Type*}

/-- Extend an endpoint labeling to the fresh cutting edge. -/
def cuttingLabel {n : ℕ} (v : SignedDart (Fin n) → β) (x y : β) :
    SignedDart (Fin (n + 1)) → β
  | .pos a => Fin.lastCases y (fun a => v (.pos a)) a
  | .neg a => Fin.lastCases x (fun a => v (.neg a)) a

@[simp] theorem cuttingLabel_pos_fresh {n : ℕ} (v : SignedDart (Fin n) → β) (x y : β) :
    cuttingLabel v x y (.pos (Fin.last n)) = y := by simp [cuttingLabel]

@[simp] theorem cuttingLabel_neg_fresh {n : ℕ} (v : SignedDart (Fin n) → β) (x y : β) :
    cuttingLabel v x y (.neg (Fin.last n)) = x := by simp [cuttingLabel]

@[simp] theorem cuttingLabel_cast {n : ℕ} (v : SignedDart (Fin n) → β) (x y : β) (d) :
    cuttingLabel v x y (P1.castSuccDart d) = v d := by
  cases d <;> simp [cuttingLabel, P1.castSuccDart]

theorem wordCloses_storedWord {α : Type*} (v : SignedDart α → β) (b : Bool) (w) :
    WordCloses v (P2.storedWord b w) ↔ WordCloses v w := by
  cases b
  · rfl
  · exact wordCloses_inverse v w

private theorem closes_oriented_iff {P : FiniteCyclicPresentation} (v : P.Dart → β)
    (f : P.OrientedFace) : WordCloses v (P.orientedBoundary f) ↔ WordCloses v (P.boundary f.face) := by
  cases h : f.orientation <;> simp only [orientedBoundary, h, Bool.false_eq_true,
    ↓reduceIte, wordCloses_inverse]

/-- The two child boundary relations recover the parent's boundary relations. -/
theorem split_closes_parent (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (v : SignedDart (Fin (P.edgeCount + 1)) → β)
    (h : ∀ f, WordCloses v ((P2.split P cut).boundary f)) :
    ∀ f, WordCloses (v ∘ P1.castSuccDart) (P.boundary f) := by
  intro f
  by_cases hf : f = cut.face.face
  · subst f
    have hl := h (P2.oldFace P cut cut.face.face)
    have hr := h (P2.rightFace P cut)
    rw [P2.split_boundary_selected, P2.selectedBoundary, wordCloses_storedWord,
      P2.selectedOrientedBoundary, wordCloses_append_singleton,
      P2.retainWord, wordWalk_map _ _ P2.castSuccDart_flip] at hl
    rw [P2.split_boundary_right, P2.rightBoundary, wordCloses_storedWord,
      P2.rightOrientedBoundary, wordCloses_cons] at hr
    change _ ∧ WordWalk v (P2.retainWord cut.right)
      (v (.pos (P2.freshEdge P))) (v (.neg (P2.freshEdge P))) at hr
    rw [P2.retainWord, wordWalk_map _ _ P2.castSuccDart_flip] at hr
    apply (closes_oriented_iff _ cut.face).mp
    apply (wordCloses_rotated _ cut.boundary_rotated).mpr
    exact wordCloses_of_walk ((wordWalk_append _ _ _ _ _).mpr ⟨_, hl, hr.2⟩)
  · have hh := h (P2.oldFace P cut f)
    rw [P2.split_boundary_old_of_ne P cut hf, P2.retainWord,
      wordCloses_map _ _ P2.castSuccDart_flip] at hh
    exact hh

/-- Parent boundary walks extend to both child boundaries. -/
theorem cuttingLabel_closes (P : FiniteCyclicPresentation) (cut : P2Cut P)
    (v : P.Dart → β) (h : ∀ f, WordCloses v (P.boundary f))
    (x y : β) (hl : WordWalk v cut.left x y) (hr : WordWalk v cut.right y x) :
    ∀ f, WordCloses (cuttingLabel v x y) ((P2.split P cut).boundary f) := by
  intro f
  rcases P2.face_cases P cut f with ⟨g, rfl⟩ | rfl
  · rw [P2.split_boundary_old]
    split_ifs with hg
    · rw [P2.selectedBoundary, wordCloses_storedWord, P2.selectedOrientedBoundary,
        wordCloses_append_singleton, P2.retainWord, wordWalk_map _ _ P2.castSuccDart_flip]
      simpa only [Function.comp_def, cuttingLabel_cast, SignedDart.flip,
        P2.freshEdge, P1.freshEdge, cuttingLabel_pos_fresh, cuttingLabel_neg_fresh] using hl
    · rw [P2.retainWord, wordCloses_map _ _ P2.castSuccDart_flip]
      simpa only [Function.comp_def, cuttingLabel_cast] using h g
  · rw [P2.split_boundary_right, P2.rightBoundary, wordCloses_storedWord,
      P2.rightOrientedBoundary, wordCloses_cons]
    change _ ∧ WordWalk (cuttingLabel v x y) (P2.retainWord cut.right) _ _
    refine ⟨rfl, ?_⟩
    rw [P2.retainWord, wordWalk_map _ _ P2.castSuccDart_flip]
    simpa only [Function.comp_def, cuttingLabel_cast, SignedDart.flip,
      P2.freshEdge, P1.freshEdge, cuttingLabel_pos_fresh, cuttingLabel_neg_fresh] using hr

/-- Retained old endpoints define a map into the split vertex quotient. -/
def splitVertexMap (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    Vertex P → Vertex (P2.split P cut) :=
  vertexLift ((endpoint (P2.split P cut)) ∘ P1.castSuccDart)
    (split_closes_parent P cut _ (endpoint_wordCloses _))

@[simp] theorem splitVertexMap_endpoint (P : FiniteCyclicPresentation) (cut : P2Cut P) (d) :
    splitVertexMap P cut (endpoint P d) = endpoint (P2.split P cut) (P1.castSuccDart d) := rfl

theorem split_child_walks (P : FiniteCyclicPresentation) (cut : P2Cut P) :
    WordWalk ((endpoint (P2.split P cut)) ∘ P1.castSuccDart) cut.left
      (endpoint (P2.split P cut) (.neg (P2.freshEdge P))) (endpoint (P2.split P cut) (.pos (P2.freshEdge P))) ∧
    WordWalk ((endpoint (P2.split P cut)) ∘ P1.castSuccDart) cut.right
      (endpoint (P2.split P cut) (.pos (P2.freshEdge P))) (endpoint (P2.split P cut) (.neg (P2.freshEdge P))) := by
  have hl := endpoint_oriented_wordCloses (P2.split P cut)
    ⟨P2.oldFace P cut cut.face.face, cut.face.orientation⟩
  have hr := endpoint_oriented_wordCloses (P2.split P cut)
    ⟨P2.rightFace P cut, cut.face.orientation⟩
  rw [P2.split_orientedBoundary_selected] at hl
  rw [P2.split_orientedBoundary_right] at hr
  change WordCloses (α := Fin (P.edgeCount + 1)) (endpoint (P2.split P cut)) _ at hl hr
  rw [P2.selectedOrientedBoundary, wordCloses_append_singleton,
    P2.retainWord, wordWalk_map _ _ P2.castSuccDart_flip] at hl
  rw [P2.rightOrientedBoundary, wordCloses_cons] at hr
  change _ ∧ WordWalk (endpoint (P2.split P cut)) (P2.retainWord cut.right)
    (endpoint (P2.split P cut) (.pos (P2.freshEdge P))) (endpoint (P2.split P cut) (.neg (P2.freshEdge P))) at hr
  dsimp only [FiniteCyclicPresentation.Dart, FiniteCyclicPresentation.Edge, P2.split] at hr
  rw [P2.retainWord, wordWalk_map _ _ P2.castSuccDart_flip] at hr
  exact ⟨hl, hr.2⟩

/-- A valid face split, including a one-sided degenerate split, preserves
vertices. The empty-word sphere is excluded by source validity. -/
def splitVertexEquiv (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid)
    (cut : P2Cut P) : Vertex P ≃ Vertex (P2.split P cut) := by
  apply Classical.choice
  have hn : cut.left ++ cut.right ≠ [] := by
    intro he
    have hlen := cut.boundary_rotated.perm.length_eq
    rw [orientedBoundary_length, he, List.length_nil] at hlen
    exact valid.2.1 cut.face.face (List.eq_nil_of_length_eq_zero hlen)
  have hc := (wordCloses_rotated (endpoint P) cut.boundary_rotated).mp
    (endpoint_oriented_wordCloses P cut.face)
  obtain ⟨x, hx⟩ := (wordCloses_iff_exists_walk _ _ hn).mp hc
  obtain ⟨y, hl, hr⟩ := (wordWalk_append _ _ _ _ _).mp hx
  let F := splitVertexMap P cut
  let G := vertexLift (P := P2.split P cut) (cuttingLabel (endpoint P) x y)
    (cuttingLabel_closes P cut _ (endpoint_wordCloses P) x y hl hr)
  have hleft : Function.LeftInverse G F := by
    intro z
    induction z using Quot.inductionOn with | _ d =>
      exact cuttingLabel_cast _ x y d
  have hlF := wordWalk_map_values F hl
  have hrF := wordWalk_map_values F hr
  change WordWalk ((endpoint (P2.split P cut)) ∘ P1.castSuccDart) cut.left (F x) (F y) at hlF
  change WordWalk ((endpoint (P2.split P cut)) ∘ P1.castSuccDart) cut.right (F y) (F x) at hrF
  have hends : F x = endpoint (P2.split P cut) (.neg (P2.freshEdge P)) ∧
      F y = endpoint (P2.split P cut) (.pos (P2.freshEdge P)) := by
    by_cases hnl : cut.left = []
    · have hnr : cut.right ≠ [] := by simpa [hnl] using hn
      exact (wordWalk_endpoints_unique hnr hrF (split_child_walks P cut).2).symm
    · exact wordWalk_endpoints_unique hnl hlF (split_child_walks P cut).1
  refine ⟨⟨F, G, hleft, ?_⟩⟩
  intro z
  induction z using Quot.inductionOn with | _ d =>
    change F (cuttingLabel (endpoint P) x y d) = endpoint (P2.split P cut) d
    change SignedDart (Fin (P.edgeCount + 1)) at d
    cases d with
    | pos e =>
      refine Fin.lastCases ?_ (fun a => ?_) e
      · rw [cuttingLabel_pos_fresh]
        exact hends.2
      · change F (cuttingLabel (endpoint P) x y (P1.castSuccDart (.pos a))) = _
        rw [cuttingLabel_cast]
        rfl
    | neg e =>
      refine Fin.lastCases ?_ (fun a => ?_) e
      · rw [cuttingLabel_neg_fresh]
        exact hends.1
      · change F (cuttingLabel (endpoint P) x y (P1.castSuccDart (.neg a))) = _
        rw [cuttingLabel_cast]
        rfl

theorem eulerCharacteristic_split (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid)
    (cut : P2Cut P) : eulerCharacteristic (P2.split P cut) = eulerCharacteristic P := by
  have hv := Nat.card_congr (splitVertexEquiv P valid cut)
  have he := P2.split_edgeCount P cut
  have hf := P2.split_faces_length P cut
  unfold eulerCharacteristic
  omega

#print axioms eulerCharacteristic_split
end Venn19.Topology.PolygonVertices
