import VennTopology.PolygonVertices
import Mathlib.Data.List.Cycle

/-! Boundary walks describe the endpoint relations without choosing a starting
side or traversal direction. They will be used to compare subdivision moves. -/

noncomputable section
namespace Venn19.Topology.PolygonVertices
open LeanEval.Topology.ClassificationOfSurfaces SurfaceCellComplex
open FiniteCyclicPresentation

variable {α β γ : Type*}

def WordWalk (v : SignedDart α → β) : List (SignedDart α) → β → β → Prop
  | [], x, y => x = y
  | d :: w, x, y => x = v d ∧ WordWalk v w (v d.flip) y

def WordCloses (v : SignedDart α → β) (w : List (SignedDart α)) : Prop :=
  Cycle.Chain (fun a b => v a.flip = v b) (w : Cycle (SignedDart α))

theorem wordWalk_append (v : SignedDart α → β) (a b : List (SignedDart α)) (x y : β) :
    WordWalk v (a ++ b) x y ↔ ∃ z, WordWalk v a x z ∧ WordWalk v b z y := by
  induction a generalizing x with
  | nil => simp [WordWalk]
  | cons d a ih => simp only [List.cons_append, WordWalk, ih]; aesop

theorem wordWalk_chain (v : SignedDart α → β) (a b : SignedDart α)
    (w : List (SignedDart α)) :
    WordWalk v w (v a.flip) (v b) ↔
      List.IsChain (fun a b => v a.flip = v b) (a :: w ++ [b]) := by
  induction w generalizing a with
  | nil => simp [WordWalk]
  | cons d w ih => simp [WordWalk, List.isChain_cons_cons, ih]

theorem wordCloses_cons (v : SignedDart α → β) (d : SignedDart α) (w) :
    WordCloses v (d :: w) ↔ WordWalk v (d :: w) (v d) (v d) := by
  simp only [WordCloses, Cycle.chain_coe_cons, WordWalk, true_and]
  exact (wordWalk_chain v d d w).symm

theorem wordCloses_iff_exists_walk (v : SignedDart α → β) (w)
    (hne : w ≠ []) : WordCloses v w ↔ ∃ x, WordWalk v w x x := by
  cases w with
  | nil => contradiction
  | cons d w =>
    rw [wordCloses_cons]
    simp only [WordWalk, true_and]
    constructor
    · intro h; exact ⟨v d, rfl, h⟩
    · rintro ⟨x, rfl, h⟩; exact h

theorem wordCloses_of_walk {v : SignedDart α → β} {w} {x}
    (h : WordWalk v w x x) : WordCloses v w := by
  cases w with
  | nil => exact Cycle.Chain.nil _
  | cons d w =>
    exact (wordCloses_iff_exists_walk v _ (by simp)).mpr ⟨x, h⟩

theorem wordCloses_rotated (v : SignedDart α → β) {a b}
    (h : a.IsRotated b) : WordCloses v a ↔ WordCloses v b := by
  unfold WordCloses
  rw [Cycle.coe_eq_coe.mpr h]

theorem wordWalk_inverse (v : SignedDart α → β) (w) (x y : β) :
    WordWalk v (inverseWord w) y x ↔ WordWalk v w x y := by
  induction w generalizing x y with
  | nil => simp [inverseWord, WordWalk, eq_comm]
  | cons d w ih =>
    simp only [inverseWord, List.reverse_cons, List.map_append, List.map_singleton]
    rw [wordWalk_append]
    change (∃ z, WordWalk v (inverseWord w) y z ∧ WordWalk v [d.flip] z x) ↔ _
    simp only [ih, WordWalk, SignedDart.flip_flip]
    aesop

theorem wordCloses_inverse (v : SignedDart α → β) (w) :
    WordCloses v (inverseWord w) ↔ WordCloses v w := by
  by_cases hn : w = []
  · subst w; rfl
  · rw [wordCloses_iff_exists_walk _ _ (by simpa [inverseWord] using hn),
      wordCloses_iff_exists_walk _ _ hn]
    simp only [wordWalk_inverse]

/-- The list formulation is exactly the modulo-indexed corner condition. -/
theorem wordCloses_iff_corners (v : SignedDart α → β) (w) :
    WordCloses v w ↔ ∀ i : Fin w.length,
      v (w.get i).flip = v (w.get ⟨(i.val + 1) % w.length, Nat.mod_lt _ i.pos⟩) := by
  cases w with
  | nil => exact ⟨fun _ i => Fin.elim0 i, fun _ => Cycle.Chain.nil _⟩
  | cons d w =>
    rw [WordCloses, Cycle.chain_coe_cons, ← List.cons_append, List.isChain_iff_getElem]
    constructor
    · intro h i
      have hi := i.isLt
      have hil : i.val < w.length + 1 := i.isLt
      have hc := h i.val (by simp; omega)
      by_cases hj : i.val + 1 < (d :: w).length
      · simpa only [List.get_eq_getElem,
          List.getElem_append_left hi, List.getElem_append_left hj,
          Nat.mod_eq_of_lt hj] using hc
      · have he : i.val + 1 = (d :: w).length := by omega
        have hl : ¬ i.val + 1 < (d :: w).length := hj
        simpa only [List.get_eq_getElem,
          List.getElem_append_left hi, List.getElem_append_right (Nat.le_of_not_gt hl),
          he, List.getElem_append, Nat.lt_irrefl, ↓reduceDIte,
          Nat.sub_self, List.getElem_cons_zero, Nat.mod_self] using hc
    · intro h i hi
      have hii : i < (d :: w).length := by simp at hi ⊢; omega
      have hc := h ⟨i, hii⟩
      by_cases hj : i + 1 < (d :: w).length
      · simpa only [List.get_eq_getElem,
          List.getElem_append_left hii, List.getElem_append_left hj,
          Nat.mod_eq_of_lt hj] using hc
      · have he : i + 1 = (d :: w).length := by omega
        simpa only [List.get_eq_getElem,
          List.getElem_append_left hii, List.getElem_append_right (Nat.le_of_not_gt hj),
          he, List.getElem_append, Nat.lt_irrefl, ↓reduceDIte,
          Nat.sub_self, List.getElem_cons_zero, Nat.mod_self] using hc

theorem endpoint_wordCloses (P : FiniteCyclicPresentation) (f : P.Face) :
    WordCloses (endpoint P) (P.boundary f) := by
  rw [wordCloses_iff_corners]
  intro i
  exact corner_eq ⟨f, i⟩

theorem endpoint_oriented_wordCloses (P : FiniteCyclicPresentation) (f : P.OrientedFace) :
    WordCloses (endpoint P) (P.orientedBoundary f) := by
  cases h : f.orientation <;> simp only [orientedBoundary, h, Bool.false_eq_true, ↓reduceIte]
  · exact endpoint_wordCloses P f.face
  · exact (wordCloses_inverse _ _).mpr (endpoint_wordCloses P f.face)

/-- A labeling satisfying every face corner descends to the vertex quotient. -/
def vertexLift {P : FiniteCyclicPresentation} (v : P.Dart → β)
    (h : ∀ f, WordCloses v (P.boundary f)) : Vertex P → β :=
  Quot.lift v (by
    rintro a b ⟨o, rfl, rfl⟩
    exact (wordCloses_iff_corners v _).mp (h o.1) o.2)

theorem wordCloses_append_singleton (v : SignedDart α → β) (w) (d) :
    WordCloses v (w ++ [d]) ↔ WordWalk v w (v d.flip) (v d) := by
  rw [wordCloses_rotated v List.isRotated_append]
  simp only [List.singleton_append, wordCloses_cons, WordWalk, true_and]

theorem wordWalk_map (v : SignedDart γ → β) (f : SignedDart α → SignedDart γ)
    (hf : ∀ d, f d.flip = (f d).flip) (w) (x y : β) :
    WordWalk v (w.map f) x y ↔ WordWalk (v ∘ f) w x y := by
  induction w generalizing x with
  | nil => rfl
  | cons d w ih => simp only [List.map_cons, WordWalk, ih, Function.comp_apply, hf]

theorem wordCloses_map (v : SignedDart γ → β) (f : SignedDart α → SignedDart γ)
    (hf : ∀ d, f d.flip = (f d).flip) (w) :
    WordCloses v (w.map f) ↔ WordCloses (v ∘ f) w := by
  change Cycle.Chain _ ((w : Cycle (SignedDart α)).map f) ↔ _
  rw [Cycle.chain_map]
  simp only [WordCloses, Function.comp_apply, hf]

theorem wordWalk_map_values {v : SignedDart α → β} (f : β → γ) {w x y}
    (h : WordWalk v w x y) : WordWalk (f ∘ v) w (f x) (f y) := by
  induction w generalizing x with
  | nil => exact congrArg f h
  | cons d w ih => exact ⟨congrArg f h.1, ih h.2⟩

theorem wordWalk_end_unique {v : SignedDart α → β} {w x y z}
    (h : WordWalk v w x y) (h' : WordWalk v w x z) : y = z := by
  induction w generalizing x with
  | nil => exact h.symm.trans h'
  | cons d w ih => exact ih h.2 h'.2

theorem wordWalk_endpoints_unique {v : SignedDart α → β} {w x y x' y'}
    (hn : w ≠ []) (h : WordWalk v w x y) (h' : WordWalk v w x' y') :
    x = x' ∧ y = y' := by
  cases w with
  | nil => contradiction
  | cons d w => exact ⟨h.1.trans h'.1.symm, wordWalk_end_unique h.2 h'.2⟩

end Venn19.Topology.PolygonVertices
