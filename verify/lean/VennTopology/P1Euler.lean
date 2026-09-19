import VennTopology.PolygonWordWalk
import ClassificationOfSurfaces.FiniteCyclicP1

/-! Edge subdivision replaces an old edge by two edges and creates exactly
one new vertex. The new midpoint is kept distinct in the endpoint quotient. -/

noncomputable section
namespace Venn17.Topology.PolygonVertices
open LeanEval.Topology.ClassificationOfSurfaces SurfaceCellComplex
open FiniteCyclicPresentation

variable {β : Type*}

/-- Choose the expanded endpoint corresponding to an original endpoint. -/
def retainedDart {n : ℕ} (a : Fin n) : SignedDart (Fin n) → SignedDart (Fin (n + 1))
  | .pos e => .pos e.castSucc
  | .neg e => if e = a then .neg (Fin.last n) else .neg e.castSucc

/-- Original endpoint values together with an independent midpoint value. -/
def subdivisionLabel {n : ℕ} (a : Fin n) (v : SignedDart (Fin n) → β) (m : β) :
    SignedDart (Fin (n + 1)) → β
  | .pos e => Fin.lastCases m (fun e => v (.pos e)) e
  | .neg e => Fin.lastCases (v (.neg a)) (fun e => if e = a then m else v (.neg e)) e

@[simp] theorem subdivisionLabel_retained {n : ℕ} (a : Fin n)
    (v : SignedDart (Fin n) → β) (m : β) (d) :
    subdivisionLabel a v m (retainedDart a d) = v d := by
  cases d with
  | pos e => simp [retainedDart, subdivisionLabel]
  | neg e => by_cases h : e = a <;> simp [retainedDart, subdivisionLabel, h]

@[simp] theorem subdivisionLabel_mid {n : ℕ} (a : Fin n)
    (v : SignedDart (Fin n) → β) (m : β) :
    subdivisionLabel a v m (.pos (Fin.last n)) = m := by simp [subdivisionLabel]

theorem wordWalk_expandDart {n : ℕ} (a : Fin n) (v : SignedDart (Fin n) → β)
    (m x y : β) (d) :
    WordWalk (subdivisionLabel a v m) (P1.expandDart a d) x y ↔
      x = v d ∧ v d.flip = y := by
  cases d with
  | pos e => by_cases h : e = a <;>
      simp [P1.expandDart, h, WordWalk, subdivisionLabel, P1.firstSubedge, P1.freshEdge, SignedDart.flip]
  | neg e => by_cases h : e = a <;>
      simp [P1.expandDart, h, WordWalk, subdivisionLabel, P1.firstSubedge, P1.freshEdge, SignedDart.flip]

theorem wordWalk_expandWord {n : ℕ} (a : Fin n) (v : SignedDart (Fin n) → β)
    (m : β) (w) (x y : β) :
    WordWalk (subdivisionLabel a v m) (P1.expandWord a w) x y ↔ WordWalk v w x y := by
  induction w generalizing x with
  | nil => rfl
  | cons d w ih =>
    rw [P1.expandWord_cons, wordWalk_append]
    simp only [wordWalk_expandDart, ih, WordWalk]
    aesop

theorem wordCloses_expandWord {n : ℕ} (a : Fin n) (v : SignedDart (Fin n) → β)
    (m : β) (w) :
    WordCloses (subdivisionLabel a v m) (P1.expandWord a w) ↔ WordCloses v w := by
  by_cases hn : w = []
  · subst w; exact ⟨fun _ => Cycle.Chain.nil _, fun _ => Cycle.Chain.nil _⟩
  · rw [wordCloses_iff_exists_walk _ _ (fun h => hn ((P1.expandWord_eq_nil_iff a w).mp h)),
      wordCloses_iff_exists_walk _ _ hn]
    simp only [wordWalk_expandWord]

theorem subdivisionLabel_reconstruct {n : ℕ} (a : Fin n)
    (v : SignedDart (Fin (n + 1)) → β)
    (h : v (.neg a.castSucc) = v (.pos (Fin.last n))) :
    subdivisionLabel a (v ∘ retainedDart a) (v (.pos (Fin.last n))) = v := by
  funext d
  cases d with
  | pos e =>
    refine Fin.lastCases ?_ (fun b => ?_) e
    · simp [subdivisionLabel]
    · simp [subdivisionLabel, retainedDart]
  | neg e =>
    refine Fin.lastCases ?_ (fun b => ?_) e
    · simp [subdivisionLabel, retainedDart]
    · by_cases hb : b = a
      · subst b; simpa [subdivisionLabel] using h.symm
      · simp [subdivisionLabel, retainedDart, hb]

/-- Any occurrence of the subdivided edge identifies the two representations
of its midpoint. Validity ensures such an occurrence exists. -/
theorem subdivision_midpoint_eq (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid)
    (a : P.Edge) : endpoint (P1.expand P a) (.neg a.castSucc) =
      endpoint (P1.expand P a) (.pos (Fin.last P.edgeCount)) := by
  classical
  have hpos : 0 < (P.edgeOccurrences a).card := by
    rw [P.card_edgeOccurrences]
    rcases valid.2.2.2 a with h | h <;> omega
  obtain ⟨o, ho⟩ := Finset.card_pos.mp hpos
  have hedge := (P.mem_edgeOccurrences a o).mp ho
  have hd : o.dart ∈ P.boundary o.1 := List.get_mem _ _
  obtain ⟨u, w, hw⟩ := List.mem_iff_append.mp hd
  have hc := endpoint_wordCloses (P1.expand P a) (P1.faceEquiv P a o.1)
  rw [P1.expand_boundary] at hc
  have hne := (P1.expand_isSurfaceValid P a valid).2.1 (P1.faceEquiv P a o.1)
  rw [P1.expand_boundary] at hne
  obtain ⟨x, hx⟩ := (wordCloses_iff_exists_walk _ _ hne).mp hc
  rw [hw, P1.expandWord_append, P1.expandWord_cons, wordWalk_append] at hx
  obtain ⟨y, _, hy⟩ := hx
  obtain ⟨z, hz, _⟩ := (wordWalk_append _ _ _ _ _).mp hy
  change edgeOfDart o.dart = a at hedge
  cases he : o.dart with
  | pos b =>
    have hb : b = a := by simpa only [he, edgeOfDart] using hedge
    subst b
    rw [he, P1.expandDart_pos_self] at hz
    exact hz.2.1
  | neg b =>
    have hb : b = a := by simpa only [he, edgeOfDart] using hedge
    subst b
    rw [he, P1.expandDart_neg_self] at hz
    exact hz.2.1.symm

theorem retainedLabel_closes (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid)
    (a : P.Edge) (f : P.Face) :
    WordCloses ((endpoint (P1.expand P a)) ∘ retainedDart a) (P.boundary f) := by
  have hc := endpoint_wordCloses (P1.expand P a) (P1.faceEquiv P a f)
  rw [P1.expand_boundary] at hc
  have he := subdivisionLabel_reconstruct a (endpoint (P1.expand P a))
    (subdivision_midpoint_eq P valid a)
  rw [← he] at hc
  exact (wordCloses_expandWord a _ _ _).mp hc

/-- The vertex set after edge subdivision is exactly the old vertex set
plus one distinct midpoint. -/
def expandVertexEquiv (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid)
    (a : P.Edge) : Vertex (P1.expand P a) ≃ Vertex P ⊕ Unit := by
  let label := subdivisionLabel a (Sum.inl ∘ endpoint P) (Sum.inr ())
  have hlabel : ∀ f, WordCloses label ((P1.expand P a).boundary f) := by
    intro f
    obtain ⟨g, rfl⟩ := (P1.faceEquiv P a).surjective f
    rw [P1.expand_boundary]
    apply (wordCloses_expandWord a _ _ _).mpr
    have hc := endpoint_wordCloses P g
    obtain ⟨x, hx⟩ := (wordCloses_iff_exists_walk _ _ (valid.2.1 g)).mp hc
    exact wordCloses_of_walk (wordWalk_map_values Sum.inl hx)
  let F := vertexLift (P := P1.expand P a) label hlabel
  let old := vertexLift ((endpoint (P1.expand P a)) ∘ retainedDart a)
    (retainedLabel_closes P valid a)
  let G : Vertex P ⊕ Unit → Vertex (P1.expand P a) :=
    Sum.elim old (fun _ => endpoint (P1.expand P a) (.pos (Fin.last P.edgeCount)))
  refine ⟨F, G, ?_, ?_⟩
  · intro z
    induction z using Quot.inductionOn with | _ d =>
      change G (label d) = endpoint (P1.expand P a) d
      change SignedDart (Fin (P.edgeCount + 1)) at d
      cases d with
      | pos e =>
        refine Fin.lastCases ?_ (fun b => ?_) e
        · change G (subdivisionLabel a _ _ (.pos (Fin.last P.edgeCount))) = _
          rw [subdivisionLabel_mid]
          rfl
        · simp only [label, subdivisionLabel, Fin.lastCases_castSucc]
          rfl
      | neg e =>
        refine Fin.lastCases ?_ (fun b => ?_) e
        · simp only [label, subdivisionLabel, Fin.lastCases_last]
          change endpoint (P1.expand P a) (retainedDart a (.neg a)) = _
          simp [retainedDart]
        · by_cases hb : b = a
          · subst b
            simp only [label, subdivisionLabel, Fin.lastCases_castSucc, ↓reduceIte]
            exact (subdivision_midpoint_eq P valid a).symm
          · simp only [label, subdivisionLabel, Fin.lastCases_castSucc, if_neg hb]
            change endpoint (P1.expand P a) (retainedDart a (.neg b)) = _
            simp [retainedDart, hb]
  · intro z
    cases z with
    | inl z =>
      induction z using Quot.inductionOn with | _ d =>
        exact subdivisionLabel_retained a (Sum.inl ∘ endpoint P) (Sum.inr ()) d
    | inr z => cases z; exact subdivisionLabel_mid a _ _

theorem expand_vertex_count (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid)
    (a : P.Edge) : Nat.card (Vertex (P1.expand P a)) = Nat.card (Vertex P) + 1 := by
  rw [Nat.card_congr (expandVertexEquiv P valid a), Nat.card_sum]
  simp

theorem eulerCharacteristic_expand (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid)
    (a : P.Edge) : eulerCharacteristic (P1.expand P a) = eulerCharacteristic P := by
  have hv := expand_vertex_count P valid a
  have he := P1.expand_edgeCount P a
  have hf := P1.expand_faces_length P a
  unfold eulerCharacteristic
  omega

#print axioms eulerCharacteristic_expand
end Venn17.Topology.PolygonVertices
