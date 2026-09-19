import VennCore.Checker
import VennCore.Embed

namespace Venn17

/-- Exact supplied JSON, embedded as data rather than read by the proof at runtime.
SHA-256: c178d7bdde6e02b1b0c2780339434095d3633b8bb77a7293e9d575d04ad7ae77. -/
def suppliedJSON : String := input_file% "venn17-local-c3-s2.json"

def suppliedFaces : Array Face := (parse suppliedJSON).toOption.getD #[]

/-- A proposed occurrence for each bit pattern. These are witnesses, not assumptions. -/
def occurrenceWitnesses (faces : Array Face) : Array Nat := Id.run do
  let mut witnesses := Array.replicate (2^17) faces.size
  for f in [:faces.size] do
    for v in faces[f]! do
      witnesses := witnesses.set! v f
  return witnesses

def suppliedOccurrences : Array Nat := occurrenceWitnesses suppliedFaces

def occurrenceCheck : Bool := (Array.range (2^17)).all fun v =>
  let f := suppliedOccurrences[v]!
  f < suppliedFaces.size && suppliedFaces[f]!.contains v

theorem occurrence_check_passes : occurrenceCheck = true := by
  native_decide

/-- Direct mathematical coverage statement, not just a field of a checker report. -/
theorem every_pattern_occurs (v : Nat) (hv : v < 2^17) :
    ∃ f, f < suppliedFaces.size ∧ v ∈ suppliedFaces[f]! := by
  have h := Array.all_eq_true.mp occurrence_check_passes v (by simpa using hv)
  simp only [Array.getElem_range, Bool.and_eq_true, decide_eq_true_eq,
    Array.contains_iff_mem] at h
  exact ⟨suppliedOccurrences[v]!, h⟩

def Square (f : Face) : Prop :=
  f.size = 4 ∧
  ∃ u a b : Nat, a ≠ b ∧ powerOfTwo a = true ∧ powerOfTwo b = true ∧
    f = #[u, u ^^^ a, u ^^^ a ^^^ b, u ^^^ b]

def squareWitnessCheck (f : Face) : Bool :=
  let u := f[0]!
  let a := u ^^^ f[1]!
  let b := u ^^^ f[3]!
  f.size == 4 && a != b && powerOfTwo a && powerOfTwo b &&
    f == #[u, u ^^^ a, u ^^^ a ^^^ b, u ^^^ b]

theorem squareWitnessCheck_sound (f : Face) (h : squareWitnessCheck f = true) :
    Square f := by
  simp only [squareWitnessCheck, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne] at h
  exact ⟨h.1.1.1.1, f[0]!, f[0]! ^^^ f[1]!, f[0]! ^^^ f[3]!,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem square_witnesses_pass : suppliedFaces.all squareWitnessCheck = true := by
  native_decide

theorem every_crossing_is_a_square (f : Face) (hf : f ∈ suppliedFaces) : Square f :=
  squareWitnessCheck_sound f ((Array.all_eq_true_iff_forall_mem.mp square_witnesses_pass) f hf)

/-- Computational theorem about this exact input and the finite checker.
`native_decide` introduces a compiler-trust axiom, printed below. -/
theorem supplied_file_accepted : accepts suppliedJSON = true := by
  native_decide

/-- All named finite checks and the recomputed counts hold on the supplied input.
This is deliberately not stated as a theorem about Jordan curves in ℝ². -/
theorem supplied_file_verified :
    ∃ r, audit suppliedJSON = .ok r ∧ r.Passed :=
  (accepts_iff suppliedJSON).mp supplied_file_accepted

theorem region_count :
    ∃ r, audit suppliedJSON = .ok r ∧ r.regions = 131072 := by
  obtain ⟨r, h, checks⟩ := supplied_file_verified
  exact ⟨r, h, checks.1⟩

#print axioms supplied_file_verified
#print axioms every_pattern_occurs
#print axioms every_crossing_is_a_square

end Venn17
