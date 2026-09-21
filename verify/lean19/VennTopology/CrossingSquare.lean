import VennTopology.TriangleMidline

noncomputable section
namespace Venn19.Topology.CrossingSquare
open Set

/-- Four nonnegative corner weights, with support on adjacent corners only. -/
def Weights := {a : Fin 4 → ℝ | (∀ k, 0 ≤ a k) ∧
  (a 0 = 0 ∨ a 2 = 0) ∧ (a 1 = 0 ∨ a 3 = 0) ∧ a 0+a 1+a 2+a 3 < 1}

def square : Set (ℝ × ℝ) := {p | |p.1| < 1 ∧ |p.2| < 1}

def flatten (a : Fin 4 → ℝ) : ℝ × ℝ :=
  (a 0-a 1-a 2+a 3, a 0+a 1-a 2-a 3)

def expand (p : ℝ × ℝ) : Fin 4 → ℝ :=
  ![max ((p.1+p.2)/2) 0, max ((p.2-p.1)/2) 0,
    max (-(p.1+p.2)/2) 0, max ((p.1-p.2)/2) 0]

theorem flatten_mem_square (a : Weights) : flatten a.val ∈ square := by
  have h0 := a.property.1 0
  have h1 := a.property.1 1
  have h2 := a.property.1 2
  have h3 := a.property.1 3
  have hs := a.property.2.2.2
  change |a.val 0-a.val 1-a.val 2+a.val 3| < 1 ∧
    |a.val 0+a.val 1-a.val 2-a.val 3| < 1
  constructor <;> rw [abs_lt] <;> constructor <;> linarith

theorem expand_mem (p : square) : (∀ k, 0 ≤ expand p.val k) ∧
    (expand p.val 0 = 0 ∨ expand p.val 2 = 0) ∧
    (expand p.val 1 = 0 ∨ expand p.val 3 = 0) ∧
    expand p.val 0+expand p.val 1+expand p.val 2+expand p.val 3 < 1 := by
  have hx := abs_lt.mp p.property.1
  have hy := abs_lt.mp p.property.2
  refine ⟨fun k => ?_,?_,?_,?_⟩
  · fin_cases k <;> simp [expand]
  · dsimp [expand]
    by_cases h : 0 ≤ p.val.1+p.val.2
    · right; exact max_eq_right (by linarith)
    · left; exact max_eq_right (by linarith)
  · dsimp [expand]
    by_cases h : 0 ≤ p.val.2-p.val.1
    · right; exact max_eq_right (by linarith)
    · left; exact max_eq_right (by linarith)
  · dsimp [expand]
    by_cases h : 0 ≤ p.val.1+p.val.2 <;> by_cases h' : 0 ≤ p.val.2-p.val.1
    all_goals
      repeat' first | rw [max_eq_left (by linarith)] | rw [max_eq_right (by linarith)]
      linarith

theorem expand_flatten (a : Weights) : expand (flatten a.val) = a.val := by
  have h0 := a.property.1 0
  have h1 := a.property.1 1
  have h2 := a.property.1 2
  have h3 := a.property.1 3
  rcases a.property.2.1 with h02 | h02 <;> rcases a.property.2.2.1 with h13 | h13
  all_goals
    funext k
    fin_cases k <;> dsimp [expand,flatten]
    all_goals
      first | rw [max_eq_left (by linarith)] | rw [max_eq_right (by linarith)]
      linarith

theorem flatten_expand (p : ℝ × ℝ) : flatten (expand p) = p := by
  apply Prod.ext <;> dsimp [flatten,expand]
  all_goals
    by_cases h : 0 ≤ p.1+p.2 <;> by_cases h' : 0 ≤ p.2-p.1
    all_goals
      repeat' first | rw [max_eq_left (by linarith)] | rw [max_eq_right (by linarith)]
      linarith

/-- An explicit local crossing model: four triangles around a center form an
open square. The coordinate formulas will identify the labelled arms with axes. -/
def homeomorph : Weights ≃ₜ square where
  toFun a := ⟨flatten a.val,flatten_mem_square a⟩
  invFun p := ⟨expand p.val,expand_mem p⟩
  left_inv a := Subtype.ext (expand_flatten a)
  right_inv p := Subtype.ext (flatten_expand p.val)
  continuous_toFun := by
    apply Continuous.subtype_mk
    have h (k : Fin 4) : Continuous (fun a : Weights => a.val k) :=
      (continuous_apply k).comp continuous_subtype_val
    exact (((h 0).sub (h 1)).sub (h 2) |>.add (h 3)).prodMk
      (((h 0).add (h 1)).sub (h 2) |>.sub (h 3))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    fin_cases k <;> dsimp [expand] <;> fun_prop

theorem square_isOpen : IsOpen square :=
  (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)

/-- Topological transversality of two sets at a point: a homeomorphism from an
open neighborhood to an open plane square sends the point to the origin and
the two sets exactly to the coordinate axes. No differentiability is asserted. -/
def HasCrossingChart {X : Type*} [TopologicalSpace X] (C D : Set X) (p : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ ∃ h : U ≃ₜ square,
    (∀ x : U, x.val = p → (h x).val = (0,0)) ∧
    (∀ x : U, x.val ∈ C ↔ (h x).val.1 = 0) ∧
    (∀ x : U, x.val ∈ D ↔ (h x).val.2 = 0)

#print axioms homeomorph
end Venn19.Topology.CrossingSquare
