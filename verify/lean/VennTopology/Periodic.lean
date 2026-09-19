import VennTopology.Automorphism
import VennTopology.Incidence
import VennCore.Rotation
import Mathlib.Logic.Function.Iterate

namespace Venn17.Topology

theorem steps_eq_iterate (f : Nat → Nat) (n x : Nat) : steps f n x = f^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [steps, ih, Function.iterate_succ_apply']

def equivOfPeriod {X : Type*} (f : X → X) (h : ∀ x, f^[17] x = x) : Equiv.Perm X where
  toFun := f
  invFun := f^[16]
  left_inv x := by simpa only [Function.iterate_succ_apply] using h x
  right_inv x := by simpa only [Function.iterate_succ_apply'] using h x

theorem region_rotation_verified : regionRotationCheck = true := by native_decide

theorem region_period (v : Nat) : regionStep^[17] v = v := by
  by_cases hv : v < 2^17
  · have h := Array.all_eq_true.mp region_rotation_verified v (by simpa using hv)
    simp only [Array.getElem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact (steps_eq_iterate _ _ _).symm.trans h.2
  · have h : ∀ n, regionStep^[n] v = v := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        simp only [regionStep, if_neg hv]
    exact h 17

def regionPermutation : Equiv.Perm Nat := equivOfPeriod regionStep region_period

theorem face_check_at (fs : Array Face) (h : faceRotationCheck fs = true)
    (f : Nat) (hf : f < fs.size) :
    ((rotationWitnesses fs)[f]! < fs.size ∧ faceShift fs (rotationWitnesses fs) f < 4) ∧
    steps (fun f => (rotationWitnesses fs)[f]!) 17 f = f ∧
    ∀ k : Fin 4, regionStep ((fs[f]!)[k.val]!) =
      (fs[(rotationWitnesses fs)[f]!]!)[(k.val + faceShift fs (rotationWitnesses fs) f)%4]! := by
  have h := Array.all_eq_true.mp h f (by simpa using hf)
  simp only [Array.getElem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨h.1.1, h.1.2, ?_⟩
  intro k
  have hh := Array.all_eq_true.mp h.2 k.val (by simp)
  simpa only [Array.getElem!_eq_getD, show (default : Face) = #[] from rfl,
    show (default : Nat) = 0 from rfl, Array.getElem_range, beq_iff_eq] using hh

def faceStep (fs : Array Face) (h : faceRotationCheck fs = true) (f : Fin fs.size) :
    Fin fs.size := ⟨(rotationWitnesses fs)[f.val]!, (face_check_at fs h f.val f.isLt).1.1⟩

theorem faceStep_iterate_val (fs : Array Face) (h : faceRotationCheck fs = true)
    (n : Nat) (f : Fin fs.size) :
    ((faceStep fs h)^[n] f).val = steps (fun i => (rotationWitnesses fs)[i]!) n f.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', steps]
    change (rotationWitnesses fs)[((faceStep fs h)^[n] f).val]! = _
    rw [ih]

theorem face_period (fs : Array Face) (h : faceRotationCheck fs = true) (f : Fin fs.size) :
    (faceStep fs h)^[17] f = f := by
  apply Fin.ext
  rw [faceStep_iterate_val]
  exact (face_check_at fs h f.val f.isLt).2.1

def facePermutation (fs : Array Face) (h : faceRotationCheck fs = true) : Equiv.Perm (Fin fs.size) :=
  equivOfPeriod (faceStep fs h) (face_period fs h)

theorem next_eq_add_one (k : Fin 4) : Quad.next k = k + 1 := rfl

noncomputable def rotationAutomorphism (fs : Array Face) (h : faceRotationCheck fs = true) :
    (quadOfFaces fs).Automorphism where
  vertices := regionPermutation
  faces := facePermutation fs h
  corners f := Equiv.addRight
    (⟨faceShift fs (rotationWitnesses fs) f.val, (face_check_at fs h f.val f.isLt).1.2⟩ : Fin 4)
  next_eq f k := by
    change Quad.next k + _ = Quad.next (k + _)
    simp only [next_eq_add_one]
    ac_rfl
  corner_eq f k := by
    change regionStep ((fs[f.val]!)[k.val]!) =
      (fs[(rotationWitnesses fs)[f.val]!]!)[(k.val + faceShift fs (rotationWitnesses fs) f.val)%4]!
    exact (face_check_at fs h f.val f.isLt).2.2 k

#print axioms rotationAutomorphism

end Venn17.Topology
