import VennTopology.PlaneArrangement
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Covering.Quotient

/-! The cyclic symmetry acts freely away from its unique fixed point. Its
orbit quotient is a genuine 17-sheeted covering, as needed for a construction
of rotation sectors. No conjugacy or classification of periodic maps is assumed. -/

noncomputable section
namespace Venn17.Topology
open Set Function
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

/-- Prime period leaves only fixed points and full-length orbits. -/
theorem minimalPeriod_eq_prime_of_not_fixed {X : Type*} (f : X → X) {p : ℕ}
    (hp : p.Prime) (hperiod : ∀ x, f^[p] x = x) {x : X} (hx : f x ≠ x) :
    minimalPeriod f x = p := by
  have hd := (show IsPeriodicPt f p x from hperiod x).minimalPeriod_dvd
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact (hx ((minimalPeriod_eq_one_iff_isFixedPt.mp h))).elim
  · exact h

theorem planar_minimal_period (x : Plane) (hx : realizedPlaneSymmetry x ≠ x) :
    minimalPeriod realizedPlaneSymmetry x = 17 :=
  minimalPeriod_eq_prime_of_not_fixed _ (by decide) planar_symmetry_period hx

theorem planar_orbit_injective (x : Plane) (hx : realizedPlaneSymmetry x ≠ x) :
    Function.Injective (fun k : Fin 17 => realizedPlaneSymmetry^[k.val] x) := by
  intro i j hij
  apply Fin.ext
  exact (iterate_eq_iterate_iff_of_lt_minimalPeriod
    (by simpa only [planar_minimal_period x hx] using i.isLt)
    (by simpa only [planar_minimal_period x hx] using j.isLt)).mp hij

/-- Remove the one fixed point from the actual plane realization. -/
def freePlaneSet : Set Plane := {x | realizedPlaneSymmetry x ≠ x}
abbrev FreePlane := freePlaneSet

theorem freePlaneSet_isOpen : IsOpen freePlaneSet :=
  isOpen_ne_fun realizedPlaneSymmetry.continuous continuous_id

instance : LocallyCompactSpace FreePlane := freePlaneSet_isOpen.locallyCompactSpace

/-- The restricted symmetry on the free part of the plane. -/
def freePlaneSymmetry : FreePlane ≃ₜ FreePlane :=
  realizedPlaneSymmetry.subtype (fun x => by
    change realizedPlaneSymmetry x ≠ x ↔
      realizedPlaneSymmetry (realizedPlaneSymmetry x) ≠ realizedPlaneSymmetry x
    exact (not_congr realizedPlaneSymmetry.injective.eq_iff).symm)

theorem freePlaneSymmetry_iterate (n : ℕ) (x : FreePlane) :
    (freePlaneSymmetry^[n] x).val = realizedPlaneSymmetry^[n] x.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change realizedPlaneSymmetry ((freePlaneSymmetry^[n] x).val) = _
    rw [ih]

theorem freePlaneSymmetry_period (x : FreePlane) : freePlaneSymmetry^[17] x = x := by
  apply Subtype.ext
  rw [freePlaneSymmetry_iterate, planar_symmetry_period]

theorem freePlane_orbit_injective (x : FreePlane) :
    Function.Injective (fun k : Fin 17 => freePlaneSymmetry^[k.val] x) := by
  intro i j h
  apply planar_orbit_injective x.val x.property
  simpa only [freePlaneSymmetry_iterate] using congrArg Subtype.val h

abbrev RotationGroup := Multiplicative (ZMod 17)

instance : MulAction RotationGroup FreePlane where
  smul g x := freePlaneSymmetry^[g.toAdd.val] x
  one_smul x := rfl
  mul_smul g h x := by
    change freePlaneSymmetry^[(g.toAdd + h.toAdd).val] x =
      freePlaneSymmetry^[g.toAdd.val] (freePlaneSymmetry^[h.toAdd.val] x)
    rw [ZMod.val_add,
      (show IsPeriodicPt freePlaneSymmetry 17 x from freePlaneSymmetry_period x).iterate_mod_apply,
      Function.iterate_add_apply]

@[simp] theorem rotationGroup_smul (g : RotationGroup) (x : FreePlane) :
    g • x = freePlaneSymmetry^[g.toAdd.val] x := rfl

instance : ContinuousConstSMul RotationGroup FreePlane where
  continuous_const_smul g := freePlaneSymmetry.continuous.iterate g.toAdd.val

instance : IsCancelSMul RotationGroup FreePlane where
  right_cancel' g h x he := by
    have hv := freePlane_orbit_injective x
      (a₁ := ⟨g.toAdd.val, ZMod.val_lt _⟩) (a₂ := ⟨h.toAdd.val, ZMod.val_lt _⟩) he
    change g.toAdd = h.toAdd
    exact ZMod.val_injective 17 (congrArg Fin.val hv)

/-- The topological orbit space of the free action. -/
abbrev RotationOrbitSpace := Quotient (MulAction.orbitRel RotationGroup FreePlane)

def rotationOrbitProjection : FreePlane → RotationOrbitSpace := Quotient.mk _

theorem rotationOrbitProjection_isQuotientCoveringMap :
    IsQuotientCoveringMap rotationOrbitProjection RotationGroup :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem rotationOrbitProjection_isCoveringMap : IsCoveringMap rotationOrbitProjection :=
  rotationOrbitProjection_isQuotientCoveringMap.isCoveringMap

theorem rotationOrbitProjection_fiber_card (q : RotationOrbitSpace) :
    Nat.card (rotationOrbitProjection ⁻¹' {q}) = 17 := by
  obtain ⟨x, rfl⟩ := rotationOrbitProjection_isQuotientCoveringMap.surjective q
  rw [Nat.card_congr (rotationOrbitProjection_isQuotientCoveringMap.fiberEquivGroup ⟨x, rfl⟩)]
  change Nat.card (ZMod 17) = 17
  simp

#print axioms rotationOrbitProjection_isCoveringMap
end Venn17.Topology
