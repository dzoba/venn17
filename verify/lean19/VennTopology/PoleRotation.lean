import VennTopology.PolygonRotation
import VennTopology.PoleRotationData
import VennTopology.GeometricLinks
import VennTopology.RegionSymmetry

/-! The certified pole links carry the genuine local circle rotations of
angles +2π/19 and -2π/19. This identifies the local generator; extending it
to a global sphere or plane conjugacy remains a separate topological step. -/

noncomputable section
namespace Venn19.Topology
open Set
attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars

/-- The existing geometric coordinate action, expressed in encoded labels. -/
def encodedRotation : Equiv.Perm Nat :=
  (Coordinates.labelEquiv 524288 suppliedModel.oriented.size).symm.trans
    (diagramAutomorphism.labels.trans (Coordinates.labelEquiv 524288 suppliedModel.oriented.size))

theorem encodedRotation_step (x : Nat) (hx : x < 524288 + suppliedModel.oriented.size) :
    encodedRotation x = encodedRotationStep suppliedModel.oriented x := by
  by_cases h : x < 524288
  · have he : (Coordinates.labelEquiv 524288 suppliedModel.oriented.size).symm x = .inl x := by
      apply (Coordinates.labelEquiv 524288 suppliedModel.oriented.size).injective
      simp only [Equiv.apply_symm_apply, Coordinates.labelEquiv_region _ _ _ h]
    change Coordinates.labelEquiv 524288 suppliedModel.oriented.size
      (diagramAutomorphism.labels ((Coordinates.labelEquiv 524288 suppliedModel.oriented.size).symm x)) = _
    rw [he]
    change Coordinates.labelEquiv 524288 suppliedModel.oriented.size (.inl (regionStep x)) = _
    rw [Coordinates.labelEquiv_region _ _ _ (regionStep_lt h)]
    simp only [encodedRotationStep, encodedRotationStepWith, if_pos h]
  · let f : Fin suppliedModel.oriented.size := ⟨x - 524288, by omega⟩
    have he : (Coordinates.labelEquiv 524288 suppliedModel.oriented.size).symm x = .inr f := by
      apply (Coordinates.labelEquiv 524288 suppliedModel.oriented.size).injective
      simp only [Equiv.apply_symm_apply, Coordinates.labelEquiv_face]
      dsimp [f]
      omega
    change Coordinates.labelEquiv 524288 suppliedModel.oriented.size
      (diagramAutomorphism.labels ((Coordinates.labelEquiv 524288 suppliedModel.oriented.size).symm x)) = _
    rw [he]
    change 524288 + (rotationWitnesses suppliedModel.oriented)[f.val]! = _
    simp only [encodedRotationStep, encodedRotationStepWith, if_neg h, f, Array.getElem!_eq_getD]
    rfl

private theorem cyclicNext_iterate_val {n : ℕ} (s : ℕ) (j : Fin n) :
    (Coordinates.cyclicNext^[s] j).val = (j.val + s) % n := by
  induction s with
  | zero => exact (Nat.mod_eq_of_lt j.isLt).symm
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    change ((Coordinates.cyclicNext^[s] j).val + 1) % n = _
    rw [ih, Nat.mod_add_mod]
    congr 1

theorem poleLinkActionCheck_sound (fs : Array Face) (stars : LinkProof.Stars) (pole step : ℕ)
    (h : poleLinkActionCheck fs stars pole step = true) :
    (stars.getD pole #[]).size = 38 ∧ ∀ j : Fin (stars.getD pole #[]).size,
      rowVertices fs 524288 (stars.getD pole #[]) j < 524288 + fs.size ∧
      encodedRotationStep fs (rowVertices fs 524288 (stars.getD pole #[]) j) =
        rowVertices fs 524288 (stars.getD pole #[]) (Coordinates.cyclicNext^[step] j) := by
  simp only [poleLinkActionCheck, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  intro j
  have hj := Array.all_eq_true.mp h.2 j.val (by simpa using j.isLt)
  simpa only [Array.getElem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    rowVertices, cyclicNext_iterate_val, encodedRotationStep] using hj

def poleIndex (p : Fin 2) : Fin suppliedLinkStars.size :=
  ⟨if p = 0 then 0 else 524287, by rw [supplied_link_rows.1]; split_ifs <;> omega⟩

def poleLinkStep (p : Fin 2) : ℕ := if p = 0 then 2 else 36

theorem pole_link_action (p : Fin 2) :
    let row := suppliedLinkStars.getD (poleIndex p).val #[]
    row.size = 38 ∧ ∀ j : Fin row.size,
      encodedRotation (rowVertices suppliedModel.oriented 524288 row j) =
        rowVertices suppliedModel.oriented 524288 row (Coordinates.cyclicNext^[poleLinkStep p] j) := by
  have h : poleLinkActionCheck suppliedModel.oriented suppliedLinkStars
      (poleIndex p).val (poleLinkStep p) = true := by
    fin_cases p
    · exact supplied_pole_link_action_verified.1
    · exact supplied_pole_link_action_verified.2
  obtain ⟨hn, hj⟩ := poleLinkActionCheck_sound _ _ _ _ h
  refine ⟨hn, fun j => ?_⟩
  rw [encodedRotation_step _ (hj j).1]
  exact (hj j).2

/-- The existing geometric circle parametrization is equivariant, not merely
a circle homeomorphism chosen independently of the action. -/
theorem pole_link_circle_rotation (p : Fin 2) (z : Circle) :
    Coordinates.reindex encodedRotation (supplied_dart_link_circle (poleIndex p) z).val =
      (supplied_dart_link_circle (poleIndex p)
        (Circle.exp (2 * Real.pi / 38 * poleLinkStep p) * z)).val := by
  have h := pole_link_action p
  have hr := supplied_link_rows.2 (poleIndex p)
  have hg := Coordinates.labeledPolygonHomeomorph_rotation encodedRotation
    (rowVertices suppliedModel.oriented 524288 (suppliedLinkStars.getD (poleIndex p).val #[]))
    (LinkProof.rowCheck_sound _ _ _ _ hr).2.1 (LinkProof.rowCheck_sound _ _ _ _ hr).1
    (poleLinkStep p) h.2 z
  have he : (↑(suppliedLinkStars.getD (poleIndex p).val #[]).size : ℝ) = 38 := by
    exact_mod_cast h.1
  rw [he] at hg
  exact hg

theorem zero_pole_link_rotation (z : Circle) :
    Coordinates.reindex encodedRotation (supplied_dart_link_circle (poleIndex 0) z).val =
      (supplied_dart_link_circle (poleIndex 0) (Circle.exp (2 * Real.pi / 19) * z)).val := by
  have h := pole_link_circle_rotation 0 z
  change _ = (supplied_dart_link_circle (poleIndex 0) (Circle.exp (2 * Real.pi / 38 * 2) * z)).val at h
  rw [show 2 * Real.pi / 38 * 2 = 2 * Real.pi / 19 by ring] at h
  exact h

theorem one_pole_link_rotation (z : Circle) :
    Coordinates.reindex encodedRotation (supplied_dart_link_circle (poleIndex 1) z).val =
      (supplied_dart_link_circle (poleIndex 1) (Circle.exp (-(2 * Real.pi / 19)) * z)).val := by
  have h := pole_link_circle_rotation 1 z
  change _ = (supplied_dart_link_circle (poleIndex 1) (Circle.exp (2 * Real.pi / 38 * 36) * z)).val at h
  rw [show 2 * Real.pi / 38 * 36 = -(2 * Real.pi / 19) + 2 * Real.pi by ring,
    Circle.exp_add_two_pi] at h
  exact h

#print axioms pole_link_circle_rotation
end Venn19.Topology
