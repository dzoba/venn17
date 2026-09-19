import VennTopology.LabeledPolygon
import VennTopology.CoordinateRelabel
import Mathlib.Analysis.Complex.Isometry

/-! A cyclic shift of a labeled coordinate polygon is conjugate, through the
proved polygon-circle homeomorphism, to the corresponding rigid circle rotation. -/

noncomputable section
namespace Venn17.Topology.Coordinates
open Set
variable {I : Type*} {n : ℕ}

/-- Advancing one edge adds one to the additive-circle parameter, including
the last-to-first edge. -/
theorem edgePhase_next (p : EdgeParameters n) :
    edgePhase (cyclicNext p.1, p.2) = edgePhase p + (1 : ℝ) := by
  have h := edgePhase_normalize (p.1, (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1))
  simp only [normalizeEdge, ↓reduceIte, edgePhase, add_zero] at h
  simp only [edgePhase, AddCircle.coe_add] at h ⊢
  rw [h]
  abel

theorem edgePhase_iterate_next (s : ℕ) (p : EdgeParameters n) :
    edgePhase (cyclicNext^[s] p.1, p.2) = edgePhase p + (s : ℝ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', edgePhase_next (cyclicNext^[s] p.1, p.2), ih]
    push_cast
    rw [AddCircle.coe_add]
    abel

/-- Parameter formula for the previously constructed circle parametrization. -/
theorem labeledPolygonMap_phase (v : Fin n → I) (hn : 3 ≤ n) (p : EdgeParameters n) :
    labeledPolygonMap v hn (AddCircle.toCircle (edgePhase p)) =
      relabel v (edgePoint p) := by
  unfold labeledPolygonMap circlePolygonHomeomorph
  simp only [Homeomorph.trans_apply]
  rw [← AddCircle.homeomorphCircle_apply (by exact_mod_cast (show n ≠ 0 by omega)),
    Homeomorph.symm_apply_apply]
  exact congrArg (relabel v) (polygonMap_phase hn p)

theorem reindex_relabel_edgePoint (e : I ≃ I) (v : Fin n → I) (p : EdgeParameters n) :
    reindex e (relabel v (edgePoint p)) =
      (1 - p.2.val) • vertex (e (v p.1)) + p.2.val • vertex (e (v (cyclicNext p.1))) := by
  rw [relabel_edgePoint]
  have hadd (x y : Point I) : reindex e (x + y) = reindex e x + reindex e y := by
    ext j; simp [reindex_apply]
  have hsmul (r : ℝ) (x : Point I) : reindex e (r • x) = r • reindex e x := by
    ext j; simp [reindex_apply]
  rw [hadd, hsmul, hsmul, reindex_vertex, reindex_vertex]

/-- Concrete equivariance: moving each polygon vertex by `s` cyclic positions
rotates its circle coordinate by exactly `2πs/n`. -/
theorem labeledPolygonMap_rotation (e : I ≃ I) (v : Fin n → I) (hn : 3 ≤ n) (s : ℕ)
    (hv : ∀ j, e (v j) = v (cyclicNext^[s] j)) (z : Circle) :
    reindex e (labeledPolygonMap v hn z) =
      labeledPolygonMap v hn (Circle.exp (2 * Real.pi / n * s) * z) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨t, ht⟩ := (AddCircle.homeomorphCircle hn0).surjective z
  rw [AddCircle.homeomorphCircle_apply] at ht
  obtain ⟨p, rfl⟩ := edgePhase_surjective (show 0 < n by omega) t
  rw [← ht, labeledPolygonMap_phase]
  have hphase : AddCircle.toCircle (edgePhase (cyclicNext^[s] p.1, p.2)) =
      Circle.exp (2 * Real.pi / n * s) * AddCircle.toCircle (edgePhase p) := by
    rw [edgePhase_iterate_next, AddCircle.toCircle_add, AddCircle.toCircle_apply_mk, mul_comm]
  rw [← hphase, labeledPolygonMap_phase, reindex_relabel_edgePoint, relabel_edgePoint, hv, hv]
  congr 2
  exact congrArg (vertex ∘ v) ((Function.iterate_succ_apply cyclicNext s p.1).symm.trans
    (Function.iterate_succ_apply' cyclicNext s p.1))

/-- The circle homeomorphism realizes the same explicit coordinate action. -/
theorem labeledPolygonHomeomorph_rotation (e : I ≃ I) (v : Fin n → I)
    (hi : Function.Injective v) (hn : 3 ≤ n) (s : ℕ)
    (hv : ∀ j, e (v j) = v (cyclicNext^[s] j)) (z : Circle) :
    reindex e (labeledPolygonHomeomorph v hi hn z).val =
      (labeledPolygonHomeomorph v hi hn (Circle.exp (2 * Real.pi / n * s) * z)).val :=
  labeledPolygonMap_rotation e v hn s hv z

#print axioms labeledPolygonHomeomorph_rotation
end Venn17.Topology.Coordinates
