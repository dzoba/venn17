import VennTopology.PlaneRealization
import VennTopology.PuncturedCrossings

/-! Simplicity, topological crossing charts, and the exact-order cyclic
symmetry transported to the constructed Euclidean plane realization. -/

noncomputable section
namespace Venn19.Topology
open Set
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

@[simp] theorem realizedPlaneCurve_mem (x : PuncturedDiagram) (i : Fin 19) :
    diagramPlaneHomeomorph x ∈ realizedPlaneCurve i ↔ x ∈ puncturedCurve i :=
  diagramPlaneHomeomorph.injective.mem_set_image

def realizedPlaneCrossing (f : Fin suppliedModel.oriented.size) : Plane :=
  diagramPlaneHomeomorph (puncturedCrossingPoint f)

theorem planar_no_triple_intersections (i j k : Fin 19)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : Plane) :
    x ∈ realizedPlaneCurve i → x ∈ realizedPlaneCurve j → x ∉ realizedPlaneCurve k := by
  obtain ⟨y, rfl⟩ := diagramPlaneHomeomorph.surjective x
  simpa only [realizedPlaneCurve_mem] using punctured_no_triple_intersections i j k hij hik hjk y

theorem planar_crossing_iff (x : Plane) :
    (∃ i j : Fin 19, i ≠ j ∧ x ∈ realizedPlaneCurve i ∧ x ∈ realizedPlaneCurve j) ↔
      ∃ f : Fin suppliedModel.oriented.size, x = realizedPlaneCrossing f := by
  obtain ⟨y, rfl⟩ := diagramPlaneHomeomorph.surjective x
  simpa only [realizedPlaneCurve_mem, realizedPlaneCrossing, diagramPlaneHomeomorph.injective.eq_iff]
    using punctured_crossing_iff y

theorem CrossingSquare.HasCrossingChart.image {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {C D : Set X} {p : X} (hc : HasCrossingChart C D p) (e : X ≃ₜ Y) :
    HasCrossingChart (e '' C) (e '' D) (e p) := by
  obtain ⟨U, hU, hp, h, hzero, hC, hD⟩ := hc
  let V := e.symm ⁻¹' U
  let g : V ≃ₜ U := e.symm.subtype (fun _ => Iff.rfl)
  refine ⟨V, hU.preimage e.symm.continuous, ?_, g.trans h, ?_, ?_, ?_⟩
  · change e.symm (e p) ∈ U
    simpa only [e.symm_apply_apply] using hp
  · intro y hy
    apply hzero (g y)
    change e.symm y.val = p
    rw [hy, e.symm_apply_apply]
  · intro y
    have hc := hC (g y)
    change e.symm y.val ∈ C ↔ _ at hc
    change y.val ∈ e '' C ↔ (h (g y)).val.1 = 0
    rw [← hc]
    conv_lhs => rw [← e.apply_symm_apply y.val]
    exact e.injective.mem_set_image
  · intro y
    have hd := hD (g y)
    change e.symm y.val ∈ D ↔ _ at hd
    change y.val ∈ e '' D ↔ (h (g y)).val.2 = 0
    rw [← hd]
    conv_lhs => rw [← e.apply_symm_apply y.val]
    exact e.injective.mem_set_image

theorem planar_transverse_crossing (f : Fin suppliedModel.oriented.size) :
    ∃ i j : Fin 19, i ≠ j ∧ CrossingSquare.HasCrossingChart
      (realizedPlaneCurve i) (realizedPlaneCurve j) (realizedPlaneCrossing f) := by
  obtain ⟨i, j, hij, h⟩ := punctured_transverse_crossing f
  exact ⟨i, j, hij, h.image diagramPlaneHomeomorph⟩

/-- This is a plane homeomorphism; its identification with a rigid rotation
requires a further conjugacy theorem. -/
def realizedPlaneSymmetry : Plane ≃ₜ Plane :=
  diagramPlaneHomeomorph.symm.trans (puncturedRotation.trans diagramPlaneHomeomorph)

@[simp] theorem planar_symmetry_apply (x : PuncturedDiagram) :
    realizedPlaneSymmetry (diagramPlaneHomeomorph x) = diagramPlaneHomeomorph (puncturedRotation x) := by
  simp [realizedPlaneSymmetry]

theorem planar_symmetry_iterate (n : ℕ) (x : PuncturedDiagram) :
    realizedPlaneSymmetry^[n] (diagramPlaneHomeomorph x) =
      diagramPlaneHomeomorph (puncturedRotation^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      planar_symmetry_apply]

theorem planar_symmetry_period (x : Plane) : realizedPlaneSymmetry^[19] x = x := by
  obtain ⟨y, rfl⟩ := diagramPlaneHomeomorph.surjective x
  rw [planar_symmetry_iterate, punctured_rotation_period]

theorem planar_symmetry_no_short_period (k : ℕ) (hk : 0 < k) (hk17 : k < 19) :
    ∃ x : Plane, realizedPlaneSymmetry^[k] x ≠ x := by
  obtain ⟨x, hx⟩ := punctured_rotation_no_short_period k hk hk17
  refine ⟨diagramPlaneHomeomorph x, ?_⟩
  rw [planar_symmetry_iterate, ne_eq, diagramPlaneHomeomorph.injective.eq_iff]
  exact hx

theorem planar_symmetry_curve_image (i : Fin 19) :
    realizedPlaneSymmetry '' realizedPlaneCurve i = realizedPlaneCurve (curveRotation i) := by
  change realizedPlaneSymmetry '' (diagramPlaneHomeomorph '' puncturedCurve i) = _
  rw [← image_comp]
  have he : realizedPlaneSymmetry ∘ diagramPlaneHomeomorph = diagramPlaneHomeomorph ∘ puncturedRotation :=
    funext planar_symmetry_apply
  rw [he, image_comp, punctured_rotation_curve_image]
  rfl

theorem planar_symmetry_region_image (v : Fin 524288) :
    realizedPlaneSymmetry '' realizedPlaneRegion v = realizedPlaneRegion (patternRotation v) := by
  change realizedPlaneSymmetry '' (diagramPlaneHomeomorph '' puncturedRegion v) = _
  rw [← image_comp]
  have he : realizedPlaneSymmetry ∘ diagramPlaneHomeomorph = diagramPlaneHomeomorph ∘ puncturedRotation :=
    funext planar_symmetry_apply
  rw [he, image_comp, punctured_rotation_region_image]
  rfl

theorem planar_symmetry_fixed_iff (x : Plane) :
    realizedPlaneSymmetry x = x ↔ (diagramPlaneHomeomorph.symm x).val = patternPoint 524287 := by
  obtain ⟨y, rfl⟩ := diagramPlaneHomeomorph.surjective x
  rw [planar_symmetry_apply, diagramPlaneHomeomorph.injective.eq_iff,
    diagramPlaneHomeomorph.symm_apply_apply, punctured_rotation_fixed_iff]

theorem planar_symmetry_unique_fixed_point : ∃! x : Plane, realizedPlaneSymmetry x = x := by
  let p : PuncturedDiagram := ⟨patternPoint 524287, fun h =>
    (by decide : (524287 : Fin 524288) ≠ 0) (patternPoint_injective h)⟩
  refine ⟨diagramPlaneHomeomorph p, ?_, ?_⟩
  · change realizedPlaneSymmetry (diagramPlaneHomeomorph p) = diagramPlaneHomeomorph p
    rw [planar_symmetry_fixed_iff, diagramPlaneHomeomorph.symm_apply_apply]
  · intro x hx
    apply diagramPlaneHomeomorph.symm.injective
    apply Subtype.ext
    rw [diagramPlaneHomeomorph.symm_apply_apply]
    exact (planar_symmetry_fixed_iff x).mp hx

#print axioms planar_transverse_crossing
#print axioms planar_symmetry_period
end Venn19.Topology
