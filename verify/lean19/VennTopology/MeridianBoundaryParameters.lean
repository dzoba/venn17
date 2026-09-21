import VennTopology.MeridianIntersections
import VennTopology.RigidSectorCover

/-! The forward and reversed halves of each polygonal boundary retain the
same pole-to-pole parameter. These identities include the shared endpoints. -/
noncomputable section
namespace Venn19.Topology
open Set Coordinates
attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars

theorem diagramMeridianBoundaryMap_front (k l : Fin 19) (t : MeridianParameter) :
    diagramMeridianBoundaryMap k l (meridianCircleParameter t) = diagramMeridianMap k t := by
  obtain ⟨i, r, ht⟩ := meridianParameter_edge t
  have he : t = meridianEdgeParameter i r := Subtype.ext ht
  rw [he]
  apply diagramEncodedHomeomorph.injective
  apply Subtype.ext
  rw [diagramMeridianMap_edge]
  change (diagramEncodedHomeomorph (diagramEncodedHomeomorph.symm _)).val = _
  simp only [Homeomorph.apply_symm_apply]
  have hp : meridianCircleParameter (meridianEdgeParameter i r) =
      AddCircle.toCircle (edgePhase ((⟨i.val, by omega⟩ : Fin 38), r)) := rfl
  rw [hp, labeledPolygonMap_phase, relabel_edgePoint]
  have hn : cyclicNext (⟨i.val, by omega⟩ : Fin 38) = ⟨i.val+1, by omega⟩ := by
    apply Fin.ext
    change (i.val+1)%38 = i.val+1
    exact Nat.mod_eq_of_lt (by omega)
  rw [hn, meridian_boundary_front k l (⟨i.val, by omega⟩ : Fin 20),
    meridian_boundary_front k l (⟨i.val+1, by omega⟩ : Fin 20)]

theorem meridian_reverse_phase (i : Fin 19) (r : Icc (0 : ℝ) 1) :
    AddCircle.toCircle (edgePhase ((⟨37-i.val, by omega⟩ : Fin 38),
      ⟨1-r.val, by constructor <;> linarith [r.property.1, r.property.2]⟩)) =
      (meridianCircleParameter (meridianEdgeParameter i r))⁻¹ := by
  have hp : edgePhase ((⟨37-i.val, by omega⟩ : Fin 38),
      ⟨1-r.val, by constructor <;> linarith [r.property.1, r.property.2]⟩) =
      -(((i.val : ℝ)+r.val : ℝ) : AddCircle (38 : ℝ)) := by
    unfold edgePhase
    have hv : ((37-i.val : ℕ) : ℝ)+(1-r.val) = 38-((i.val : ℝ)+r.val) := by
      rw [Nat.cast_sub (by omega)]
      norm_num
      ring
    rw [hv, AddCircle.coe_sub, AddCircle.coe_period, zero_sub]
    rfl
  rw [hp, AddCircle.toCircle_neg]
  rfl

theorem diagramMeridianBoundaryMap_back (k l : Fin 19) (t : MeridianParameter) :
    diagramMeridianBoundaryMap k l (meridianCircleParameter t)⁻¹ = diagramMeridianMap l t := by
  obtain ⟨i, r, ht⟩ := meridianParameter_edge t
  have he : t = meridianEdgeParameter i r := Subtype.ext ht
  rw [he]
  apply diagramEncodedHomeomorph.injective
  apply Subtype.ext
  rw [diagramMeridianMap_edge]
  change (diagramEncodedHomeomorph (diagramEncodedHomeomorph.symm _)).val = _
  simp only [Homeomorph.apply_symm_apply]
  rw [← meridian_reverse_phase, labeledPolygonMap_phase, relabel_edgePoint]
  have h1 : (⟨37-i.val, by omega⟩ : Fin 38) =
      ⟨(38-(i.val+1))%38, Nat.mod_lt _ (by decide)⟩ := by
    apply Fin.ext; dsimp; omega
  have h2 : cyclicNext (⟨37-i.val, by omega⟩ : Fin 38) =
      ⟨(38-i.val)%38, Nat.mod_lt _ (by decide)⟩ := by
    apply Fin.ext; change (37-i.val+1)%38 = (38-i.val)%38
    congr 1; omega
  rw [h2, h1, meridian_boundary_back k l (⟨i.val+1, by omega⟩ : Fin 20),
    meridian_boundary_back k l (⟨i.val, by omega⟩ : Fin 20)]
  simp only [sub_sub_cancel]
  exact add_comm _ _

theorem meridianCircleParameter_exp (t : MeridianParameter) :
    meridianCircleParameter t = Circle.exp (Real.pi / 19 * t.val) := by
  rw [meridianCircleParameter, AddCircle.toCircle_apply_mk]
  congr 1
  ring

theorem meridianCircleParameter_im_nonneg (t : MeridianParameter) :
    0 ≤ (meridianCircleParameter t : ℂ).im := by
  rw [meridianCircleParameter_exp]
  simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · exact mul_nonneg (by positivity) t.property.1
  · have h := t.property.2
    nlinarith [Real.pi_pos]

/-- Every circle parameter is in the forward or reversed meridian half. -/
theorem meridianCircleParameter_halves (z : Circle) :
    ∃ t : MeridianParameter, z = meridianCircleParameter t ∨ z = (meridianCircleParameter t)⁻¹ := by
  obtain ⟨θ, hθ, rfl⟩ := circle_positive_angle z
  by_cases h : θ ≤ Real.pi
  · let t : MeridianParameter := ⟨19 * θ / Real.pi, by
      constructor
      · exact div_nonneg (mul_nonneg (by norm_num) hθ.1) Real.pi_pos.le
      · rw [div_le_iff₀ Real.pi_pos]; linarith⟩
    refine ⟨t, Or.inl ?_⟩
    rw [meridianCircleParameter_exp]
    congr 1
    dsimp [t]
    field_simp
  · let t : MeridianParameter := ⟨19 * (2*Real.pi-θ) / Real.pi, by
      constructor
      · apply div_nonneg _ Real.pi_pos.le; nlinarith [hθ.2]
      · rw [div_le_iff₀ Real.pi_pos]; linarith⟩
    refine ⟨t, Or.inr ?_⟩
    rw [meridianCircleParameter_exp, ← Circle.exp_neg]
    have hv : -(Real.pi / 19 * t.val) = θ-2*Real.pi := by
      dsimp [t]
      field_simp
      ring
    rw [hv, Circle.exp_sub_two_pi]

end Venn19.Topology
