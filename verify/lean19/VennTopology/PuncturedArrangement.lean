import VennTopology.CurveSymmetry
import VennTopology.PuncturedRegions

noncomputable section
namespace Venn19.Topology
open Set
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

/-- The surface with the intended point at infinity removed. Identification
with the Euclidean plane is a separate, still outstanding theorem. -/
abbrev PuncturedDiagram := {x : Diagram // x ≠ patternPoint 0}

def puncturedCurve (i : Fin 19) : Set PuncturedDiagram := Subtype.val ⁻¹' diagramCurve i
def puncturedRegion (v : Fin 524288) : Set PuncturedDiagram := Subtype.val ⁻¹' diagramRegion v

theorem pole_avoids_curves (i : Fin 19) : patternPoint 0 ∉ diagramCurve i := by
  have h := region_subset_complement 0 (patternPoint_mem_region 0)
  exact fun hi => h (mem_iUnion.mpr ⟨i,hi⟩)

def puncturedCurveHomeomorph (i : Fin 19) : diagramCurve i ≃ₜ puncturedCurve i where
  toFun x := ⟨⟨x.val,fun he => pole_avoids_curves i (he ▸ x.property)⟩,x.property⟩
  invFun x := ⟨x.val.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def puncturedCurveCircle (i : Fin 19) : Circle ≃ₜ puncturedCurve i :=
  (diagramCurveHomeomorph i).trans (puncturedCurveHomeomorph i)

theorem punctured_curves_are_embedded_circles (i : Fin 19) :
    ∃ f : Circle → PuncturedDiagram, Continuous f ∧ Function.Injective f ∧ Set.range f = puncturedCurve i := by
  refine ⟨fun z => (puncturedCurveCircle i z).val,
    continuous_subtype_val.comp (puncturedCurveCircle i).continuous,
    Subtype.val_injective.comp (puncturedCurveCircle i).injective,?_⟩
  ext x
  constructor
  · rintro ⟨z,rfl⟩; exact (puncturedCurveCircle i z).property
  · intro hx
    obtain ⟨z,hz⟩ := (puncturedCurveCircle i).surjective ⟨x,hx⟩
    exact ⟨z,congrArg Subtype.val hz⟩

theorem puncturedRegion_pathConnected (v : Fin 524288) : IsPathConnected (puncturedRegion v) := by
  have h : IsPathConnected (diagramRegion v \ {patternPoint 0}) := by
    by_cases hv : v = 0
    · subst v; exact diagramRegion_punctured_pathConnected 0
    · have hp : patternPoint 0 ∉ diagramRegion v := by
        intro hp
        exact Set.disjoint_left.mp (diagramRegion_disjoint hv) hp (patternPoint_mem_region 0)
      have he : diagramRegion v \ {patternPoint 0} = diagramRegion v := by
        ext x; simp only [mem_sdiff,mem_singleton_iff]
        exact ⟨And.left,fun hx => ⟨hx,fun he => hp (he ▸ hx)⟩⟩
      rw [he]
      exact diagramRegion_pathConnected v
  have hpre : IsPathConnected ((Subtype.val : PuncturedDiagram → Diagram) ⁻¹'
      (diagramRegion v \ {patternPoint 0})) := h.preimage_coe (fun _ hx => hx.2)
  have he : (Subtype.val : PuncturedDiagram → Diagram) ⁻¹'
      (diagramRegion v \ {patternPoint 0}) = puncturedRegion v := by
    ext x
    exact and_iff_left x.property
  rwa [he] at hpre

def puncturedComplement : Set PuncturedDiagram := (⋃ i : Fin 19, puncturedCurve i)ᶜ
def puncturedComplementRegion (v : Fin 524288) : Set puncturedComplement :=
  Subtype.val ⁻¹' puncturedRegion v

def complementForget (x : puncturedComplement) : diagramComplement := ⟨x.val.val,by
  simpa only [diagramComplement,puncturedComplement,puncturedCurve,mem_compl_iff,mem_iUnion,
    mem_preimage] using x.property⟩

theorem punctured_complement_unique_region (x : PuncturedDiagram) :
    x ∈ puncturedComplement ↔ ∃! v : Fin 524288, x ∈ puncturedRegion v := by
  simpa only [puncturedComplement,puncturedCurve,puncturedRegion,mem_compl_iff,mem_iUnion,
    mem_preimage] using diagram_complement_unique_region x.val

theorem puncturedComplementRegion_isClopen (v : Fin 524288) :
    IsClopen (puncturedComplementRegion v) :=
  (complementRegion_isClopen v).preimage (show Continuous complementForget by unfold complementForget; fun_prop)

theorem puncturedComplementRegion_pathConnected (v : Fin 524288) :
    IsPathConnected (puncturedComplementRegion v) :=
  (puncturedRegion_pathConnected v).preimage_coe (by
    intro x hx
    have h := region_subset_complement v hx
    simpa only [diagramComplement,puncturedComplement,puncturedCurve,mem_compl_iff,mem_iUnion,
      mem_preimage] using h)

def puncturedComponentsEquiv : ConnectedComponents puncturedComplement ≃ Fin 524288 :=
  ConnectedComponents.equivOfIsClopenOfIsConnected puncturedComplementRegion_isClopen
    (fun u v huv => ((diagramRegion_disjoint huv).preimage Subtype.val).preimage Subtype.val)
    (by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨v,hv,_⟩ := (punctured_complement_unique_region x.val).mp x.property
      exact mem_iUnion.mpr ⟨v,hv⟩)
    (fun v => (puncturedComplementRegion_pathConnected v).isConnected)

theorem punctured_complement_component_count : Nat.card (ConnectedComponents puncturedComplement) = 524288 := by
  rw [Nat.card_congr puncturedComponentsEquiv]
  simp

def puncturedRotation : PuncturedDiagram ≃ₜ PuncturedDiagram :=
  diagramRotation.subtype (fun x => by
    change x ≠ patternPoint 0 ↔ diagramRotation x ≠ patternPoint 0
    have h : diagramRotation x = patternPoint 0 ↔ x = patternPoint 0 := by
      conv_lhs => rw [← diagram_rotation_fixes_zero]
      exact diagramRotation.injective.eq_iff
    exact (not_congr h).symm)

theorem punctured_rotation_iterate (n : Nat) (x : PuncturedDiagram) :
    (puncturedRotation^[n] x).val = diagramRotation^[n] x.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change diagramRotation ((puncturedRotation^[n] x).val) = _
    rw [ih]

theorem punctured_rotation_period (x : PuncturedDiagram) : puncturedRotation^[19] x = x := by
  apply Subtype.ext
  rw [punctured_rotation_iterate,diagram_rotation_period]

theorem punctured_rotation_curve_image (i : Fin 19) :
    puncturedRotation '' puncturedCurve i = puncturedCurve (curveRotation i) := by
  ext x
  obtain ⟨y,rfl⟩ := puncturedRotation.surjective x
  rw [puncturedRotation.injective.mem_set_image]
  exact (diagram_rotation_mem_curve y.val i).symm

theorem punctured_rotation_region_image (v : Fin 524288) :
    puncturedRotation '' puncturedRegion v = puncturedRegion (patternRotation v) := by
  ext x
  obtain ⟨y,rfl⟩ := puncturedRotation.surjective x
  rw [puncturedRotation.injective.mem_set_image]
  exact (diagram_rotation_mem_region y.val v).symm

theorem punctured_rotation_fixed_iff (x : PuncturedDiagram) :
    puncturedRotation x = x ↔ x.val = patternPoint 524287 := by
  have h : puncturedRotation x = x ↔ diagramRotation x.val = x.val := Subtype.val_injective.eq_iff.symm
  rw [h]
  rw [diagram_rotation_fixed_iff,or_iff_right x.property]

theorem punctured_rotation_no_short_period (k : Nat) (hk : 0 < k) (hk17 : k < 19) :
    ∃ x : PuncturedDiagram, puncturedRotation^[k] x ≠ x := by
  let x : PuncturedDiagram := ⟨patternPoint 1,fun he =>
    (by decide : (1 : Fin 524288) ≠ 0) (patternPoint_injective he)⟩
  refine ⟨x,fun he => ?_⟩
  have hv := congrArg Subtype.val he
  rw [punctured_rotation_iterate] at hv
  exact diagram_rotation_no_short_period k hk hk17 hv

def puncturedCrossingPoint (f : Fin suppliedModel.oriented.size) : PuncturedDiagram :=
  ⟨crossingPoint f,by
    intro he
    have hp := Quad.point_injective (congrArg Subtype.val he)
    cases hp⟩

theorem punctured_crossing_iff (x : PuncturedDiagram) :
    (∃ i j : Fin 19, i ≠ j ∧ x ∈ puncturedCurve i ∧ x ∈ puncturedCurve j) ↔
      ∃ f : Fin suppliedModel.oriented.size, x = puncturedCrossingPoint f := by
  change (∃ i j : Fin 19, i ≠ j ∧ x.val ∈ diagramCurve i ∧ x.val ∈ diagramCurve j) ↔ _
  rw [diagram_crossing_iff]
  apply exists_congr
  intro f
  exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩

theorem punctured_no_triple_intersections (i j k : Fin 19)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : PuncturedDiagram) :
    x ∈ puncturedCurve i → x ∈ puncturedCurve j → x ∉ puncturedCurve k :=
  diagram_no_triple_intersections i j k hij hik hjk x.val

#print axioms punctured_complement_component_count
#print axioms punctured_rotation_curve_image
end Venn19.Topology
