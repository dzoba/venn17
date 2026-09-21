import VennTopology.PuncturedSides
import VennTopology.Planar
import Mathlib.Data.Fintype.EquivFin

noncomputable section
namespace Venn19.Topology
open Set
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

def planeCurve (e : PuncturedDiagram ≃ₜ Plane) (i : Fin 19) : Set Plane := e '' puncturedCurve i
def planeSide (e : PuncturedDiagram ≃ₜ Plane) (i : Fin 19) (b : Bool) : Set Plane := e '' puncturedSide i b
def planeRegion (e : PuncturedDiagram ≃ₜ Plane) (v : Fin 524288) : Set Plane := e '' puncturedRegion v

theorem diagramBitField_zero_pattern (i : Fin 19) : diagramBitField i (patternPoint 0) = -1 := by
  rw [diagramBitField_pattern]
  simp [bitSign]

/-- The closed nonnegative side stays compact after removing the all-zero
pole, since its bit field has value -1 at that pole. -/
theorem punctured_nonnegative_compact (i : Fin 19) :
    IsCompact {x : PuncturedDiagram | 0 ≤ diagramBitField i x.val} := by
  have hK : IsCompact {x : Diagram | 0 ≤ diagramBitField i x} :=
    (isClosed_le continuous_const (diagramBitField_continuous i)).isCompact
  apply Topology.IsInducing.subtypeVal.isCompact_preimage' hK
  intro x hx
  refine ⟨⟨x,?_⟩,rfl⟩
  intro he
  change 0 ≤ diagramBitField i x at hx
  rw [he,diagramBitField_zero_pattern] at hx
  norm_num at hx

theorem planeSide_true_bounded (e : PuncturedDiagram ≃ₜ Plane) (i : Fin 19) :
    Bornology.IsBounded (planeSide e i true) := by
  apply ((punctured_nonnegative_compact i).image e.continuous).isBounded.subset
  apply image_mono
  intro x hx
  change 0 < sideSign true * diagramBitField i x.val at hx
  simpa [sideSign] using hx.le

theorem puncturedCurve_compact (i : Fin 19) : IsCompact (puncturedCurve i) := by
  apply Topology.IsInducing.subtypeVal.isCompact_preimage' (diagramCurve_compact i)
  intro x hx
  exact ⟨⟨x,fun he => pole_avoids_curves i (he ▸ hx)⟩,rfl⟩

theorem planeCurve_compact (e : PuncturedDiagram ≃ₜ Plane) (i : Fin 19) :
    IsCompact (planeCurve e i) := (puncturedCurve_compact i).image e.continuous

theorem planeSide_isOpen (e : PuncturedDiagram ≃ₜ Plane) (i : Fin 19) (b : Bool) :
    IsOpen (planeSide e i b) := e.isOpenMap _ (puncturedSide_isOpen i b)

theorem planeSide_pathConnected (e : PuncturedDiagram ≃ₜ Plane) (i : Fin 19) (b : Bool) :
    IsPathConnected (planeSide e i b) := (puncturedSide_pathConnected i b).image e.continuous

theorem planeSide_disjoint (e : PuncturedDiagram ≃ₜ Plane) (i : Fin 19) :
    Disjoint (planeSide e i false) (planeSide e i true) :=
  Set.disjoint_image_of_injective e.injective (puncturedSide_disjoint i)

theorem planeSide_cover (e : PuncturedDiagram ≃ₜ Plane) (i : Fin 19) :
    (⋃ b, planeSide e i b) = (planeCurve e i)ᶜ := by
  unfold planeSide planeCurve
  rw [← image_iUnion,puncturedSide_cover,image_compl_eq e.bijective]

theorem planeSide_false_unbounded (e : PuncturedDiagram ≃ₜ Plane) (i : Fin 19) :
    ¬ Bornology.IsBounded (planeSide e i false) := by
  intro hb
  have hu : planeCurve e i ∪ (planeSide e i false ∪ planeSide e i true) = univ := by
    have hc := planeSide_cover e i
    have he : (⋃ b, planeSide e i b) = planeSide e i false ∪ planeSide e i true := by
      ext x; simp only [mem_iUnion,mem_union]; exact Bool.exists_bool
    rw [he] at hc
    rw [hc,union_compl_self]
  have hbound := (planeCurve_compact e i).isBounded.union (hb.union (planeSide_true_bounded e i))
  rw [hu] at hbound
  exact NormedSpace.unbounded_univ ℝ Plane hbound

theorem planeRegion_eq_sides (e : PuncturedDiagram ≃ₜ Plane) (v : Fin 524288) :
    planeRegion e v = ⋂ i : Fin 19, planeSide e i (v.val.testBit i.val) := by
  unfold planeRegion planeSide
  rw [puncturedRegion_eq_sides,image_iInter e.bijective]

theorem planeRegion_pathConnected (e : PuncturedDiagram ≃ₜ Plane) (v : Fin 524288) :
    IsPathConnected (planeRegion e v) := (puncturedRegion_pathConnected v).image e.continuous

theorem plane_curves_are_embedded_circles (e : PuncturedDiagram ≃ₜ Plane) (i : Fin 19) :
    ∃ f : Circle → Plane, Continuous f ∧ Function.Injective f ∧ range f = planeCurve e i := by
  obtain ⟨f,hc,hi,hr⟩ := punctured_curves_are_embedded_circles i
  refine ⟨e ∘ f,e.continuous.comp hc,e.injective.comp hi,?_⟩
  rw [Set.range_comp,hr]
  rfl

theorem plane_curve_complement_component_count (e : PuncturedDiagram ≃ₜ Plane) (i : Fin 19) :
    Nat.card (ConnectedComponents ((planeCurve e i)ᶜ : Set Plane)) = 2 := by
  obtain ⟨f,hc,hi,hr⟩ := plane_curves_are_embedded_circles e i
  exact (congrArg (fun s : Set Plane => Nat.card (ConnectedComponents (sᶜ : Set Plane))) hr).symm.trans
    (planar_jordan_separation_circle f hc hi)

theorem plane_complement_unique_region (e : PuncturedDiagram ≃ₜ Plane) (x : Plane) :
    x ∉ ⋃ i : Fin 19, planeCurve e i ↔ ∃! v : Fin 524288, x ∈ planeRegion e v := by
  obtain ⟨y,rfl⟩ := e.surjective x
  simpa only [planeCurve,planeRegion,mem_iUnion,e.injective.mem_set_image,
    puncturedComplement,mem_compl_iff] using punctured_complement_unique_region y

theorem all_bit_patterns (b : Fin 19 → Bool) :
    ∃ v : Fin 524288, ∀ i : Fin 19, v.val.testBit i.val = b i := by
  have h : Function.Bijective (fun v : Fin 524288 => fun i : Fin 19 => v.val.testBit i.val) := by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨fun _ _ h => pattern_eq_of_bits (congrFun h),?_⟩
    norm_num [Fintype.card_fun]
  obtain ⟨v,hv⟩ := h.surjective b
  exact ⟨v,congrFun hv⟩

/-- Every choice of inside/outside bits gives a nonempty path-connected
planar region, conditional only on the supplied plane homeomorphism. -/
theorem plane_every_membership_pattern (e : PuncturedDiagram ≃ₜ Plane) (b : Fin 19 → Bool) :
    IsPathConnected (⋂ i : Fin 19, planeSide e i (b i)) := by
  obtain ⟨v,hv⟩ := all_bit_patterns b
  have he := planeRegion_eq_sides e v
  simp_rw [hv] at he
  rw [← he]
  exact planeRegion_pathConnected e v

/-- Conditional planar conclusion: the input is a plane homeomorphism, not an
assumed Jordan/inside-outside theorem. PlaneRealization constructs the concrete
instance; rigid rotation conjugacy remains a separate obligation. -/
theorem planar_sides_verified (e : PuncturedDiagram ≃ₜ Plane) :
    (∀ i : Fin 19,
      (∃ f : Circle → Plane, Continuous f ∧ Function.Injective f ∧ range f = planeCurve e i) ∧
      (∀ b, IsOpen (planeSide e i b) ∧ IsPathConnected (planeSide e i b)) ∧
      Disjoint (planeSide e i false) (planeSide e i true) ∧
      (⋃ b, planeSide e i b) = (planeCurve e i)ᶜ ∧
      Bornology.IsBounded (planeSide e i true) ∧
      ¬ Bornology.IsBounded (planeSide e i false)) ∧
    (∀ v : Fin 524288, IsPathConnected (planeRegion e v) ∧
      planeRegion e v = ⋂ i : Fin 19, planeSide e i (v.val.testBit i.val)) ∧
    (∀ x : Plane, x ∉ ⋃ i : Fin 19, planeCurve e i ↔ ∃! v : Fin 524288, x ∈ planeRegion e v) ∧
    (∀ b : Fin 19 → Bool, IsPathConnected (⋂ i : Fin 19, planeSide e i (b i))) :=
  ⟨fun i => ⟨plane_curves_are_embedded_circles e i,
      fun b => ⟨planeSide_isOpen e i b,planeSide_pathConnected e i b⟩,
      planeSide_disjoint e i,planeSide_cover e i,planeSide_true_bounded e i,planeSide_false_unbounded e i⟩,
    fun v => ⟨planeRegion_pathConnected e v,planeRegion_eq_sides e v⟩,
    plane_complement_unique_region e,plane_every_membership_pattern e⟩

#print axioms planeSide_true_bounded
#print axioms planeSide_false_unbounded
#print axioms planar_sides_verified
end Venn19.Topology
