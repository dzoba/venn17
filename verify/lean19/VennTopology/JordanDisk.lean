import Schoenflies.Main
import Schoenflies.JordanRegionRecognition
import VennTopology.Planar

/-! A compact region with a prescribed Jordan boundary is a closed disk.
The homeomorphism retains the given boundary parametrization, which is needed
for gluing the rotation sectors. The Schoenflies input is a proved theorem. -/
noncomputable section
namespace Venn19.Topology
open Set Metric

abbrev PlaneClosedDisk := closedBall (0 : Plane) 1

def compactJordanCircle (r : UnitCircle → Plane) (hc : Continuous r) (hi : Function.Injective r) :
    Schoenflies.JordanCircle := ⟨r, hc, hi⟩

theorem compactJordanRegion_eq (S : Set Plane) (hS : IsCompact S)
    (r : UnitCircle → Plane) (hc : Continuous r) (hi : Function.Injective r)
    (hf : frontier S ⊆ range r) (hx : ∃ x ∈ interior S, x ∉ range r) :
    S = closure (compactJordanCircle r hc hi).inside := by
  let J := compactJordanCircle r hc hi
  have hs := J.subset_closure_inside_of_isCompact_frontier_subset hS hf
  apply J.eq_closure_inside_of_isCompact_frontier_subset hS hs hf
  obtain ⟨x, hx, hn⟩ := hx
  refine ⟨x, hx, ?_⟩
  have hm := hs (interior_subset hx)
  rw [J.closure_inside] at hm
  exact hm.resolve_right hn

def compactJordanRegionHomeomorph (S : Set Plane) (hS : IsCompact S)
    (r : UnitCircle → Plane) (hc : Continuous r) (hi : Function.Injective r)
    (hf : frontier S ⊆ range r) (hx : ∃ x ∈ interior S, x ∉ range r) : S ≃ₜ PlaneClosedDisk :=
  (Homeomorph.setCongr (compactJordanRegion_eq S hS r hc hi hf hx)).trans
    (compactJordanCircle r hc hi).regionalExtensionData.insideHomeomorph

theorem compactJordanRegionHomeomorph_boundary (S : Set Plane) (hS : IsCompact S)
    (r : UnitCircle → Plane) (hc : Continuous r) (hi : Function.Injective r)
    (hf : frontier S ⊆ range r) (hx : ∃ x ∈ interior S, x ∉ range r)
    (hb : range r ⊆ S) (z : UnitCircle) :
    (compactJordanRegionHomeomorph S hS r hc hi hf hx ⟨r z, hb (mem_range_self z)⟩).val = z.val := by
  let J := compactJordanCircle r hc hi
  have h := J.regionalExtensionData.inside_boundary (J.carrierHomeomorph z)
  rw [J.carrierHomeomorph.symm_apply_apply] at h
  exact h

section Punctured
variable {X : Type*} [TopologicalSpace X] [T1Space X]

/-- Lift a compact subset avoiding `p` into the punctured space. -/
def liftAvoidingPoint (p : X) (S : Set X) (hp : p ∉ S) :
    S ≃ₜ {x : {x : X // x ≠ p} // x.val ∈ S} where
  toFun x := ⟨⟨x.val, fun he => hp (he ▸ x.property)⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def puncturedBoundaryMap (p : X) (S : Set X) (hp : p ∉ S)
    (r : UnitCircle → X) (hb : range r ⊆ S) : UnitCircle → {x : X // x ≠ p} :=
  fun z => ⟨r z, fun he => hp (he ▸ hb (mem_range_self z))⟩

/-- Transport compact Jordan-region data through an arbitrary punctured-plane
chart. The chosen point lies outside the entire closed region. -/
theorem puncturedJordan_conditions (p : X) (e : {x : X // x ≠ p} ≃ₜ Plane)
    (S : Set X) (hS : IsCompact S) (hp : p ∉ S)
    (r : UnitCircle → X) (_hc : Continuous r) (_hi : Function.Injective r)
    (hb : range r ⊆ S) (hf : frontier S ⊆ range r)
    (hx : ∃ x ∈ interior S, x ∉ range r) :
    let T : Set {x : X // x ≠ p} := Subtype.val ⁻¹' S
    let R := puncturedBoundaryMap p S hp r hb
    IsCompact (e '' T) ∧ frontier (e '' T) ⊆ range (e ∘ R) ∧
      ∃ y ∈ interior (e '' T), y ∉ range (e ∘ R) := by
  let T : Set {x : X // x ≠ p} := Subtype.val ⁻¹' S
  let R := puncturedBoundaryMap p S hp r hb
  have hT : IsCompact T := Topology.IsInducing.subtypeVal.isCompact_preimage' hS (by
    intro x hx
    exact ⟨⟨x, fun he => hp (he ▸ hx)⟩, rfl⟩)
  have hU : IsOpen {x : X | x ≠ p} := isClosed_singleton.isOpen_compl
  have hrange : range (e ∘ R) = e '' (Subtype.val ⁻¹' range r) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨R z, mem_range_self z, rfl⟩
    · rintro ⟨x, ⟨z, hz⟩, rfl⟩
      exact ⟨z, congrArg e (Subtype.ext hz)⟩
  have hfront : frontier (e '' T) ⊆ range (e ∘ R) := by
    rw [← e.image_frontier, hrange]
    apply image_mono
    dsimp only [T]
    have hpre : (Subtype.val : {x : X // x ≠ p} → X) ⁻¹' frontier S =
        frontier ((Subtype.val : {x : X // x ≠ p} → X) ⁻¹' S) :=
      hU.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage continuous_subtype_val S
    rw [← hpre]
    exact preimage_mono hf
  have hpoint : ∃ y ∈ interior (e '' T), y ∉ range (e ∘ R) := by
    obtain ⟨x, hx, hn⟩ := hx
    let u : {x : X // x ≠ p} := ⟨x, fun he => hp (he ▸ interior_subset hx)⟩
    refine ⟨e u, ?_, ?_⟩
    · rw [← e.image_interior]
      exact mem_image_of_mem e (preimage_interior_subset_interior_preimage continuous_subtype_val hx)
    · rw [hrange]
      intro he
      obtain ⟨v, hv, he⟩ := he
      have heq := e.injective he
      apply hn
      change u.val ∈ range r
      exact heq ▸ hv
  exact ⟨hT.image e.continuous, hfront, hpoint⟩

def puncturedJordanDisk (p : X) (e : {x : X // x ≠ p} ≃ₜ Plane)
    (S : Set X) (hS : IsCompact S) (hp : p ∉ S)
    (r : UnitCircle → X) (hc : Continuous r) (hi : Function.Injective r)
    (hb : range r ⊆ S) (hf : frontier S ⊆ range r)
    (hx : ∃ x ∈ interior S, x ∉ range r) : S ≃ₜ PlaneClosedDisk :=
  let T : Set {x : X // x ≠ p} := Subtype.val ⁻¹' S
  let R := puncturedBoundaryMap p S hp r hb
  let H := puncturedJordan_conditions p e S hS hp r hc hi hb hf hx
  (liftAvoidingPoint p S hp).trans ((e.image T).trans
    (compactJordanRegionHomeomorph (e '' T) H.1 (e ∘ R)
      (e.continuous.comp (hc.subtype_mk _))
      (e.injective.comp (fun _ _ h => hi (congrArg Subtype.val h))) H.2.1 H.2.2))

/-- The punctured-plane construction preserves the prescribed boundary values. -/
theorem puncturedJordanDisk_boundary (p : X) (e : {x : X // x ≠ p} ≃ₜ Plane)
    (S : Set X) (hS : IsCompact S) (hp : p ∉ S)
    (r : UnitCircle → X) (hc : Continuous r) (hi : Function.Injective r)
    (hb : range r ⊆ S) (hf : frontier S ⊆ range r)
    (hx : ∃ x ∈ interior S, x ∉ range r) (z : UnitCircle) :
    (puncturedJordanDisk p e S hS hp r hc hi hb hf hx ⟨r z, hb (mem_range_self z)⟩).val = z.val := by
  let T : Set {x : X // x ≠ p} := Subtype.val ⁻¹' S
  let R := puncturedBoundaryMap p S hp r hb
  let H := puncturedJordan_conditions p e S hS hp r hc hi hb hf hx
  exact compactJordanRegionHomeomorph_boundary (e '' T) H.1 (e ∘ R)
    (e.continuous.comp (hc.subtype_mk _))
    (e.injective.comp (fun _ _ h => hi (congrArg Subtype.val h))) H.2.1 H.2.2
    (by rintro y ⟨w, rfl⟩; exact ⟨R w, hb (mem_range_self w), rfl⟩) z

end Punctured

#print axioms compactJordanRegionHomeomorph
#print axioms compactJordanRegionHomeomorph_boundary
#print axioms puncturedJordanDisk
#print axioms puncturedJordanDisk_boundary
end Venn19.Topology
