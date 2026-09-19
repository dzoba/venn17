import VennTopology.DiagramCurves
import VennTopology.TriangleMidline

noncomputable section
namespace Venn17.Topology
open Set
open scoped Classical
local instance regionsDecidableEq : DecidableEq Nat := Classical.decEq _

/-- Bounds and distinctness of the actual vertices of every encoded triangle. -/
theorem encodedTriangle_bounds (fs : Array Face) (n : Nat)
    (hc : cornersCheck fs n = true) (hd : distinctCornersCheck fs = true)
    (t : Fin (4*fs.size)) :
    let c := LinkProof.triangleVertex fs n t.val 0
    let u := LinkProof.triangleVertex fs n t.val 1
    let v := LinkProof.triangleVertex fs n t.val 2
    n ≤ c ∧ u < n ∧ v < n ∧ c ≠ u ∧ c ≠ v ∧ u ≠ v := by
  have h1 := cornersCheck_sound fs n hc (triangleFace fs t) (triangleCorner fs t)
  have h2 := cornersCheck_sound fs n hc (triangleFace fs t) (Quad.next (triangleCorner fs t))
  have hi := triangleVertices_injective fs n hc hd t
  have hne : LinkProof.triangleVertex fs n t.val 1 ≠ LinkProof.triangleVertex fs n t.val 2 :=
    fun h => (by decide : (1 : Fin 3) ≠ 2) (hi h)
  simp only [triangleVertex_zero,triangleVertex_one,triangleVertex_two] at hne ⊢
  exact ⟨by omega,h1,h2,by omega,by omega,hne⟩

theorem dominates_avoids_curves (fs : Array Face) (n count : Nat)
    (hc : cornersCheck fs n = true) (hd : distinctCornersCheck fs = true)
    (v : Fin n) {x : Coordinates.Point Nat} (hx : Coordinates.Dominates n v.val x) :
    x ∉ ⋃ i : Fin count, encodedCurve fs n i.val := by
  rintro ⟨_,⟨i,rfl⟩,hi⟩
  obtain ⟨t,_,ht⟩ := mem_iUnion₂.mp hi
  obtain ⟨hb,hu,hv,_,_,huv⟩ := encodedTriangle_bounds fs n hc hd t
  rw [pairPoint_center, pairPoint_ends] at ht
  have hp : (1/2 : ℝ) • Coordinates.vertex (LinkProof.triangleVertex fs n t.val 1) +
      (1/2 : ℝ) • Coordinates.vertex (LinkProof.triangleVertex fs n t.val 2) =
      Coordinates.pairPoint (LinkProof.triangleVertex fs n t.val 1,LinkProof.triangleVertex fs n t.val 2) := by
    simp [Coordinates.pairPoint,smul_add]
  rw [hp] at ht
  exact Coordinates.midline_not_dominates hb hu hv huv v.isLt ht hx

theorem curve_complement_unique_region (fs : Array Face) (n count : Nat)
    (hc : cornersCheck fs n = true) (hd : distinctCornersCheck fs = true)
    (hl : CurveProof.labelsCheck fs n count = true) {x : Coordinates.Point Nat}
    (hx : x ∈ Coordinates.realization (encodedCells fs n)) :
    x ∉ ⋃ i : Fin count, encodedCurve fs n i.val ↔
      ∃! v : Fin n, Coordinates.Dominates n v.val x := by
  constructor
  · intro hnot
    obtain ⟨t,ht⟩ := mem_iUnion.mp hx
    obtain ⟨hb,hu,hv,hcu,hcv,huv⟩ := encodedTriangle_bounds fs n hc hd t
    have ht' : x ∈ Coordinates.simplex
        {LinkProof.triangleVertex fs n t.val 0,LinkProof.triangleVertex fs n t.val 1,
          LinkProof.triangleVertex fs n t.val 2} := ht
    have hne : x (LinkProof.triangleVertex fs n t.val 1) ≠ x (LinkProof.triangleVertex fs n t.val 2) := by
      intro he
      have hm := (Coordinates.triangle_midline_iff hcu hcv huv ht').mpr he
      obtain ⟨i,hi⟩ := CurveProof.labelsCheck_sound fs n count hl t
      apply hnot
      refine mem_iUnion.mpr ⟨i,mem_iUnion₂.mpr ⟨t,hi,?_⟩⟩
      rw [pairPoint_center,pairPoint_ends]
      simpa [Coordinates.pairPoint,smul_add] using hm
    have hex : ∃ v : Fin n, Coordinates.Dominates n v.val x := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine ⟨⟨_,hv⟩,Coordinates.triangle_dominates_of_lt hb hv hu ?_ hlt⟩
        simpa only [Finset.pair_comm] using ht'
      · exact ⟨⟨_,hu⟩,Coordinates.triangle_dominates_of_lt hb hu hv ht' hgt⟩
    obtain ⟨v,hv⟩ := hex
    refine ⟨v,hv,?_⟩
    intro w hw
    exact Fin.ext (Coordinates.dominates_disjoint w.isLt v.isLt hw hv)
  · rintro ⟨v,hv,_⟩
    exact dominates_avoids_curves fs n count hc hd v hv

/-- Every region is star-convex about its pattern vertex, hence path connected. -/
theorem encoded_region_pathConnected (fs : Array Face) (n : Nat)
    (hcov : coverageCheck fs n = true) (v : Fin n) :
    IsPathConnected (Coordinates.region (encodedCells fs n) n v.val) := by
  apply (Coordinates.region_starConvex (encodedCells fs n) n v.val).isPathConnected
  refine ⟨?_,Coordinates.dominates_vertex⟩
  obtain ⟨f,k,hk⟩ := coverageCheck_sound fs n hcov v.val v.isLt
  obtain ⟨t,ht⟩ := triangleFaceCorner_surjective fs (f,k)
  have hf := congrArg Prod.fst ht
  have hk' := congrArg Prod.snd ht
  dsimp only at hf hk'
  refine mem_iUnion.mpr ⟨t,Coordinates.vertex_mem_simplex ?_⟩
  have he : LinkProof.triangleVertex fs n t.val 1 = v.val := by
    rw [triangleVertex_one,hf,hk',hk]
  rw [← he]
  simp [encodedCells]

attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons

/-- The region associated to a pattern is the part of the surface where its
region coordinate is strictly larger than every other region coordinate. -/
def diagramRegion (v : Fin 131072) : Set Diagram :=
  {x | Coordinates.Dominates 131072 v.val (diagramEncodedHomeomorph x).val}

theorem diagram_complement_unique_region (x : Diagram) :
    x ∉ ⋃ i : Fin 17, diagramCurve i ↔ ∃! v : Fin 131072, x ∈ diagramRegion v := by
  have h := curve_complement_unique_region suppliedModel.oriented 131072 17
    supplied_corners_bounded supplied_distinct_corners_verified supplied_curve_labels_verified
    (diagramEncodedHomeomorph x).property
  simpa only [mem_iUnion,diagramCurve,diagramRegion,mem_setOf_eq] using h

theorem diagramRegion_disjoint {u v : Fin 131072} (huv : u ≠ v) :
    Disjoint (diagramRegion u) (diagramRegion v) := by
  rw [Set.disjoint_left]
  intro x hxu hxv
  exact huv (Fin.ext (Coordinates.dominates_disjoint u.isLt v.isLt hxu hxv))

theorem supplied_region_coverage : coverageCheck suppliedModel.oriented 131072 = true := by
  have h := supplied_incidence_verified
  simp only [suppliedIncidenceCheck,incidenceCheck,Bool.and_eq_true] at h
  simpa only [supplied_graph_size] using h.1.1.2

theorem patternPoint_mem_region (v : Fin 131072) : patternPoint v ∈ diagramRegion v := by
  change Coordinates.Dominates 131072 v.val
    (Coordinates.reindex (Coordinates.labelEquiv 131072 suppliedModel.oriented.size)
      (Quad.point (.inl v.val)))
  rw [← Quad.coordinates_vertex_eq,Coordinates.reindex_vertex,
    Coordinates.labelEquiv_region _ _ _ v.isLt]
  exact Coordinates.dominates_vertex

theorem diagramRegion_pathConnected (v : Fin 131072) : IsPathConnected (diagramRegion v) := by
  have hp := encoded_region_pathConnected suppliedModel.oriented 131072 supplied_region_coverage v
  have hp' := hp.preimage_coe (fun _ hx => hx.1)
  have he : (((↑) : Coordinates.realization (encodedCells suppliedModel.oriented 131072) →
      Coordinates.Point Nat) ⁻¹' Coordinates.region (encodedCells suppliedModel.oriented 131072) 131072 v.val) =
      {x | Coordinates.Dominates 131072 v.val x.val} := by
    ext x
    exact and_iff_right x.property
  rw [he] at hp'
  exact diagramEncodedHomeomorph.isPathConnected_preimage.mpr hp'

theorem dominates_isOpen (n v : Nat) : IsOpen {x : Coordinates.Point Nat | Coordinates.Dominates n v x} := by
  have he : {x : Coordinates.Point Nat | Coordinates.Dominates n v x} =
      {x | 0 < x v} ∩ ⋂ w : Fin n, {x | w.val = v ∨ x w.val < x v} := by
    ext x
    simp only [Coordinates.Dominates,mem_setOf_eq,mem_inter_iff,mem_iInter]
    constructor
    · rintro ⟨h,h'⟩; exact ⟨h,fun w => by by_cases hw : w.val = v; exact Or.inl hw; exact Or.inr (h' w hw)⟩
    · rintro ⟨h,h'⟩; exact ⟨h,fun w hw => (h' w).resolve_left hw⟩
  rw [he]
  refine (isOpen_lt continuous_const (continuous_apply v)).inter (isOpen_iInter_of_finite ?_)
  intro w
  by_cases hw : w.val = v
  · simp [hw]
  · simpa only [hw,false_or] using isOpen_lt (continuous_apply w.val) (continuous_apply v)

theorem diagramRegion_isOpen (v : Fin 131072) : IsOpen (diagramRegion v) :=
  (dominates_isOpen 131072 v.val).preimage
    (continuous_subtype_val.comp diagramEncodedHomeomorph.continuous)

def diagramComplement : Set Diagram := (⋃ i : Fin 17, diagramCurve i)ᶜ

def complementRegion (v : Fin 131072) : Set diagramComplement :=
  Subtype.val ⁻¹' diagramRegion v

theorem region_subset_complement (v : Fin 131072) : diagramRegion v ⊆ diagramComplement := by
  intro x hx
  apply (diagram_complement_unique_region x).mpr
  refine ⟨v,hx,?_⟩
  intro w hw
  exact Fin.ext (Coordinates.dominates_disjoint w.isLt v.isLt hw hx)

theorem complementRegion_isOpen (v : Fin 131072) : IsOpen (complementRegion v) :=
  (diagramRegion_isOpen v).preimage continuous_subtype_val

theorem complementRegion_pairwise : Pairwise (Function.onFun Disjoint complementRegion) := by
  intro u v huv
  exact (diagramRegion_disjoint huv).preimage Subtype.val

theorem complementRegion_cover : (⋃ v, complementRegion v) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨v,hv,_⟩ := (diagram_complement_unique_region x.val).mp x.property
  exact mem_iUnion.mpr ⟨v,hv⟩

theorem complementRegion_isClopen (v : Fin 131072) : IsClopen (complementRegion v) := by
  have he : (complementRegion v)ᶜ = ⋃ w : {w : Fin 131072 // w ≠ v}, complementRegion w.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨w,hw⟩ := mem_iUnion.mp (show x ∈ ⋃ w, complementRegion w by rw [complementRegion_cover]; trivial)
      exact mem_iUnion.mpr ⟨⟨w,fun h => hx (h ▸ hw)⟩,hw⟩
    · intro hx
      obtain ⟨w,hw⟩ := mem_iUnion.mp hx
      intro hv
      exact Set.disjoint_left.mp (complementRegion_pairwise w.property) hw hv
  refine ⟨isOpen_compl_iff.mp ?_,complementRegion_isOpen v⟩
  rw [he]
  exact isOpen_iUnion (fun w => complementRegion_isOpen w.val)

theorem complementRegion_pathConnected (v : Fin 131072) : IsPathConnected (complementRegion v) :=
  (diagramRegion_pathConnected v).preimage_coe (region_subset_complement v)

/-- The actual geometric complement has exactly one connected component per
region pattern. This is independent of the still-missing sphere homeomorphism. -/
def diagramComponentsEquiv : ConnectedComponents diagramComplement ≃ Fin 131072 :=
  ConnectedComponents.equivOfIsClopenOfIsConnected complementRegion_isClopen
    complementRegion_pairwise complementRegion_cover
    (fun v => (complementRegion_pathConnected v).isConnected)

theorem diagram_complement_component_count : Nat.card (ConnectedComponents diagramComplement) = 131072 := by
  rw [Nat.card_congr diagramComponentsEquiv]
  simp

#print axioms diagram_complement_component_count
#print axioms diagram_complement_unique_region
end Venn17.Topology
