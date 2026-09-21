import VennTopology.Regions

noncomputable section
namespace Venn19.Topology
open Set
open scoped Classical
local instance puncturedRegionsDecidableEq : DecidableEq Nat := Classical.decEq _

namespace Coordinates
variable {T : Type*} (cells : T → Finset Nat)

theorem dominates_convex (n v : Nat) : Convex ℝ {x : Point Nat | Dominates n v x} := by
  intro x hx y hy a b ha hb hab
  have hpos : 0 < a ∨ 0 < b := by by_contra! h; linarith
  refine ⟨?_,fun w hw => ?_⟩
  · change 0 < a * x v + b * y v
    rcases hpos with hp | hp
    · exact add_pos_of_pos_of_nonneg (mul_pos hp hx.1) (mul_nonneg hb hy.1.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ha hx.1.le) (mul_pos hp hy.1)
  · change a * x w.val + b * y w.val < a * x v + b * y v
    have h1 := hx.2 w hw
    have h2 := hy.2 w hw
    rcases hpos with hp | hp
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h1 hp) (mul_le_mul_of_nonneg_left h2.le hb)
    · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left h1.le ha) (mul_lt_mul_of_pos_left h2 hp)

/-- A small circle around the pattern vertex lies strictly inside its region. -/
theorem shell_mem_punctured_region (n v : Nat) {y : Point Nat} (hy : y ∈ link cells v) :
    mix v (3/4 : ℝ) y ∈ region cells n v \ {vertex v} := by
  have hc := mix_coordinate cells hy (3/4 : ℝ)
  refine ⟨⟨mix_mem_realization cells hy (by norm_num) (by norm_num),?_,?_⟩,?_⟩
  · rw [hc]; norm_num
  · intro w hw
    obtain ⟨t,ht⟩ := mem_iUnion.mp (link_mem_realization cells hy)
    have hb := simplex_le_one ht w.val
    change (3/4 : ℝ) * vertex v w.val + (1-3/4) * y w.val < _
    rw [vertex_other hw,hc]
    linarith
  · intro he
    have he' := congrArg (fun x : Point Nat => x v) (mem_singleton_iff.mp he)
    rw [hc,vertex_self] at he'
    norm_num at he'

theorem punctured_region_pathConnected (n v : Nat)
    (hf : ∀ t a, a ∈ cells t → ((cells t).erase a).Nonempty)
    (hl : IsPathConnected (link cells v)) :
    IsPathConnected (region cells n v \ {vertex v}) := by
  let shell : Point Nat → Point Nat := mix v (3/4 : ℝ)
  have hcont : Continuous shell := by unfold shell mix; fun_prop
  have hs := hl.image hcont
  have hsub : shell '' link cells v ⊆ region cells n v \ {vertex v} := by
    rintro _ ⟨y,hy,rfl⟩
    exact shell_mem_punctured_region cells n v hy
  obtain ⟨b,hb⟩ := hs.nonempty
  refine ⟨b,hsub hb,fun {x} hx => ?_⟩
  have hxp : x ∈ puncturedStar cells v := by
    rw [puncturedStar_eq_delete_vertex cells hf]
    exact ⟨⟨hx.1.1,hx.1.2.1⟩,hx.2⟩
  let y := radialProjection v x
  have hy : y ∈ link cells v := puncturedStar_decomposition cells hf hxp
  have hsy : shell y ∈ shell '' link cells v := mem_image_of_mem _ hy
  have hshell := hsub hsy
  obtain ⟨t,hvt,hyt⟩ := mem_iUnion₂.mp hy
  have hycell := simplex_mono (Finset.erase_subset v (cells t)) hyt
  have hvertex := vertex_mem_simplex hvt
  have hxc : x ∈ simplex (cells t) := by
    rw [← mix_radialProjection v x hxp.2.2]
    exact (convex_convexHull ℝ _) hvertex hycell hxp.2.1.le (sub_nonneg.mpr hxp.2.2.le) (by ring)
  have hsc : shell y ∈ simplex (cells t) :=
    (convex_convexHull ℝ _) hvertex hycell (by norm_num) (by norm_num) (by norm_num)
  let S : Set (Point Nat) := simplex (cells t) ∩ {z | Dominates n v z} ∩ {z | z v < 1}
  have hcv : Convex ℝ {z : Point Nat | z v < 1} := by
    intro z hz w hw a b ha hb hab
    change a * z v + b * w v < 1
    have hp : 0 < a ∨ 0 < b := by by_contra! h; linarith
    rcases hp with hp | hp
    · have := add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hz hp) (mul_le_mul_of_nonneg_left hw.le hb)
      nlinarith
    · have := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hz.le ha) (mul_lt_mul_of_pos_left hw hp)
      nlinarith
  have hS : Convex ℝ S := ((convex_convexHull ℝ _).inter (dominates_convex n v)).inter hcv
  have hxS : x ∈ S := ⟨⟨hxc,hx.1.2⟩,hxp.2.2⟩
  have hsS : shell y ∈ S := ⟨⟨hsc,hshell.1.2⟩,by
    change mix v (3/4 : ℝ) y v < 1
    rw [mix_coordinate cells hy]
    norm_num⟩
  have hSm : S ⊆ region cells n v \ {vertex v} := by
    intro z hz
    refine ⟨⟨mem_iUnion.mpr ⟨t,hz.1.1⟩,hz.1.2⟩,?_⟩
    intro he
    have h : z v < 1 := hz.2
    rw [mem_singleton_iff.mp he,vertex_self] at h
    exact lt_irrefl _ h
  exact ((hs.joinedIn b hb (shell y) hsy).mono hsub).trans
    (((hS.isPathConnected ⟨x,hxS⟩).joinedIn _ hsS _ hxS).mono hSm)

end Coordinates

attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

theorem encoded_cells_erase_nonempty (t : Fin (4*suppliedModel.oriented.size)) (a : Nat)
    (_ha : a ∈ encodedCells suppliedModel.oriented 524288 t) :
    ((encodedCells suppliedModel.oriented 524288 t).erase a).Nonempty := by
  have h := encodedTriangle_bounds _ _ supplied_corners_bounded supplied_distinct_corners_verified t
  apply Finset.Nontrivial.erase_nonempty
  exact ⟨LinkProof.triangleVertex _ _ t.val 0,by simp [encodedCells],
    LinkProof.triangleVertex _ _ t.val 1,by simp [encodedCells],h.2.2.2.1⟩

def encodedRegionLinkCircle (v : Fin 524288) :
    Circle ≃ₜ Coordinates.link (encodedCells suppliedModel.oriented 524288) v.val :=
  (supplied_dart_link_circle ⟨v.val,by rw [supplied_link_rows.1]; omega⟩).trans
    (Homeomorph.setCongr (encoded_link_eq_dartLink _ _ _
      (triangleVertices_injective _ _ supplied_corners_bounded supplied_distinct_corners_verified)).symm)

theorem encoded_region_link_pathConnected (v : Fin 524288) :
    IsPathConnected (Coordinates.link (encodedCells suppliedModel.oriented 524288) v.val) := by
  have h := isPathConnected_univ.image
    (continuous_subtype_val.comp (encodedRegionLinkCircle v).continuous)
  have he : (fun z => (encodedRegionLinkCircle v z).val) '' Set.univ =
      Coordinates.link (encodedCells suppliedModel.oriented 524288) v.val := by
    ext x
    constructor
    · rintro ⟨z,_,rfl⟩; exact (encodedRegionLinkCircle v z).property
    · intro hx
      obtain ⟨z,hz⟩ := (encodedRegionLinkCircle v).surjective ⟨x,hx⟩
      exact ⟨z,trivial,congrArg Subtype.val hz⟩
  change IsPathConnected ((fun z => (encodedRegionLinkCircle v z).val) '' Set.univ) at h
  rwa [he] at h

theorem patternPoint_encoded (v : Fin 524288) :
    (diagramEncodedHomeomorph (patternPoint v)).val = Coordinates.vertex v.val := by
  change Coordinates.reindex (Coordinates.labelEquiv 524288 suppliedModel.oriented.size)
    (Quad.point (.inl v.val)) = _
  rw [← Quad.coordinates_vertex_eq,Coordinates.reindex_vertex,Coordinates.labelEquiv_region _ _ _ v.isLt]

/-- Puncturing any region at its pattern vertex preserves path connectedness;
in particular this discharges the connectivity issue at the future infinity. -/
theorem diagramRegion_punctured_pathConnected (v : Fin 524288) :
    IsPathConnected (diagramRegion v \ {patternPoint v}) := by
  have h := Coordinates.punctured_region_pathConnected
    (encodedCells suppliedModel.oriented 524288) 524288 v.val
    encoded_cells_erase_nonempty (encoded_region_link_pathConnected v)
  have hp := h.preimage_coe (fun _ hx => hx.1.1)
  have hpre := diagramEncodedHomeomorph.isPathConnected_preimage.mpr hp
  convert hpre using 1
  ext x
  change (Coordinates.Dominates _ _ _ ∧ x ≠ patternPoint v) ↔
    (( _ ∧ Coordinates.Dominates _ _ _) ∧ (diagramEncodedHomeomorph x).val ≠ Coordinates.vertex v.val)
  rw [← patternPoint_encoded v]
  simp only [(diagramEncodedHomeomorph x).property,true_and]
  apply and_congr_right
  intro _
  exact not_congr (Subtype.val_injective.eq_iff.trans diagramEncodedHomeomorph.injective.eq_iff).symm

#print axioms diagramRegion_punctured_pathConnected
end Venn19.Topology
