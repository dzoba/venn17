import VennTopology.MeridianGeometry

/-! The meridians are embedded closed intervals with the two specified poles
as endpoints. Their coordinate descriptions allow their intersections to be
checked geometrically, rather than inferred from vertex disjointness alone. -/
noncomputable section
namespace Venn19.Topology
open Set Coordinates
open scoped Classical
attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars

abbrev MeridianParameter := Icc (0 : ℝ) 19

def meridianCircleParameter (t : MeridianParameter) : Circle :=
  AddCircle.toCircle (t.val : AddCircle (38 : ℝ))

theorem meridianCircleParameter_continuous : Continuous meridianCircleParameter :=
  AddCircle.continuous_toCircle.comp ((AddCircle.continuous_mk' _).comp continuous_subtype_val)

theorem meridianCircleParameter_injective : Function.Injective meridianCircleParameter := by
  letI : Fact (0 < (38 : ℝ)) := ⟨by norm_num⟩
  intro t u h
  apply Subtype.ext
  have he := AddCircle.injective_toCircle (by norm_num : (38 : ℝ) ≠ 0) h
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
    (show t.val ∈ Ico 0 (0 + 38) from ⟨t.property.1, by linarith [t.property.2]⟩)
    (show u.val ∈ Ico 0 (0 + 38) from ⟨u.property.1, by linarith [u.property.2]⟩)).mp he

def diagramMeridianMap (k : Fin 19) (t : MeridianParameter) : Diagram :=
  diagramMeridianBoundaryMap k (cyclicNext k) (meridianCircleParameter t)

theorem diagramMeridianMap_continuous (k : Fin 19) : Continuous (diagramMeridianMap k) :=
  (diagramMeridianBoundaryMap_continuous _ _).comp meridianCircleParameter_continuous

theorem diagramMeridianMap_injective (k : Fin 19) : Function.Injective (diagramMeridianMap k) :=
  (diagramMeridianBoundaryMap_injective _ _ (cyclicNext_ne (by decide) k).symm).comp
    meridianCircleParameter_injective

/-- Every point of the parameter interval is on one of its 19 unit edges. -/
theorem meridianParameter_edge (t : MeridianParameter) :
    ∃ i : Fin 19, ∃ r : Icc (0 : ℝ) 1, t.val = (i.val : ℝ) + r.val := by
  by_cases ht : t.val = 19
  · exact ⟨18, ⟨1, by norm_num⟩, by norm_num; exact ht⟩
  · have ht' : t.val < 19 := lt_of_le_of_ne t.property.2 ht
    have hf := Nat.floor_le t.property.1
    have hc := Nat.lt_floor_add_one t.val
    have hi : ⌊t.val⌋₊ < 19 := by exact_mod_cast (lt_of_le_of_lt hf ht')
    exact ⟨⟨⌊t.val⌋₊, hi⟩, ⟨t.val - ⌊t.val⌋₊, by constructor <;> linarith⟩, by simp⟩

def meridianEdgeParameter (i : Fin 19) (r : Icc (0 : ℝ) 1) : MeridianParameter :=
  ⟨(i.val : ℝ) + r.val, add_nonneg (Nat.cast_nonneg _) r.property.1, by
    have hi : (i.val : ℝ) + 1 ≤ 19 := by exact_mod_cast i.isLt
    linarith [r.property.2]⟩

theorem meridian_boundary_front (k l : Fin 19) (i : Fin 20) :
    meridianBoundaryLabel k l ⟨i.val, by omega⟩ = meridianLabel k i := by
  simp [meridianBoundaryLabel, i.isLt]

theorem diagramMeridianMap_edge (k : Fin 19) (i : Fin 19) (r : Icc (0 : ℝ) 1) :
    (diagramEncodedHomeomorph (diagramMeridianMap k (meridianEdgeParameter i r))).val =
      (1 - r.val) • vertex (meridianLabel k ⟨i.val, by omega⟩) +
        r.val • vertex (meridianLabel k ⟨i.val + 1, by omega⟩) := by
  change (diagramEncodedHomeomorph (diagramEncodedHomeomorph.symm _)).val = _
  simp only [Homeomorph.apply_symm_apply]
  have he : meridianCircleParameter (meridianEdgeParameter i r) =
      AddCircle.toCircle (edgePhase ((⟨i.val, by omega⟩ : Fin 38), r)) := rfl
  rw [he, labeledPolygonMap_phase, relabel_edgePoint]
  rw [meridian_boundary_front k (cyclicNext k) (⟨i.val, by omega⟩ : Fin 20)]
  have hn : cyclicNext (⟨i.val, by omega⟩ : Fin 38) = ⟨i.val+1, by omega⟩ := by
    apply Fin.ext
    change (i.val + 1) % 38 = i.val + 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [hn, meridian_boundary_front k (cyclicNext k) (⟨i.val+1, by omega⟩ : Fin 20)]

def encodedMeridian (k : Fin 19) : Set (Point Nat) :=
  ⋃ i : Fin 19, segment ℝ (vertex (meridianLabel k ⟨i.val, by omega⟩))
    (vertex (meridianLabel k ⟨i.val+1, by omega⟩))

def diagramMeridian (k : Fin 19) : Set Diagram :=
  {x | (diagramEncodedHomeomorph x).val ∈ encodedMeridian k}

theorem diagramMeridianMap_range (k : Fin 19) : range (diagramMeridianMap k) = diagramMeridian k := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨i, r, ht⟩ := meridianParameter_edge t
    have he : t = meridianEdgeParameter i r := Subtype.ext ht
    rw [he]
    change (diagramEncodedHomeomorph (diagramMeridianMap k _)).val ∈ encodedMeridian k
    rw [diagramMeridianMap_edge]
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [segment_eq_image_lineMap]
    exact ⟨r.val, r.property, AffineMap.lineMap_apply_module _ _ _⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [segment_eq_image_lineMap] at hi
    obtain ⟨r, hr, he⟩ := hi
    refine ⟨meridianEdgeParameter i ⟨r, hr⟩, diagramEncodedHomeomorph.injective (Subtype.ext ?_)⟩
    rw [diagramMeridianMap_edge]
    simpa only [AffineMap.lineMap_apply_module] using he

theorem diagramMeridianMap_zero (k : Fin 19) :
    diagramMeridianMap k ⟨0, by norm_num⟩ = patternPoint 0 := by
  apply diagramEncodedHomeomorph.injective
  apply Subtype.ext
  have h := diagramMeridianMap_edge k 0 ⟨0, by norm_num⟩
  simpa [meridianEdgeParameter, meridian_labels_verified.1 k, patternPoint_encoded, show (18 : ℝ) + 1 = 19 by norm_num] using h

theorem diagramMeridianMap_one (k : Fin 19) :
    diagramMeridianMap k ⟨19, by norm_num⟩ = patternPoint 524287 := by
  apply diagramEncodedHomeomorph.injective
  apply Subtype.ext
  have h := diagramMeridianMap_edge k 18 ⟨1, by norm_num⟩
  simpa [meridianEdgeParameter, meridian_labels_verified.1 k, patternPoint_encoded, show (18 : ℝ) + 1 = 19 by norm_num] using h

theorem diagramMeridianMap_rotation (k : Fin 19) (t : MeridianParameter) :
    diagramRotation (diagramMeridianMap k t) = diagramMeridianMap (cyclicNext k) t :=
  diagramMeridianBoundaryMap_rotation _ _ _

theorem diagram_meridian_rotation (k : Fin 19) :
    diagramRotation '' diagramMeridian k = diagramMeridian (cyclicNext k) := by
  rw [← diagramMeridianMap_range, ← diagramMeridianMap_range, ← range_comp]
  congr 1
  funext t
  exact diagramMeridianMap_rotation k t

/-- Each explicitly constructed meridian is a closed embedded interval. -/
def diagramMeridianHomeomorph (k : Fin 19) : MeridianParameter ≃ₜ diagramMeridian k :=
  ((diagramMeridianMap_continuous k).subtype_mk _).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (Set.rangeFactorization (diagramMeridianMap k))
      ⟨Set.rangeFactorization_injective.mpr (diagramMeridianMap_injective k),
        Set.rangeFactorization_surjective⟩) |>.trans
    (Homeomorph.setCongr (diagramMeridianMap_range k))

#print axioms diagramMeridianHomeomorph
end Venn19.Topology
