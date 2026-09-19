import VennTopology.BitField

noncomputable section
namespace Venn17.Topology
open Set
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

theorem diagram_curve_field_zero (i : Fin 17) (x : Diagram) (hx : x ∈ diagramCurve i) :
    diagramBitField i x = 0 := by
  rw [diagramCurve_original] at hx
  obtain ⟨f,k,hl,hx⟩ := mem_iUnion.mp hx |>.imp (fun _ => mem_iUnion₂.mp)
  have hne := (diagram_edge_bitSign f k i).mpr hl
  have hs : bitSign i.val (diagramQuad.corner f k) + bitSign i.val (diagramQuad.corner f (Quad.next k)) = 0 := by
    rcases bitSign_cases i.val (diagramQuad.corner f k) with h | h <;>
      rcases bitSign_cases i.val (diagramQuad.corner f (Quad.next k)) with h' | h' <;> simp_all
  have hc : diagramQuad.faceSign i.val f = 0 := by
    rcases diagram_faceSign_cases i f with hc | hc
    · exact False.elim (hne ((hc k).trans (hc (Quad.next k)).symm))
    · exact hc.1
  exact diagramQuad.bitField_arm_zero 131072 i.val f
    (fun k => cornersCheck_sound _ _ supplied_corners_bounded f k) k hc hs hx

/-- The zero set is precisely the labelled curve, including centers where the
current triangle has a different edge label. -/
theorem diagram_field_zero_curve (i : Fin 17) (x : Diagram) (hx : diagramBitField i x = 0) :
    x ∈ diagramCurve i := by
  obtain ⟨f,k,ht⟩ := mem_iUnion₂.mp x.property
  have hc := diagram_corners_injective f
  have hb := cornersCheck_sound _ _ supplied_corners_bounded f
  have hf := diagramQuad.bitField_triangle 131072 i.val f hc hb k ht
  have hsum := diagramQuad.triangle_corner_sum f hc ht
  have hxu := Coordinates.simplex_nonneg (diagramQuad.triangle_eq_simplex f k ▸ ht) (.inl (diagramQuad.corner f k))
  have hxv := Coordinates.simplex_nonneg (diagramQuad.triangle_eq_simplex f k ▸ ht) (.inl (diagramQuad.corner f (Quad.next k)))
  change x.val (.inr f) + x.val (.inl (diagramQuad.corner f k)) +
    x.val (.inl (diagramQuad.corner f (Quad.next k))) = 1 at hsum
  change diagramQuad.bitField 131072 i.val x.val = 0 at hx
  rw [hx] at hf
  rw [diagramCurve_original]
  rcases diagram_faceSign_cases i f with hconst | ⟨hcenter,l,hl⟩
  · have hs := bitSign_cases i.val (diagramQuad.corner f k)
    have hu := hconst k
    have hv := hconst (Quad.next k)
    rw [hv,← hu] at hf
    rcases hs with hs | hs <;> rw [hs] at hf <;> nlinarith
  · rw [hcenter, mul_zero,zero_add] at hf
    by_cases hlabel : diagramQuad.corner f k ^^^ diagramQuad.corner f (Quad.next k) = 2^i.val
    · refine mem_iUnion.mpr ⟨f,mem_iUnion₂.mpr ⟨k,hlabel,?_⟩⟩
      apply (diagramQuad.triangle_arm_iff f hc k ht).mpr
      have hn := (diagram_edge_bitSign f k i).mpr hlabel
      rcases bitSign_cases i.val (diagramQuad.corner f k) with hu | hu <;>
        rcases bitSign_cases i.val (diagramQuad.corner f (Quad.next k)) with hv | hv <;>
          rw [hu,hv] at hf <;> rw [hu,hv] at hn <;> norm_num at hn <;> linarith
    · have he := not_not.mp ((not_congr (diagram_edge_bitSign f k i)).mpr hlabel)
      have hz : x.val (.inl (diagramQuad.corner f k)) = 0 ∧
          x.val (.inl (diagramQuad.corner f (Quad.next k))) = 0 := by
        rw [← he] at hf
        rcases bitSign_cases i.val (diagramQuad.corner f k) with hs | hs <;>
          rw [hs] at hf <;> constructor <;> nlinarith
      have hxcenter : x.val = Quad.point (.inr f) := by
        have hr := diagramQuad.triangle_reconstruct f hc k ht
        have hh : x.val (.inr f) = 1 := by linarith [hz.1,hz.2]
        simpa only [hz.1,hz.2,hh,zero_smul,add_zero,one_smul] using hr.symm
      refine mem_iUnion.mpr ⟨f,mem_iUnion₂.mpr ⟨l,hl,?_⟩⟩
      rw [hxcenter]
      exact left_mem_segment ℝ _ _

theorem diagram_curve_iff_field_zero (i : Fin 17) (x : Diagram) :
    x ∈ diagramCurve i ↔ diagramBitField i x = 0 :=
  ⟨diagram_curve_field_zero i x,diagram_field_zero_curve i x⟩

/-- A geometric bit coordinate is continuous, interpolates every pattern, and
has exactly the intended embedded circle as its zero set. -/
theorem diagram_bit_field_verified (i : Fin 17) :
    Continuous (diagramBitField i) ∧
    (∀ v : Fin 131072, diagramBitField i (patternPoint v) = bitSign i.val v.val) ∧
    (∀ x : Diagram, x ∈ diagramCurve i ↔ diagramBitField i x = 0) :=
  ⟨diagramBitField_continuous i,diagramBitField_pattern i,diagram_curve_iff_field_zero i⟩

#print axioms diagram_curve_iff_field_zero
end Venn17.Topology
