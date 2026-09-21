import VennTopology.Regions

noncomputable section
namespace Venn19.Topology
open Set
open scoped Classical

namespace Coordinates

theorem arm_region_support {n c u v w : Nat} (hc : n ≤ c) (hw : w < n)
    {x : Point Nat} (hx : x ∈ segment ℝ (vertex c) (pairPoint (u,v))) (hp : 0 < x w) :
    w = u ∨ w = v := by
  by_contra! h
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨r,_,rfl⟩ := hx
  have hwc : w ≠ c := by omega
  simp [AffineMap.lineMap_apply_module,pairPoint,vertex,hwc,h.1,h.2] at hp

theorem arm_positive_endpoints {n c u v : Nat} (hc : n ≤ c) (hu : u < n)
    (hv : v < n) (huv : u ≠ v) {x : Point Nat}
    (hx : x ∈ segment ℝ (vertex c) (pairPoint (u,v))) (hne : x ≠ vertex c) :
    0 < x u ∧ 0 < x v := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨r,hr,rfl⟩ := hx
  have hr0 : r ≠ 0 := by intro h; apply hne; simp [AffineMap.lineMap_apply_module,h]
  have hp : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
  have huc : u ≠ c := by omega
  have hvc : v ≠ c := by omega
  simp [AffineMap.lineMap_apply_module,pairPoint,vertex,huc,hvc,huv,Ne.symm huv]
  positivity

theorem arm_center_unique {n c d u v : Nat} (hc : n ≤ c) (hu : u < n) (hv : v < n)
    (hx : vertex c ∈ segment ℝ (vertex d) (pairPoint (u,v))) : c = d := by
  by_contra hcd
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨r,_,he⟩ := hx
  have hh := congrFun he c
  have hcu : c ≠ u := by omega
  have hcv : c ≠ v := by omega
  simp [AffineMap.lineMap_apply_module,pairPoint,vertex,hcu,hcv,hcd] at hh

end Coordinates

theorem hasLabel_mask (fs : Array Face) (n i t : Nat) :
    CurveProof.hasLabel fs n i t = true ↔
      LinkProof.triangleVertex fs n t 1 ^^^ LinkProof.triangleVertex fs n t 2 = 2^i := by
  unfold CurveProof.hasLabel CurveProof.ends
  by_cases h : LinkProof.triangleVertex fs n t 1 ≤ LinkProof.triangleVertex fs n t 2
  · simp [min_eq_left h,max_eq_right h]
  · simp [min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h),Nat.xor_comm]

theorem arm_as_segment (fs : Array Face) (n t : Nat) :
    segment ℝ (Coordinates.pairPoint (CurveProof.center fs n t))
      (Coordinates.pairPoint (CurveProof.ends fs n t)) =
    segment ℝ (Coordinates.vertex (LinkProof.triangleVertex fs n t 0))
      (Coordinates.pairPoint (LinkProof.triangleVertex fs n t 1,LinkProof.triangleVertex fs n t 2)) := by
  rw [pairPoint_center,pairPoint_ends]
  simp [Coordinates.pairPoint,smul_add]

/-- Distinct labelled curves can meet only at actual crossing centers. -/
theorem encodedCurve_intersection_center (fs : Array Face) (n : Nat)
    (hc : cornersCheck fs n = true) (hd : distinctCornersCheck fs = true)
    {i j : Nat} (hij : i ≠ j) {x : Coordinates.Point Nat}
    (hi : x ∈ encodedCurve fs n i) (hj : x ∈ encodedCurve fs n j) :
    ∃ f : Fin fs.size, x = Coordinates.vertex (n+f.val) := by
  obtain ⟨t,hti,ht⟩ := mem_iUnion₂.mp hi
  obtain ⟨s,hsj,hs⟩ := mem_iUnion₂.mp hj
  rw [arm_as_segment] at ht hs
  obtain ⟨htc,htu,htv,_,_,htuv⟩ := encodedTriangle_bounds fs n hc hd t
  obtain ⟨hsc,hsu,hsv,_,_,hsuv⟩ := encodedTriangle_bounds fs n hc hd s
  by_cases he : x = Coordinates.vertex (LinkProof.triangleVertex fs n t.val 0)
  · exact ⟨triangleFace fs t,by simpa only [triangleVertex_zero] using he⟩
  · obtain ⟨hpu,hpv⟩ := Coordinates.arm_positive_endpoints htc htu htv htuv ht he
    have hu := Coordinates.arm_region_support hsc htu hs hpu
    have hv := Coordinates.arm_region_support hsc htv hs hpv
    have hm : LinkProof.triangleVertex fs n t.val 1 ^^^ LinkProof.triangleVertex fs n t.val 2 =
        LinkProof.triangleVertex fs n s.val 1 ^^^ LinkProof.triangleVertex fs n s.val 2 := by
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact False.elim (htuv (hu.trans hv.symm))
      · rw [hu,hv]
      · rw [hu,hv,Nat.xor_comm]
      · exact False.elim (htuv (hu.trans hv.symm))
    have hi' := (hasLabel_mask fs n i t.val).mp hti
    have hj' := (hasLabel_mask fs n j s.val).mp hsj
    exact False.elim (hij ((Nat.pow_right_inj (by decide : 1 < 2)).mp (hi'.symm.trans (hm.trans hj'))))

/-- A curve through a center must use one of that face's four arms. -/
theorem center_on_curve (fs : Array Face) (n : Nat) (hc : cornersCheck fs n = true)
    (hd : distinctCornersCheck fs = true) (f : Fin fs.size) (i : Nat)
    (hx : Coordinates.vertex (n+f.val) ∈ encodedCurve fs n i) :
    ∃ k : Fin 4, CurveProof.hasLabel fs n i (4*f.val+k.val) = true := by
  obtain ⟨t,hl,ht⟩ := mem_iUnion₂.mp hx
  rw [arm_as_segment] at ht
  obtain ⟨_,hu,hv,_,_,_⟩ := encodedTriangle_bounds fs n hc hd t
  have he := Coordinates.arm_center_unique (n := n) (by omega : n ≤ n+f.val) hu hv ht
  rw [triangleVertex_zero] at he
  have hface : (triangleFace fs t).val = f.val := by omega
  have hidx : t.val = 4*f.val+t.val%4 := by dsimp [triangleFace] at hface; omega
  refine ⟨⟨t.val%4,by omega⟩,?_⟩
  simpa only [← hidx] using hl

theorem crossingLabelsCheck_sound (fs : Array Face) (n : Nat)
    (h : CurveProof.crossingLabelsCheck fs n = true) (f : Fin fs.size) (k : Fin 4) :
    CurveProof.edgeMask fs n (4*f.val+k.val) = CurveProof.edgeMask fs n (4*f.val) ∨
    CurveProof.edgeMask fs n (4*f.val+k.val) = CurveProof.edgeMask fs n (4*f.val+1) := by
  have hf := Array.all_eq_true.mp h f.val (by simp)
  simp only [Array.getElem_range,Bool.and_eq_true] at hf
  have hk := Array.all_eq_true.mp hf.2 k.val (by simp)
  simp only [Array.getElem_range,beq_iff_eq] at hk
  have hm : k.val%2 = 0 ∨ k.val%2 = 1 := by omega
  rcases hm with hm | hm
  · exact Or.inl (by simpa only [hm,Nat.add_zero] using hk)
  · exact Or.inr (by simpa only [hm] using hk)

theorem center_curve_two_labels (fs : Array Face) (n : Nat) (hc : cornersCheck fs n = true)
    (hd : distinctCornersCheck fs = true) (hl : CurveProof.crossingLabelsCheck fs n = true)
    (f : Fin fs.size) (i : Nat) (hi : Coordinates.vertex (n+f.val) ∈ encodedCurve fs n i) :
    2^i = CurveProof.edgeMask fs n (4*f.val) ∨ 2^i = CurveProof.edgeMask fs n (4*f.val+1) := by
  obtain ⟨k,hk⟩ := center_on_curve fs n hc hd f i hi
  have hm : CurveProof.edgeMask fs n (4*f.val+k.val) = 2^i := by
    simpa only [CurveProof.edgeMask,CurveProof.hasLabel,beq_iff_eq] using hk
  simpa only [hm] using crossingLabelsCheck_sound fs n hl f k

theorem encoded_no_triple (fs : Array Face) (n : Nat) (hc : cornersCheck fs n = true)
    (hd : distinctCornersCheck fs = true) (hl : CurveProof.crossingLabelsCheck fs n = true)
    {i j k : Nat} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {x : Coordinates.Point Nat}
    (hi : x ∈ encodedCurve fs n i) (hj : x ∈ encodedCurve fs n j) : x ∉ encodedCurve fs n k := by
  intro hk
  obtain ⟨f,rfl⟩ := encodedCurve_intersection_center fs n hc hd hij hi hj
  have hi' := center_curve_two_labels fs n hc hd hl f i hi
  have hj' := center_curve_two_labels fs n hc hd hl f j hj
  have hk' := center_curve_two_labels fs n hc hd hl f k hk
  have h1 : 2^i ≠ 2^j := fun h => hij ((Nat.pow_right_inj (by decide : 1 < 2)).mp h)
  have h2 : 2^i ≠ 2^k := fun h => hik ((Nat.pow_right_inj (by decide : 1 < 2)).mp h)
  have h3 : 2^j ≠ 2^k := fun h => hjk ((Nat.pow_right_inj (by decide : 1 < 2)).mp h)
  rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj' <;> rcases hk' with hk' | hk' <;> omega

theorem center_has_two_curves (fs : Array Face) (n count : Nat)
    (hl : CurveProof.labelsCheck fs n count = true)
    (hp : CurveProof.crossingLabelsCheck fs n = true) (f : Fin fs.size) :
    ∃ i j : Fin count, i ≠ j ∧ Coordinates.vertex (n+f.val) ∈ encodedCurve fs n i.val ∧
      Coordinates.vertex (n+f.val) ∈ encodedCurve fs n j.val := by
  let t : Fin (4*fs.size) := ⟨4*f.val,by have := f.isLt; omega⟩
  let s : Fin (4*fs.size) := ⟨4*f.val+1,by have := f.isLt; omega⟩
  obtain ⟨i,hi⟩ := CurveProof.labelsCheck_sound fs n count hl t
  obtain ⟨j,hj⟩ := CurveProof.labelsCheck_sound fs n count hl s
  have hface := Array.all_eq_true.mp hp f.val (by simp)
  simp only [Array.getElem_range,Bool.and_eq_true,bne_iff_ne] at hface
  have hmi : CurveProof.edgeMask fs n (4*f.val) = 2^i.val := by
    simpa only [CurveProof.edgeMask,CurveProof.hasLabel,beq_iff_eq,t] using hi
  have hmj : CurveProof.edgeMask fs n (4*f.val+1) = 2^j.val := by
    simpa only [CurveProof.edgeMask,CurveProof.hasLabel,beq_iff_eq,s] using hj
  refine ⟨i,j,?_,?_,?_⟩
  · intro h
    exact hface.1 (hmi.trans ((congrArg (fun k : Fin count => 2^k.val) h).trans hmj.symm))
  · refine mem_iUnion₂.mpr ⟨t,hi,?_⟩
    rw [arm_as_segment]
    have he : LinkProof.triangleVertex fs n t.val 0 = n+f.val := by
      simp [LinkProof.triangleVertex,t]
    rw [he]
    exact left_mem_segment ℝ _ _
  · refine mem_iUnion₂.mpr ⟨s,hj,?_⟩
    rw [arm_as_segment]
    have he : LinkProof.triangleVertex fs n s.val 0 = n+f.val := by
      simp [LinkProof.triangleVertex,s,Nat.add_div]
    rw [he]
    exact left_mem_segment ℝ _ _

attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons

theorem diagram_no_triple_intersections (i j k : Fin 19) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : Diagram) (hi : x ∈ diagramCurve i) (hj : x ∈ diagramCurve j) : x ∉ diagramCurve k :=
  encoded_no_triple suppliedModel.oriented 524288 supplied_corners_bounded
    supplied_distinct_corners_verified supplied_crossing_labels_verified
    (fun h => hij (Fin.ext h)) (fun h => hik (Fin.ext h)) (fun h => hjk (Fin.ext h)) hi hj

def crossingPoint (f : Fin suppliedModel.oriented.size) : Diagram :=
  ⟨Quad.point (.inr f),diagramQuad.triangle_subset_space f 0 (diagramQuad.center_mem_triangle f 0)⟩

theorem crossingPoint_injective : Function.Injective crossingPoint := by
  intro f g h
  exact Sum.inr.inj (Quad.point_injective (congrArg Subtype.val h))

theorem crossingPoint_encoded (f : Fin suppliedModel.oriented.size) :
    (diagramEncodedHomeomorph (crossingPoint f)).val = Coordinates.vertex (524288+f.val) := by
  change Coordinates.reindex (Coordinates.labelEquiv 524288 suppliedModel.oriented.size)
    (Quad.point (.inr f)) = _
  rw [← Quad.coordinates_vertex_eq,Coordinates.reindex_vertex,Coordinates.labelEquiv_face]

/-- Every listed crossing occurs geometrically, and it lies on precisely two
curves. No extra crossings occur along the interiors of the arcs. -/
theorem diagram_crossing_iff (x : Diagram) :
    (∃ i j : Fin 19, i ≠ j ∧ x ∈ diagramCurve i ∧ x ∈ diagramCurve j) ↔
      ∃ f : Fin suppliedModel.oriented.size, x = crossingPoint f := by
  constructor
  · rintro ⟨i,j,hij,hi,hj⟩
    obtain ⟨f,hf⟩ := encodedCurve_intersection_center suppliedModel.oriented 524288
      supplied_corners_bounded supplied_distinct_corners_verified
      (fun h => hij (Fin.ext h)) hi hj
    refine ⟨f,diagramEncodedHomeomorph.injective ?_⟩
    apply Subtype.ext
    rw [crossingPoint_encoded]
    exact hf
  · rintro ⟨f,rfl⟩
    obtain ⟨i,j,hij,hi,hj⟩ := center_has_two_curves suppliedModel.oriented 524288 19
      supplied_curve_labels_verified supplied_crossing_labels_verified f
    refine ⟨i,j,hij,?_,?_⟩
    · change (diagramEncodedHomeomorph (crossingPoint f)).val ∈ encodedCurve suppliedModel.oriented 524288 i.val
      rw [crossingPoint_encoded]
      exact hi
    · change (diagramEncodedHomeomorph (crossingPoint f)).val ∈ encodedCurve suppliedModel.oriented 524288 j.val
      rw [crossingPoint_encoded]
      exact hj

theorem diagram_crossing_exactly_two (f : Fin suppliedModel.oriented.size) :
    ∃ i j : Fin 19, i ≠ j ∧ ∀ k : Fin 19,
      crossingPoint f ∈ diagramCurve k ↔ k = i ∨ k = j := by
  obtain ⟨i,j,hij,hi,hj⟩ := (diagram_crossing_iff (crossingPoint f)).mpr ⟨f,rfl⟩
  refine ⟨i,j,hij,?_⟩
  intro k
  constructor
  · intro hk
    by_cases hki : k = i
    · exact Or.inl hki
    · by_cases hkj : k = j
      · exact Or.inr hkj
      · exact False.elim (diagram_no_triple_intersections i j k hij (Ne.symm hki)
          (Ne.symm hkj) (crossingPoint f) hi hj hk)
  · rintro (rfl | rfl) <;> assumption

#print axioms diagram_crossing_iff
#print axioms diagram_no_triple_intersections
end Venn19.Topology
