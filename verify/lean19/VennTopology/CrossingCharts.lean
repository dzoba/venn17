import VennTopology.CrossingAxes

noncomputable section
namespace Venn19.Topology
open Set

namespace Quad
variable {V F : Type*} (q : Quad V F)

theorem arm_subset_triangle (f : F) (k : Fin 4) : q.arm f k ⊆ q.triangle f k := by
  apply (convex_convexHull ℝ _).segment_subset (q.center_mem_triangle f k)
  have h := (convex_convexHull ℝ (q.triangleVertices f k))
    (q.corner_mem_triangle f k) (q.next_corner_mem_triangle f k)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+1/2 = 1)
  simpa only [triangle,smul_add] using h

theorem arm_face_of_center_positive (f g : F) (k : Fin 4) {x : Ambient V F}
    (hp : 0 < x (.inr f)) (hx : x ∈ q.arm g k) : f = g := by
  have ht := q.arm_subset_triangle g k hx
  rw [q.triangle_eq_simplex] at ht
  have hm := Coordinates.positive_coordinate_in_cell q.cellLabels ht hp
  simpa [cellLabels] using hm

theorem centerStar_curve_iff {q : Quad Nat F} (f : F) (x : q.centerStar f) (i : Nat) :
    x.val.val ∈ q.edgeCurve i ↔
      ∃ k : Fin 4, q.corner f k ^^^ q.corner f (next k) = 2^i ∧ x.val.val ∈ q.arm f k := by
  constructor
  · intro hx
    obtain ⟨g,k,hl,hx⟩ := mem_iUnion.mp hx |>.imp (fun _ => mem_iUnion₂.mp)
    have he := q.arm_face_of_center_positive f g k x.property hx
    subst g
    exact ⟨k,hl,hx⟩
  · rintro ⟨k,hl,hx⟩
    exact mem_iUnion.mpr ⟨f,mem_iUnion₂.mpr ⟨k,hl,hx⟩⟩

end Quad

theorem edgeMask_triangle (fs : Array Face) (n t : Nat) :
    CurveProof.edgeMask fs n t = LinkProof.triangleVertex fs n t 1 ^^^ LinkProof.triangleVertex fs n t 2 := by
  unfold CurveProof.edgeMask CurveProof.ends
  by_cases h : LinkProof.triangleVertex fs n t 1 ≤ LinkProof.triangleVertex fs n t 2
  · simp [min_eq_left h,max_eq_right h]
  · simp [min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h),Nat.xor_comm]

theorem edgeMask_face (fs : Array Face) (n : Nat) (f : Fin fs.size) (k : Fin 4) :
    CurveProof.edgeMask fs n (4*f.val+k.val) =
      (quadOfFaces fs).corner f k ^^^ (quadOfFaces fs).corner f (Quad.next k) := by
  let t : Fin (4*fs.size) := ⟨4*f.val+k.val,by have := f.isLt; omega⟩
  have hf : triangleFace fs t = f := by apply Fin.ext; dsimp [triangleFace,t]; omega
  have hk : triangleCorner fs t = k := by apply Fin.ext; dsimp [triangleCorner,t]; omega
  change CurveProof.edgeMask fs n t.val = _
  rw [edgeMask_triangle,triangleVertex_one,triangleVertex_two,hf,hk]

theorem crossing_labels_alternate (fs : Array Face) (n count : Nat)
    (hl : CurveProof.labelsCheck fs n count = true)
    (hc : CurveProof.crossingLabelsCheck fs n = true) (f : Fin fs.size) :
    ∃ i j : Fin count, i ≠ j ∧
      (∀ k : Fin 4, ((quadOfFaces fs).corner f k ^^^ (quadOfFaces fs).corner f (Quad.next k) = 2^i.val ↔ k.val%2 = 0)) ∧
      (∀ k : Fin 4, ((quadOfFaces fs).corner f k ^^^ (quadOfFaces fs).corner f (Quad.next k) = 2^j.val ↔ k.val%2 = 1)) := by
  let t : Fin (4*fs.size) := ⟨4*f.val,by have := f.isLt; omega⟩
  let s : Fin (4*fs.size) := ⟨4*f.val+1,by have := f.isLt; omega⟩
  obtain ⟨i,hi⟩ := CurveProof.labelsCheck_sound fs n count hl t
  obtain ⟨j,hj⟩ := CurveProof.labelsCheck_sound fs n count hl s
  have hmi : CurveProof.edgeMask fs n (4*f.val) = 2^i.val := by
    simpa only [CurveProof.edgeMask,CurveProof.hasLabel,beq_iff_eq,t] using hi
  have hmj : CurveProof.edgeMask fs n (4*f.val+1) = 2^j.val := by
    simpa only [CurveProof.edgeMask,CurveProof.hasLabel,beq_iff_eq,s] using hj
  have hf := Array.all_eq_true.mp hc f.val (by simp)
  simp only [Array.getElem_range,Bool.and_eq_true,bne_iff_ne] at hf
  have hne : 2^i.val ≠ 2^j.val := by rw [← hmi,← hmj]; exact hf.1
  have hmask (k : Fin 4) : CurveProof.edgeMask fs n (4*f.val+k.val) =
      if k.val%2 = 0 then 2^i.val else 2^j.val := by
    have hk := Array.all_eq_true.mp hf.2 k.val (by simp)
    simp only [Array.getElem_range,beq_iff_eq] at hk
    rw [hk]
    by_cases he : k.val%2 = 0
    · simpa [he] using hmi
    · have he' : k.val%2 = 1 := by omega
      simpa [he,he'] using hmj
  refine ⟨i,j,fun he => hne (congrArg (fun k : Fin count => 2^k.val) he),?_,?_⟩
  all_goals
    intro k
    rw [← edgeMask_face fs n f k,hmask]
    by_cases he : k.val%2 = 0
    · simp [he,hne]
    · have he' : k.val%2 = 1 := by omega
      simp [he',Ne.symm hne]

attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

/-- A topological transverse crossing: an open neighborhood has a plane chart
that maps the two labelled curves exactly to the two coordinate axes. -/
theorem diagram_transverse_crossing (f : Fin suppliedModel.oriented.size) :
    ∃ i j : Fin 19, i ≠ j ∧ CrossingSquare.HasCrossingChart
      (diagramCurve i) (diagramCurve j) (crossingPoint f) := by
  obtain ⟨i,j,hij,hi,hj⟩ := crossing_labels_alternate suppliedModel.oriented 524288 19
    supplied_curve_labels_verified supplied_crossing_labels_verified f
  refine ⟨i,j,hij,diagramQuad.centerStar f,diagramQuad.open_star_isOpen (.inr f),?_,
    diagramQuad.centerSquareChart f (diagram_corners_injective f),?_,?_,?_⟩
  · change 0 < Quad.point (.inr f) (.inr f)
    simp [Quad.point]
  · intro x hx
    apply diagramQuad.centerSquareChart_center f (diagram_corners_injective f) x
    exact congrArg Subtype.val hx
  · intro x
    rw [diagramCurve_original,Quad.centerStar_curve_iff]
    apply Iff.trans (exists_congr (fun k => and_congr (hi k) Iff.rfl))
    exact diagramQuad.centerSquareChart_even_axis f (diagram_corners_injective f) x
  · intro x
    rw [diagramCurve_original,Quad.centerStar_curve_iff]
    apply Iff.trans (exists_congr (fun k => and_congr (hj k) Iff.rfl))
    exact diagramQuad.centerSquareChart_odd_axis f (diagram_corners_injective f) x

#print axioms diagram_transverse_crossing
end Venn19.Topology
