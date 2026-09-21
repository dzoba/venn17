import VennTopology.RegionBits
import Venn19.Facts

noncomputable section
namespace Venn19.Topology
open Set
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

def sideSign (b : Bool) : ℝ := if b then 1 else -1

theorem sideSign_sq (b : Bool) : sideSign b * sideSign b = 1 := by
  cases b <;> norm_num [sideSign]

theorem sideActive_iff_sign (i v : Nat) (b : Bool) :
    sideActive i b v = true ↔ 0 < sideSign b * bitSign i v := by
  simp only [sideActive,beq_iff_eq,bitSign,Nat.testBit_eq_decide_div_mod_eq]
  cases b <;> by_cases h : v / 2^i % 2 = 1 <;> norm_num [sideSign,h]

def ambientSide (i : Fin 19) (b : Bool) : Set (Quad.Ambient Nat (Fin suppliedModel.oriented.size)) :=
  diagramQuad.space ∩ {x | 0 < sideSign b * diagramQuad.bitField 524288 i.val x}

def diagramSide (i : Fin 19) (b : Bool) : Set Diagram :=
  {x | 0 < sideSign b * diagramBitField i x}

theorem signed_halfspace_convex (i : Fin 19) (b : Bool) :
    Convex ℝ {x | 0 < sideSign b * diagramQuad.bitField 524288 i.val x} := by
  exact (convex_Ioi (0 : ℝ)).linear_preimage (sideSign b • diagramQuad.bitField 524288 i.val)

theorem side_triangle_joined (i : Fin 19) (b : Bool)
    (f : Fin suppliedModel.oriented.size) (k : Fin 4)
    {x y : Quad.Ambient Nat (Fin suppliedModel.oriented.size)}
    (hx : x ∈ diagramQuad.triangle f k) (hy : y ∈ diagramQuad.triangle f k)
    (hsx : 0 < sideSign b * diagramQuad.bitField 524288 i.val x)
    (hsy : 0 < sideSign b * diagramQuad.bitField 524288 i.val y) :
    JoinedIn (ambientSide i b) x y := by
  have hconv := (convex_convexHull ℝ (diagramQuad.triangleVertices f k)).inter (signed_halfspace_convex i b)
  exact ((hconv.isPathConnected ⟨x,hx,hsx⟩).joinedIn x ⟨hx,hsx⟩ y ⟨hy,hsy⟩).mono
    (fun _ hz => ⟨diagramQuad.triangle_subset_space f k hz.1,hz.2⟩)

/-- Every point on a signed side joins a region vertex on that same side. -/
theorem side_point_joined_vertex (i : Fin 19) (b : Bool)
    {x : Quad.Ambient Nat (Fin suppliedModel.oriented.size)} (hx : x ∈ ambientSide i b) :
    ∃ v : Fin 524288, sideActive i.val b v.val = true ∧
      JoinedIn (ambientSide i b) x (Quad.point (.inl v.val)) := by
  obtain ⟨f,k,ht⟩ := mem_iUnion₂.mp hx.1
  have hc := diagram_corners_injective f
  have hb : ∀ k, diagramQuad.corner f k < 524288 := cornersCheck_sound _ _ supplied_corners_bounded f
  have hf := diagramQuad.bitField_triangle 524288 i.val f hc hb k ht
  have hsum := diagramQuad.triangle_corner_sum f hc ht
  change x (.inr f) + x (.inl (diagramQuad.corner f k)) +
    x (.inl (diagramQuad.corner f (Quad.next k))) = 1 at hsum
  have hu := Coordinates.simplex_nonneg (diagramQuad.triangle_eq_simplex f k ▸ ht) (.inl (diagramQuad.corner f k))
  have hv := Coordinates.simplex_nonneg (diagramQuad.triangle_eq_simplex f k ▸ ht) (.inl (diagramQuad.corner f (Quad.next k)))
  have hpos : 0 < sideSign b * bitSign i.val (diagramQuad.corner f k) ∨
      0 < sideSign b * bitSign i.val (diagramQuad.corner f (Quad.next k)) := by
    rcases diagram_faceSign_cases i f with hconst | ⟨hzero,_⟩
    · left
      rw [hconst k,hconst (Quad.next k)] at hf
      have he : diagramQuad.bitField 524288 i.val x = diagramQuad.faceSign i.val f := by
        rw [← add_mul,← add_mul,hsum,one_mul] at hf
        exact hf
      rw [hconst k,← he]; exact hx.2
    · rw [hzero,mul_zero,zero_add] at hf
      by_contra! hn
      have h1 := mul_nonpos_of_nonneg_of_nonpos hu hn.1
      have h2 := mul_nonpos_of_nonneg_of_nonpos hv hn.2
      have he : sideSign b * diagramQuad.bitField 524288 i.val x =
          x (.inl (diagramQuad.corner f k)) * (sideSign b * bitSign i.val (diagramQuad.corner f k)) +
          x (.inl (diagramQuad.corner f (Quad.next k))) * (sideSign b * bitSign i.val (diagramQuad.corner f (Quad.next k))) := by rw [hf]; ring
      have hp : 0 < sideSign b * diagramQuad.bitField 524288 i.val x := hx.2
      rw [he] at hp
      exact (not_lt_of_ge (add_nonpos h1 h2)) hp
  rcases hpos with hp | hp
  · refine ⟨⟨_,hb k⟩,(sideActive_iff_sign _ _ _).mpr hp,?_⟩
    apply side_triangle_joined i b f k ht (diagramQuad.corner_mem_triangle f k) hx.2
    rwa [diagramQuad.bitField_region 524288 i.val _ (hb k)]
  · refine ⟨⟨_,hb (Quad.next k)⟩,(sideActive_iff_sign _ _ _).mpr hp,?_⟩
    apply side_triangle_joined i b f k ht (diagramQuad.next_corner_mem_triangle f k) hx.2
    rwa [diagramQuad.bitField_region 524288 i.val _ (hb (Quad.next k))]

theorem side_vertex_mem (i : Fin 19) (b : Bool) (v : Nat) (hv : v < 524288)
    (ha : sideActive i.val b v = true) : Quad.point (.inl v) ∈ ambientSide i b := by
  refine ⟨(patternPoint ⟨v,hv⟩).property,?_⟩
  change 0 < sideSign b * diagramQuad.bitField 524288 i.val (Quad.point (.inl v))
  rw [diagramQuad.bitField_region 524288 i.val v hv]
  exact (sideActive_iff_sign _ _ _).mp ha

theorem side_walk_joined (i : Fin 19) (b : Bool) {u v : Nat}
    (hw : GraphProof.Walk suppliedModel.graph (sideActive i.val b) u v) (hu : u < 524288) :
    JoinedIn (ambientSide i b) (Quad.point (.inl u)) (Quad.point (.inl v)) := by
  have hedges := supplied_incidence_verified
  simp only [suppliedIncidenceCheck,incidenceCheck,Bool.and_eq_true] at hedges
  induction hw with
  | refl v ha => exact JoinedIn.refl (side_vertex_mem i b v hu ha)
  | @step u v w ha he rest ih =>
    obtain ⟨f,k,hfu,hfv⟩ := edgesCheck_sound _ _ hedges.1.2 u v (by simpa only [supplied_graph_size] using hu) he
    have hb := cornersCheck_sound _ _ supplied_corners_bounded f
    have hv : v < 524288 := hfv ▸ hb (Quad.next k)
    have hav : sideActive i.val b v = true := by cases rest with
      | refl _ h => exact h
      | step h _ _ => exact h
    have hj : JoinedIn (ambientSide i b) (Quad.point (.inl u)) (Quad.point (.inl v)) := by
      apply side_triangle_joined i b f k
      · rw [← hfu]; exact diagramQuad.corner_mem_triangle f k
      · rw [← hfv]; exact diagramQuad.next_corner_mem_triangle f k
      · exact (side_vertex_mem i b u hu ha).2
      · exact (side_vertex_mem i b v hv hav).2
    exact hj.trans (ih hv)

theorem ambientSide_pathConnected (i : Fin 19) (b : Bool) : IsPathConnected (ambientSide i b) := by
  obtain ⟨r,hr,ha,hw⟩ := each_side_connected i.val i.isLt b
  have hr' : r < 524288 := by simpa only [supplied_graph_size] using hr
  refine ⟨Quad.point (.inl r),side_vertex_mem i b r hr' ha,fun {x} hx => ?_⟩
  obtain ⟨v,hv,hj⟩ := side_point_joined_vertex i b hx
  exact (hj.trans (side_walk_joined i b (hw v.val (by simpa only [supplied_graph_size] using v.isLt) hv) v.isLt)).symm

theorem diagramSide_pathConnected (i : Fin 19) (b : Bool) : IsPathConnected (diagramSide i b) := by
  have h := (ambientSide_pathConnected i b).preimage_coe (fun _ hx => hx.1)
  have he : ((↑) : Diagram → Quad.Ambient Nat (Fin suppliedModel.oriented.size)) ⁻¹' ambientSide i b = diagramSide i b := by
    ext x; exact and_iff_right x.property
  exact he ▸ h

#print axioms diagramSide_pathConnected
end Venn19.Topology
