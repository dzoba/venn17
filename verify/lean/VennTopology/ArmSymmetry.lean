import VennTopology.CurveIntersections

noncomputable section
namespace Venn17.Topology
open Set

namespace Quad
variable {V F : Type*} (q : Quad V F)

/-- A crossing-to-arc-midpoint segment in the original coordinate space. -/
def arm (f : F) (k : Fin 4) : Set (Ambient V F) :=
  segment ℝ (point (.inr f))
    ((1/2 : ℝ) • (point (.inl (q.corner f k)) + point (.inl (q.corner f (next k)))))

theorem Automorphism.arm_image (a : q.Automorphism) (f : F) (k : Fin 4) :
    coordinateHomeomorph a.labels '' q.arm f k = q.arm (a.faces f) (a.corners f k) := by
  change coordinateLinear a.labels '' _ = _
  rw [arm, ← LinearMap.coe_toAffineMap, image_segment]
  simp only [LinearMap.coe_toAffineMap, map_smul, map_add, coordinateLinear_point]
  simp only [arm, Automorphism.labels, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, a.corner_eq, a.next_eq]

def edgeCurve (q : Quad Nat F) (i : Nat) : Set (Ambient Nat F) :=
  ⋃ f, ⋃ k, ⋃ (_ : q.corner f k ^^^ q.corner f (next k) = 2^i), q.arm f k

theorem Automorphism.edgeCurve_image {q : Quad Nat F} (a : q.Automorphism)
    (i j : Nat) (h : ∀ f k,
      q.corner f k ^^^ q.corner f (next k) = 2^i ↔
        q.corner (a.faces f) (a.corners f k) ^^^
          q.corner (a.faces f) (next (a.corners f k)) = 2^j) :
    coordinateHomeomorph a.labels '' q.edgeCurve i = q.edgeCurve j := by
  simp only [edgeCurve,image_iUnion,a.arm_image]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨f,k,hl,hx⟩
    exact ⟨a.faces f,a.corners f k,(h f k).mp hl,hx⟩
  · rintro ⟨f,k,hl,hx⟩
    obtain ⟨g,rfl⟩ := a.faces.surjective f
    obtain ⟨l,rfl⟩ := (a.corners g).surjective k
    exact ⟨g,l,(h g l).mpr hl,hx⟩

end Quad

theorem reindex_arm (fs : Array Face) (n : Nat) (hc : cornersCheck fs n = true)
    (t : Fin (4*fs.size)) :
    Coordinates.reindex (Coordinates.labelEquiv n fs.size) ''
      (quadOfFaces fs).arm (triangleFace fs t) (triangleCorner fs t) =
    segment ℝ (Coordinates.pairPoint (CurveProof.center fs n t.val))
      (Coordinates.pairPoint (CurveProof.ends fs n t.val)) := by
  let e := Coordinates.labelEquiv n fs.size
  let L := (LinearEquiv.piCongrLeft ℝ (fun _ : Nat => ℝ) e).toLinearMap
  change L '' _ = _
  rw [Quad.arm, ← LinearMap.coe_toAffineMap, image_segment]
  simp only [LinearMap.coe_toAffineMap, map_smul, map_add]
  have hv (a : Nat ⊕ Fin fs.size) : L (Quad.point a) = Coordinates.vertex (e a) := by
    rw [← Quad.coordinates_vertex_eq]
    exact Coordinates.reindex_vertex e a
  rw [hv,hv,hv,pairPoint_center,pairPoint_ends,
    triangleVertex_zero,triangleVertex_one,triangleVertex_two]
  dsimp only [e]
  rw [Coordinates.labelEquiv_face,
    Coordinates.labelEquiv_region _ _ _ (cornersCheck_sound fs n hc _ _),
    Coordinates.labelEquiv_region _ _ _ (cornersCheck_sound fs n hc _ _),smul_add]

theorem reindex_edgeCurve (fs : Array Face) (n i : Nat) (hc : cornersCheck fs n = true) :
    Coordinates.reindex (Coordinates.labelEquiv n fs.size) '' (quadOfFaces fs).edgeCurve i =
      encodedCurve fs n i := by
  simp only [Quad.edgeCurve,image_iUnion]
  ext x
  simp only [encodedCurve,mem_iUnion]
  constructor
  · rintro ⟨f,k,hl,hx⟩
    obtain ⟨t,ht⟩ := triangleFaceCorner_surjective fs (f,k)
    have hf := congrArg Prod.fst ht
    have hk := congrArg Prod.snd ht
    dsimp only at hf hk
    refine ⟨t,?_,?_⟩
    · rw [hasLabel_mask,triangleVertex_one,triangleVertex_two,hf,hk]
      exact hl
    · rw [← reindex_arm fs n hc t,hf,hk]
      exact hx
  · rintro ⟨t,hl,hx⟩
    refine ⟨triangleFace fs t,triangleCorner fs t,?_,?_⟩
    · simpa only [hasLabel_mask,triangleVertex_one,triangleVertex_two] using hl
    · rw [reindex_arm fs n hc t]
      exact hx

attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons

theorem diagramCurve_original (i : Fin 17) (x : Diagram) :
    x ∈ diagramCurve i ↔ x.val ∈ diagramQuad.edgeCurve i.val := by
  change Coordinates.reindex (Coordinates.labelEquiv 131072 suppliedModel.oriented.size) x.val ∈
    encodedCurve suppliedModel.oriented 131072 i.val ↔ _
  rw [← reindex_edgeCurve _ _ _ supplied_corners_bounded]
  exact (Coordinates.reindex _).injective.mem_set_image

#print axioms reindex_edgeCurve
end Venn17.Topology
