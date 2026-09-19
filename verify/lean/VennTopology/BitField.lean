import VennTopology.BitSigns

noncomputable section
namespace Venn17.Topology
open Set
namespace Quad
variable {F : Type*} [Fintype F] (q : Quad Nat F)

/-- The continuous piecewise-linear membership field. Crossing centers carry
average corner values, and region vertices carry their signed bit values. -/
def bitField (n i : Nat) : Ambient Nat F →ₗ[ℝ] ℝ where
  toFun x := (∑ v ∈ Finset.range n, x (.inl v) * bitSign i v) +
    ∑ f : F, x (.inr f) * q.faceSign i f
  map_add' x y := by simp [add_mul,Finset.sum_add_distrib]; ring
  map_smul' r x := by simp [smul_eq_mul,mul_assoc,← Finset.mul_sum,mul_add]

theorem bitField_continuous (n i : Nat) : Continuous (q.bitField n i) := by
  change Continuous (fun x : Ambient Nat F => (∑ v ∈ Finset.range n, x (.inl v) * bitSign i v) +
    ∑ f : F, x (.inr f) * q.faceSign i f)
  fun_prop

theorem bitField_region (n i v : Nat) (hv : v < n) :
    q.bitField n i (point (.inl v)) = bitSign i v := by
  classical
  simp [bitField,point,hv]

theorem bitField_center (n i : Nat) (f : F) :
    q.bitField n i (point (.inr f)) = q.faceSign i f := by
  classical
  simp [bitField,point]

omit [Fintype F] in
theorem triangle_reconstruct (f : F) (hc : Function.Injective (q.corner f))
    (k : Fin 4) {x : Ambient Nat F} (hx : x ∈ q.triangle f k) :
    x (.inr f) • point (.inr f) + x (.inl (q.corner f k)) • point (.inl (q.corner f k)) +
      x (.inl (q.corner f (next k))) • point (.inl (q.corner f (next k))) = x := by
  have hr := Coordinates.simplex_reconstruct (q.triangle_eq_simplex f k ▸ hx)
  have hne : q.corner f k ≠ q.corner f (next k) := fun h => (next_ne k) (hc h).symm
  simpa [cellLabels,coordinates_vertex_eq,hne,add_assoc] using hr

theorem bitField_triangle (n i : Nat) (f : F) (hc : Function.Injective (q.corner f))
    (hb : ∀ k, q.corner f k < n) (k : Fin 4) {x : Ambient Nat F} (hx : x ∈ q.triangle f k) :
    q.bitField n i x = x (.inr f) * q.faceSign i f +
      x (.inl (q.corner f k)) * bitSign i (q.corner f k) +
      x (.inl (q.corner f (next k))) * bitSign i (q.corner f (next k)) := by
  have h := congrArg (q.bitField n i) (q.triangle_reconstruct f hc k hx)
  simpa only [map_add,map_smul,smul_eq_mul,bitField_center,
    bitField_region q n i _ (hb k),bitField_region q n i _ (hb (next k))] using h.symm

omit [Fintype F] in
theorem triangle_arm_iff (f : F) (hc : Function.Injective (q.corner f)) (k : Fin 4)
    {x : Ambient Nat F} (hx : x ∈ q.triangle f k) :
    x ∈ q.arm f k ↔ x (.inl (q.corner f k)) = x (.inl (q.corner f (next k))) := by
  have hne : q.corner f k ≠ q.corner f (next k) := fun h => (next_ne k) (hc h).symm
  have h := Coordinates.triangle_midline_iff
    (c := Sum.inr f) (u := Sum.inl (q.corner f k)) (v := Sum.inl (q.corner f (next k)))
    (by simp) (by simp) (by simp [hne]) (q.triangle_eq_simplex f k ▸ hx)
  simpa only [arm,Coordinates.pairPoint,coordinates_vertex_eq] using h

theorem bitField_arm_zero (n i : Nat) (f : F) (hb : ∀ k, q.corner f k < n) (k : Fin 4)
    (hc : q.faceSign i f = 0)
    (hs : bitSign i (q.corner f k) + bitSign i (q.corner f (next k)) = 0)
    {x : Ambient Nat F} (hx : x ∈ q.arm f k) : q.bitField n i x = 0 := by
  rw [arm,segment_eq_image_lineMap] at hx
  obtain ⟨r,_,rfl⟩ := hx
  simp only [AffineMap.lineMap_apply_module,map_add,map_smul,smul_eq_mul,
    bitField_center,bitField_region q n i _ (hb k),bitField_region q n i _ (hb (next k)),hc,hs]
  ring

end Quad
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

def diagramBitField (i : Fin 17) (x : Diagram) : ℝ := diagramQuad.bitField 131072 i.val x.val

theorem diagramBitField_continuous (i : Fin 17) : Continuous (diagramBitField i) :=
  (diagramQuad.bitField_continuous 131072 i.val).comp continuous_subtype_val

theorem diagramBitField_pattern (i : Fin 17) (v : Fin 131072) :
    diagramBitField i (patternPoint v) = bitSign i.val v.val :=
  diagramQuad.bitField_region 131072 i.val v.val v.isLt

#print axioms diagramBitField_continuous
end Venn17.Topology
