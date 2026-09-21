import VennTopology.DiagramSymmetry
import VennTopology.Intersections

noncomputable section
namespace Venn19.Topology

open Set Quad

namespace Quad.Automorphism
variable {V F : Type*} {q : Quad V F}

theorem rotated_triangle_inter_subset (a : q.Automorphism) (f : F) (k : Fin 4) (p : V)
    (hf : a.faces f ≠ f)
    (hu : q.corner f k = a.vertices (q.corner f k) ∨
      q.corner f k = a.vertices (q.corner f (next k)) → q.corner f k = p)
    (hv : q.corner f (next k) = a.vertices (q.corner f k) ∨
      q.corner f (next k) = a.vertices (q.corner f (next k)) → q.corner f (next k) = p) :
    q.triangle f k ∩ q.triangle (a.faces f) (a.corners f k) ⊆ {point (.inl p)} := by
  rw [q.triangle_inter]
  have hverts : q.triangleVertices f k ∩ q.triangleVertices (a.faces f) (a.corners f k)
      ⊆ {point (.inl p)} := by
    intro x hx
    simp only [triangleVertices, ← a.next_eq, ← a.corner_eq,
      mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hx ⊢
    rcases hx with ⟨hx, hy⟩
    rcases hx with rfl | rfl | rfl
    · simp only [point_injective.eq_iff, Sum.inr.injEq, Sum.inr_ne_inl, or_false] at hy
      exact False.elim (hf hy.symm)
    · simp only [point_injective.eq_iff, Sum.inl.injEq, Sum.inl_ne_inr, false_or] at hy
      exact congrArg (fun v => point (.inl v)) (hu hy)
    · simp only [point_injective.eq_iff, Sum.inl.injEq, Sum.inl_ne_inr, false_or] at hy
      exact congrArg (fun v => point (.inl v)) (hv hy)
  simpa only [convexHull_singleton] using convexHull_mono (𝕜 := ℝ) hverts

end Quad.Automorphism

theorem supplied_fixed_triangles_verified : fixedTriangleCheck suppliedModel.oriented = true := by
  native_decide

attribute [local irreducible] suppliedModel suppliedFaces

theorem fixed_triangle_check_at (fs : Array Face) (h : fixedTriangleCheck fs = true)
    (f : Fin fs.size) (k : Fin 4) :
    (rotationWitnesses fs)[f.val]! ≠ f.val ∧
    let u := (quadOfFaces fs).corner f k
    let v := (quadOfFaces fs).corner f (next k)
    ((u = regionStep u ∨ u = regionStep v) → u = trianglePole u v) ∧
    ((v = regionStep u ∨ v = regionStep v) → v = trianglePole u v) := by
  have h := Array.all_eq_true.mp h f.val (by simp)
  simp only [Array.getElem_range, Bool.and_eq_true, bne_iff_ne] at h
  have hk := Array.all_eq_true.mp h.2 k.val (by simp)
  simp only [Array.getElem_range, Bool.and_eq_true, decide_eq_true_eq] at hk
  exact ⟨h.1, hk⟩

/-- The two specified poles are all the fixed points, even at points in the
interiors of triangles and edges. -/
theorem diagram_rotation_fixed_iff (x : Diagram) :
    diagramRotation x = x ↔ x = patternPoint 0 ∨ x = patternPoint 524287 := by
  constructor
  · intro hfix
    obtain ⟨f, k, hx⟩ := mem_iUnion.mp x.property |>.imp (fun f => mem_iUnion.mp)
    have h := fixed_triangle_check_at _ supplied_fixed_triangles_verified f k
    let u := diagramQuad.corner f k
    let v := diagramQuad.corner f (next k)
    have hf : diagramAutomorphism.faces f ≠ f := by
      intro he
      exact h.1 (congrArg Fin.val he)
    have hy : x.val ∈ diagramQuad.triangle (diagramAutomorphism.faces f)
        (diagramAutomorphism.corners f k) := by
      have hm := mem_image_of_mem (coordinateHomeomorph diagramAutomorphism.labels) hx
      rw [diagramAutomorphism.triangle_image] at hm
      have he : coordinateHomeomorph diagramAutomorphism.labels x.val = x.val :=
        congrArg Subtype.val hfix
      rwa [he] at hm
    have he := diagramAutomorphism.rotated_triangle_inter_subset f k (trianglePole u v)
      hf h.2.1 h.2.2 ⟨hx, hy⟩
    have hp : trianglePole u v = 0 ∨ trianglePole u v = 524287 := by
      unfold trianglePole
      split <;> simp
    rcases hp with hp | hp
    · left
      apply Subtype.ext
      exact (mem_singleton_iff.mp he).trans (congrArg (fun n => point (.inl n)) hp)
    · right
      apply Subtype.ext
      exact (mem_singleton_iff.mp he).trans (congrArg (fun n => point (.inl n)) hp)
  · rintro (rfl | rfl)
    · exact diagram_rotation_fixes_zero
    · exact diagram_rotation_fixes_one

#print axioms diagram_rotation_fixed_iff

end Venn19.Topology
