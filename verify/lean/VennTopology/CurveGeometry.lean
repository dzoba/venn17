import VennTopology.CurveCertificate
import VennTopology.GeometricLinks

noncomputable section
namespace Venn17.Topology
open Set
open scoped Classical

/-- The actual center-to-midpoint arms belonging to a bit label, in the
contiguous coordinate encoding of the original triangulation. -/
def encodedCurve (fs : Array Face) (n i : Nat) : Set (Coordinates.Point Nat) :=
  ⋃ t : Fin (4*fs.size), ⋃ (_ : CurveProof.hasLabel fs n i t.val = true),
    segment ℝ (Coordinates.pairPoint (CurveProof.center fs n t.val))
      (Coordinates.pairPoint (CurveProof.ends fs n t.val))

def curveVertices (p : CurveProof.Polygon) (j : Fin p.vertices.size) : Nat × Nat :=
  p.vertices.getD j.val (0,0)

theorem encodedCurve_eq_polygon (fs : Array Face) (n i : Nat) (p : CurveProof.Polygon)
    (hp : CurveProof.check fs n i p = true) :
    encodedCurve fs n i = Coordinates.pairPolygon (curveVertices p) := by
  obtain ⟨hr,hcov⟩ := Bool.and_eq_true_iff.mp hp
  have hs := (CurveProof.polygonCheck_sound fs n i p hr).2.2.2
  ext x
  simp only [encodedCurve, Coordinates.pairPolygon, mem_iUnion]
  constructor
  · rintro ⟨t, ht, hx⟩
    obtain ⟨j,hj⟩ := CurveProof.coverageCheck_sound fs n i p hcov t ht
    have he := (CurveProof.edgeCheck_sound fs n i p j.val (hs j)).2.2
    rw [hj] at he
    refine ⟨j, ?_⟩
    change x ∈ segment ℝ (Coordinates.pairPoint (p.vertices.getD j.val (0,0)))
      (Coordinates.pairPoint (p.vertices.getD ((j.val+1)%p.vertices.size) (0,0)))
    rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa only [ha,hb] using hx
    · simpa only [ha,hb,segment_symm] using hx
  · rintro ⟨j,hj⟩
    obtain ⟨hb,hl,he⟩ := CurveProof.edgeCheck_sound fs n i p j.val (hs j)
    refine ⟨⟨p.triangles.getD j.val (4*fs.size),hb⟩,hl,?_⟩
    change x ∈ segment ℝ (Coordinates.pairPoint (p.vertices.getD j.val (0,0)))
      (Coordinates.pairPoint (p.vertices.getD ((j.val+1)%p.vertices.size) (0,0))) at hj
    rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa only [ha,hb] using hj
    · simpa only [ha,hb,segment_symm] using hj

def encodedCurveHomeomorph (fs : Array Face) (n i : Nat) (p : CurveProof.Polygon)
    (hp : CurveProof.check fs n i p = true) : Circle ≃ₜ encodedCurve fs n i := by
  have hr := CurveProof.polygonCheck_sound fs n i p (Bool.and_eq_true_iff.mp hp).1
  exact (Coordinates.pairPolygonHomeomorph (curveVertices p)
    (CurveProof.supportsCheck_disjoint _ _ hr.2.2.1) hr.1).trans
    (Homeomorph.setCongr (encodedCurve_eq_polygon fs n i p hp).symm)

theorem pairPoint_center (fs : Array Face) (n t : Nat) :
    Coordinates.pairPoint (CurveProof.center fs n t) =
      Coordinates.vertex (LinkProof.triangleVertex fs n t 0) := by
  unfold Coordinates.pairPoint CurveProof.center
  module

theorem pairPoint_ends (fs : Array Face) (n t : Nat) :
    Coordinates.pairPoint (CurveProof.ends fs n t) =
      (1/2 : ℝ) • Coordinates.vertex (LinkProof.triangleVertex fs n t 1) +
      (1/2 : ℝ) • Coordinates.vertex (LinkProof.triangleVertex fs n t 2) := by
  unfold Coordinates.pairPoint CurveProof.ends
  by_cases h : LinkProof.triangleVertex fs n t 1 ≤ LinkProof.triangleVertex fs n t 2
  · simp only [min_eq_left h,max_eq_right h,smul_add]
  · simp only [min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h),smul_add,add_comm]

theorem curve_arm_subset_triangle (fs : Array Face) (n : Nat) (t : Fin (4*fs.size)) :
    segment ℝ (Coordinates.pairPoint (CurveProof.center fs n t.val))
      (Coordinates.pairPoint (CurveProof.ends fs n t.val)) ⊆ Coordinates.simplex (encodedCells fs n t) := by
  rw [pairPoint_center, pairPoint_ends]
  have h0 := Coordinates.vertex_mem_simplex (show LinkProof.triangleVertex fs n t.val 0 ∈
    encodedCells fs n t by simp [encodedCells])
  have h1 := Coordinates.vertex_mem_simplex (show LinkProof.triangleVertex fs n t.val 1 ∈
    encodedCells fs n t by simp [encodedCells])
  have h2 := Coordinates.vertex_mem_simplex (show LinkProof.triangleVertex fs n t.val 2 ∈
    encodedCells fs n t by simp [encodedCells])
  exact (convex_convexHull ℝ _).segment_subset h0
    ((convex_convexHull ℝ _) h1 h2 (by norm_num) (by norm_num) (by norm_num))

theorem encodedCurve_subset_space (fs : Array Face) (n i : Nat) :
    encodedCurve fs n i ⊆ Coordinates.realization (encodedCells fs n) := by
  intro x hx
  obtain ⟨t,_,ht⟩ := mem_iUnion₂.mp hx
  exact mem_iUnion.mpr ⟨t, curve_arm_subset_triangle fs n t ht⟩

theorem encoded_space (fs : Array Face) (n : Nat) (hc : cornersCheck fs n = true) :
    Coordinates.reindex (Coordinates.labelEquiv n fs.size) '' (quadOfFaces fs).space =
      Coordinates.realization (encodedCells fs n) := by
  rw [← (quadOfFaces fs).realization_eq_space]
  simp only [Coordinates.realization, image_iUnion, Coordinates.reindex_simplex]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨t,rfl⟩ := triangleFaceCorner_surjective fs p
    exact ⟨t, by simpa only [cellLabels_encoded fs n hc] using hp⟩
  · rintro ⟨t,ht⟩
    exact ⟨(triangleFace fs t,triangleCorner fs t), by simpa only [cellLabels_encoded fs n hc] using ht⟩

def encodedSpaceHomeomorph (fs : Array Face) (n : Nat) (hc : cornersCheck fs n = true) :
    (quadOfFaces fs).Realization ≃ₜ Coordinates.realization (encodedCells fs n) :=
  ((Coordinates.reindex (Coordinates.labelEquiv n fs.size)).image _).trans
    (Homeomorph.setCongr (encoded_space fs n hc))

#print axioms encodedCurveHomeomorph
end Venn17.Topology
