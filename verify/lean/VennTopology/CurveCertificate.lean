import VennTopology.MidpointPolygon
import VennTopology.CurveData

namespace Venn17.CurveProof

/-- Both coordinates of each polygon vertex have the same certified owner. -/
theorem supportsCheck_sound (bound : Nat) (vs : Array PairVertex)
    (h : supportsCheck bound vs = true) (j : Fin vs.size) :
    let p := vs.getD j.val (0,0)
    p.1 < bound ∧ p.2 < bound ∧
      (supportOwners bound vs).getD p.1 vs.size = j.val ∧
      (supportOwners bound vs).getD p.2 vs.size = j.val := by
  have hj := Array.all_eq_true.mp h j.val (by simp)
  simpa only [Array.getElem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    and_assoc] using hj

theorem supportsCheck_disjoint (bound : Nat) (vs : Array PairVertex)
    (h : supportsCheck bound vs = true) :
    Topology.Coordinates.DisjointPairs (fun j : Fin vs.size => vs.getD j.val (0,0)) := by
  intro j k hne
  have hj := supportsCheck_sound bound vs h j
  have hk := supportsCheck_sound bound vs h k
  constructor
  · intro he
    apply hne
    apply Fin.ext
    exact hj.2.2.1.symm.trans ((congrArg (fun v => (supportOwners bound vs).getD v vs.size) he).trans hk.2.2.1)
  · intro he
    apply hne
    apply Fin.ext
    exact hj.2.2.1.symm.trans ((congrArg (fun v => (supportOwners bound vs).getD v vs.size) he).trans hk.2.2.2)

theorem polygonCheck_sound (fs : Array Face) (n i : Nat) (p : Polygon)
    (h : polygonCheck fs n i p = true) :
    3 ≤ p.vertices.size ∧ p.triangles.size = p.vertices.size ∧
      supportsCheck (n+fs.size) p.vertices = true ∧
      ∀ j : Fin p.vertices.size, edgeCheck fs n i p j.val = true := by
  simp only [polygonCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨h.1.1.1, h.1.1.2, h.1.2, ?_⟩
  intro j
  have hj := Array.all_eq_true.mp h.2 j.val (by simp)
  simpa only [Array.getElem_range] using hj

theorem edgeCheck_sound (fs : Array Face) (n i : Nat) (p : Polygon) (j : Nat)
    (h : edgeCheck fs n i p j = true) :
    let t := p.triangles.getD j (4*fs.size)
    t < 4*fs.size ∧ hasLabel fs n i t = true ∧
      ((p.vertices.getD j (0,0) = center fs n t ∧
        p.vertices.getD ((j+1)%p.vertices.size) (0,0) = ends fs n t) ∨
       (p.vertices.getD j (0,0) = ends fs n t ∧
        p.vertices.getD ((j+1)%p.vertices.size) (0,0) = center fs n t)) := by
  simpa only [edgeCheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, and_assoc] using h

theorem coverageCheck_sound (fs : Array Face) (n i : Nat) (p : Polygon)
    (h : coverageCheck fs n i p = true) (t : Fin (4*fs.size))
    (ht : hasLabel fs n i t.val = true) :
    ∃ j : Fin p.vertices.size, p.triangles.getD j.val (4*fs.size) = t.val := by
  have h := Array.all_eq_true.mp h t.val (by simp)
  simp only [Array.getElem_range, ht, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨⟨(trianglePositions fs p).getD t.val p.vertices.size, h.1⟩, h.2⟩

theorem labelsCheck_sound (fs : Array Face) (n count : Nat)
    (h : labelsCheck fs n count = true) (t : Fin (4*fs.size)) :
    ∃ i : Fin count, hasLabel fs n i.val t.val = true := by
  have ht := Array.all_eq_true.mp h t.val (by simp)
  simp only [Array.getElem_range] at ht
  obtain ⟨i,hi,he⟩ := Array.any_eq_true.mp ht
  exact ⟨⟨i, by simpa using hi⟩,by simpa only [Array.getElem_range] using he⟩

end Venn17.CurveProof

namespace Venn17.Topology
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons

theorem each_curve_polygon_verified (i : Fin 17) :
    CurveProof.check suppliedModel.oriented 131072 i.val
      (suppliedCurvePolygons.getD i.val default) = true ∧
    (suppliedCurvePolygons.getD i.val default).vertices.size = 30840 := by
  have h := Array.all_eq_true.mp supplied_curve_polygons_verified i.val (by simpa using i.isLt)
  simpa only [Array.getElem_range, Bool.and_eq_true, beq_iff_eq] using h

end Venn17.Topology
