import VennTopology.Realization
import VennCore.Incidence

noncomputable section
namespace Venn17.Topology

open Set Quad

def quadOfFaces (fs : Array Face) : Quad Nat (Fin fs.size) where
  corner f k := (fs[f.val]!)[k.val]!

theorem distinctCornersCheck_sound (fs : Array Face) (h : distinctCornersCheck fs = true)
    (f : Fin fs.size) : Function.Injective ((quadOfFaces fs).corner f) := by
  intro k l he
  have h := Array.all_eq_true.mp h f.val f.isLt
  have h := Array.all_eq_true.mp h k.val (by simp)
  have h := Array.all_eq_true.mp h l.val (by simp)
  simp only [Array.getElem_range, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h
  apply Fin.ext
  rcases h with h | h
  · exact h
  · exact False.elim (h (by simpa [quadOfFaces, f.isLt] using he))

theorem coverageCheck_sound (fs : Array Face) (n : Nat) (h : coverageCheck fs n = true)
    (v : Nat) (hv : v < n) :
    ∃ f k, (quadOfFaces fs).corner f k = v := by
  have h := Array.all_eq_true.mp h v (by simpa using hv)
  simp only [Array.getElem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  let d := (cornerDarts fs n)[v]!
  exact ⟨⟨d/4, h.1⟩, ⟨d%4, Nat.mod_lt _ (by decide)⟩, h.2⟩

theorem coverageCheck_mem_space (fs : Array Face) (n : Nat) (h : coverageCheck fs n = true)
    (v : Nat) (hv : v < n) : point (.inl v) ∈ (quadOfFaces fs).space := by
  obtain ⟨f, k, hk⟩ := coverageCheck_sound fs n h v hv
  rw [← hk]
  exact (quadOfFaces fs).triangle_subset_space f k ((quadOfFaces fs).corner_mem_triangle f k)

theorem cornersCheck_sound (fs : Array Face) (n : Nat) (h : cornersCheck fs n = true)
    (f : Fin fs.size) (k : Fin 4) : (quadOfFaces fs).corner f k < n := by
  have h := Array.all_eq_true.mp h f.val f.isLt
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hk : k.val < fs[f.val].size := by rw [h.1]; exact k.isLt
  have h := Array.all_eq_true.mp h.2 k.val hk
  simpa [quadOfFaces, f.isLt, hk] using h

theorem edgesCheck_sound (fs : Array Face) (g : Graph) (h : edgesCheck fs g = true)
    (u v : Nat) (hu : u < g.size) (hv : v ∈ g[u]!) :
    ∃ f k, (quadOfFaces fs).corner f k = u ∧
      (quadOfFaces fs).corner f (next k) = v := by
  have h := Array.all_eq_true.mp h u (by simpa using hu)
  simp only [Array.getElem_range] at h
  have h := Array.all_eq_true_iff_forall_mem.mp h v hv
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  let d := (directedDarts fs).getD (u,v) (4*fs.size)
  exact ⟨⟨d/4, h.1.1⟩, ⟨d%4, Nat.mod_lt _ (by decide)⟩, h.1.2, h.2⟩

/-- A soundness theorem connecting a finite certificate to continuous paths in
the actual geometric realization. No surface-classification premise is used. -/
theorem incidenceCheck_pathConnected (fs : Array Face) (g : Graph)
    (h : incidenceCheck fs g = true) : IsPathConnected (quadOfFaces fs).space := by
  simp only [incidenceCheck, Bool.and_eq_true] at h
  have hc := h.1.1.1
  have hv := h.1.1.2
  have he := h.1.2
  obtain ⟨root, hr, har, reach⟩ := GraphProof.connectedCheck_sound _ _ h.2
  let q := quadOfFaces fs
  have vertexMem (v : Nat) (hbound : v < g.size) : point (.inl v) ∈ q.space := by
    obtain ⟨f, k, hk⟩ := coverageCheck_sound fs g.size hv v hbound
    rw [← hk]
    exact q.triangle_subset_space f k (q.corner_mem_triangle f k)
  have edgeJoined (u v : Nat) (hu : decide (u < g.size) = true) (hh : v ∈ g[u]!) :
      JoinedIn q.space (point (.inl u)) (point (.inl v)) := by
    obtain ⟨f, k, hk, hl⟩ := edgesCheck_sound fs g he u v (of_decide_eq_true hu) hh
    rw [← hk, ← hl]
    exact q.adjacent_joined f k
  refine ⟨point (.inl root), vertexMem root hr, ?_⟩
  intro x hx
  obtain ⟨f, hp⟩ := q.point_joined_corner hx
  have hb := cornersCheck_sound fs g.size hc f 0
  have hw := reach (q.corner f 0) hb (by simpa using hb)
  have hj := walk_joined q.space g (fun v => v < g.size) (fun v => point (.inl v))
    (fun v h => vertexMem v (of_decide_eq_true h)) edgeJoined hw
  exact (hp.trans hj).symm

#print axioms incidenceCheck_pathConnected

end Venn17.Topology
