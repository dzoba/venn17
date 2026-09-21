import VennTopology.DartIncidence
import VennTopology.SimplexCounting
import VennTopology.Regions

noncomputable section
namespace Venn19.Topology
open Set
open scoped Classical
local instance countsNatDecidableEq : DecidableEq Nat := Classical.decEq _

def dartEdgeEquiv (fs : Array Face) (n : Nat) (stars : LinkProof.Stars)
    (hr : LinkProof.rowsCheck fs n stars = true) (hc : LinkProof.coverageCheck fs n stars = true)
    (ht : ∀ t : Fin (4*fs.size), Function.Injective (fun j : Fin 3 => LinkProof.triangleVertex fs n t.val j.val)) :
    Fin (12*fs.size) ≃ CellDirectedEdge (encodedCells fs n) :=
  Equiv.ofBijective (fun d => ⟨(LinkProof.owner fs n d.val,LinkProof.tail fs n d.val),
    dart_owner_ne_tail fs n ht d,dart_vertices fs n d⟩) (by
    constructor
    · intro d e he
      exact dart_endpoints_injective fs n stars hr hc (congrArg Subtype.val he)
    · rintro ⟨⟨a,b⟩,hab,t,ha,hb⟩
      obtain ⟨d,ho,ht⟩ := triangle_pair_dart fs n stars hr hc t ha hb hab
      exact ⟨d,Subtype.ext (Prod.ext ho ht)⟩)

theorem encoded_edge_count (fs : Array Face) (n : Nat) (stars : LinkProof.Stars)
    (hr : LinkProof.rowsCheck fs n stars = true) (hc : LinkProof.coverageCheck fs n stars = true)
    (ht : ∀ t : Fin (4*fs.size), Function.Injective (fun j : Fin 3 => LinkProof.triangleVertex fs n t.val j.val)) :
    Nat.card (CellFace (encodedCells fs n) 2) = 6*fs.size := by
  have h := Nat.card_congr (dartEdgeEquiv fs n stars hr hc ht)
  rw [Nat.card_fin,directedEdge_card] at h
  omega

theorem encoded_cell_card (fs : Array Face) (n : Nat)
    (ht : ∀ t : Fin (4*fs.size), Function.Injective (fun j : Fin 3 => LinkProof.triangleVertex fs n t.val j.val))
    (t : Fin (4*fs.size)) : (encodedCells fs n t).card = 3 := by
  have h01 := (ht t).ne (by decide : (0 : Fin 3) ≠ 1)
  have h02 := (ht t).ne (by decide : (0 : Fin 3) ≠ 2)
  have h12 := (ht t).ne (by decide : (1 : Fin 3) ≠ 2)
  change LinkProof.triangleVertex fs n t.val 0 ≠ LinkProof.triangleVertex fs n t.val 1 at h01
  change LinkProof.triangleVertex fs n t.val 0 ≠ LinkProof.triangleVertex fs n t.val 2 at h02
  change LinkProof.triangleVertex fs n t.val 1 ≠ LinkProof.triangleVertex fs n t.val 2 at h12
  simp [encodedCells,h01,h02,h12]

theorem quad_next_next_ne (k : Fin 4) : Quad.next (Quad.next k) ≠ k := by decide +revert

theorem encoded_cells_injective (fs : Array Face) (n : Nat)
    (hc : cornersCheck fs n = true) (hd : distinctCornersCheck fs = true) :
    Function.Injective (encodedCells fs n) := by
  intro t u he
  obtain ⟨_,ht1,ht2,_,_,_⟩ := encodedTriangle_bounds fs n hc hd t
  obtain ⟨_,hu1,hu2,_,_,_⟩ := encodedTriangle_bounds fs n hc hd u
  have hm : LinkProof.triangleVertex fs n t.val 0 ∈ encodedCells fs n u := he ▸ (by simp [encodedCells])
  simp only [encodedCells,Finset.mem_insert,Finset.mem_singleton] at hm
  have hf : triangleFace fs t = triangleFace fs u := by
    rw [triangleVertex_zero] at hm
    rw [triangleVertex_zero] at hm
    apply Fin.ext
    rcases hm with hm | hm | hm <;> omega
  have hi := distinctCornersCheck_sound fs hd (triangleFace fs u)
  have hm1 : LinkProof.triangleVertex fs n t.val 1 ∈ encodedCells fs n u := he ▸ (by simp [encodedCells])
  have hm2 : LinkProof.triangleVertex fs n t.val 2 ∈ encodedCells fs n u := he ▸ (by simp [encodedCells])
  simp only [encodedCells,Finset.mem_insert,Finset.mem_singleton] at hm1 hm2
  have hu0 : n ≤ LinkProof.triangleVertex fs n u.val 0 := by rw [triangleVertex_zero]; omega
  have hm1' := hm1.resolve_left (by omega)
  have hm2' := hm2.resolve_left (by omega)
  simp only [triangleVertex_one,triangleVertex_two,hf] at hm1' hm2'
  have hk : triangleCorner fs t = triangleCorner fs u := by
    rcases hm1' with h | h
    · exact hi h
    · have h := hi h
      rcases hm2' with h2 | h2
      · exact False.elim (quad_next_next_ne (triangleCorner fs u) (by rw [← h]; exact hi h2))
      · exact False.elim (Quad.next_ne (triangleCorner fs t) ((hi h2).trans h.symm))
  have hfv := congrArg Fin.val hf
  have hkv := congrArg Fin.val hk
  apply Fin.ext
  dsimp [triangleFace,triangleCorner] at hfv hkv
  omega

theorem encoded_triangle_count (fs : Array Face) (n : Nat)
    (hc : cornersCheck fs n = true) (hd : distinctCornersCheck fs = true) :
    Nat.card (CellFace (encodedCells fs n) 3) = 4*fs.size := by
  have h := Nat.card_congr (topCellEquiv (encodedCells fs n) 3
    (encoded_cell_card fs n (triangleVertices_injective fs n hc hd)) (encoded_cells_injective fs n hc hd))
  simpa only [Nat.card_fin] using h.symm

theorem encoded_vertex_mem_iff (fs : Array Face) (n : Nat)
    (hc : cornersCheck fs n = true) (hcov : coverageCheck fs n = true) (v : Nat) :
    (∃ t : Fin (4*fs.size), v ∈ encodedCells fs n t) ↔ v < n+fs.size := by
  constructor
  · rintro ⟨t,ht⟩
    have h1 := cornersCheck_sound fs n hc (triangleFace fs t) (triangleCorner fs t)
    have h2 := cornersCheck_sound fs n hc (triangleFace fs t) (Quad.next (triangleCorner fs t))
    have h0 := (triangleFace fs t).isLt
    simp only [encodedCells,Finset.mem_insert,Finset.mem_singleton,
      triangleVertex_zero,triangleVertex_one,triangleVertex_two] at ht
    rcases ht with ht | ht | ht <;> omega
  · intro hv
    by_cases hn : v < n
    · obtain ⟨f,k,hk⟩ := coverageCheck_sound fs n hcov v hn
      obtain ⟨t,he⟩ := triangleFaceCorner_surjective fs (f,k)
      have hf := congrArg Prod.fst he
      have hc' := congrArg Prod.snd he
      dsimp only at hf hc'
      refine ⟨t,?_⟩
      have he : v = LinkProof.triangleVertex fs n t.val 1 := by rw [triangleVertex_one,hf,hc',hk]
      rw [he]; simp [encodedCells]
    · let f : Fin fs.size := ⟨v-n,by omega⟩
      obtain ⟨t,he⟩ := triangleFaceCorner_surjective fs (f,0)
      have hf := congrArg Prod.fst he
      dsimp only at hf
      refine ⟨t,?_⟩
      have he : v = LinkProof.triangleVertex fs n t.val 0 := by rw [triangleVertex_zero,hf]; dsimp [f]; omega
      rw [he]; simp [encodedCells]

def encodedVertexEquiv (fs : Array Face) (n : Nat)
    (hc : cornersCheck fs n = true) (hcov : coverageCheck fs n = true) :
    Fin (n+fs.size) ≃ CellFace (encodedCells fs n) 1 :=
  Equiv.ofBijective (fun v => ⟨{v.val},by simp,by
    obtain ⟨t,ht⟩ := (encoded_vertex_mem_iff fs n hc hcov v.val).mpr v.isLt
    exact ⟨t,by simpa using ht⟩⟩) (by
    constructor
    · intro v w he
      have he := congrArg Subtype.val he
      simpa only [Finset.singleton_inj,Fin.val_inj] using he
    · rintro ⟨s,hs,t,ht⟩
      obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hs
      have hv := (encoded_vertex_mem_iff fs n hc hcov v).mp ⟨t,ht (by simp)⟩
      exact ⟨⟨v,hv⟩,rfl⟩)

theorem encoded_vertex_count (fs : Array Face) (n : Nat)
    (hc : cornersCheck fs n = true) (hcov : coverageCheck fs n = true) :
    Nat.card (CellFace (encodedCells fs n) 1) = n+fs.size := by
  simpa only [Nat.card_fin] using (Nat.card_congr (encodedVertexEquiv fs n hc hcov)).symm

#print axioms encoded_edge_count
#print axioms encoded_triangle_count
#print axioms encoded_vertex_count
end Venn19.Topology
