import VennTopology.GeometricLinks

noncomputable section
namespace Venn17.Topology
open Set

theorem dart_endpoints_injective (fs : Array Face) (n : Nat) (stars : LinkProof.Stars)
    (hr : LinkProof.rowsCheck fs n stars = true) (hc : LinkProof.coverageCheck fs n stars = true) :
    Function.Injective (fun d : Fin (12*fs.size) => (LinkProof.owner fs n d.val,LinkProof.tail fs n d.val)) := by
  intro d e he
  have ho := congrArg Prod.fst he
  have ht := congrArg Prod.snd he
  obtain ⟨hd,k,hk⟩ := LinkProof.coverageCheck_sound fs n stars hc d
  dsimp only at ho ht
  have hecov := (LinkProof.coverageCheck_sound fs n stars hc e).2
  have hlex : ∃ l : Fin (stars.getD (LinkProof.owner fs n d.val) #[]).size,
      (stars.getD (LinkProof.owner fs n d.val) #[]).getD l.val 0 = e.val := by
    exact Eq.mp (congrArg (fun v => ∃ l : Fin (stars.getD v #[]).size,
      (stars.getD v #[]).getD l.val 0 = e.val) ho.symm) hecov
  obtain ⟨l,hl⟩ := hlex
  have hinj := (LinkProof.rowCheck_sound fs n _ _
    ((LinkProof.rowsCheck_sound fs n stars hr).2 ⟨_,hd⟩)).2.1
  have hkl : k = l := hinj (by
    change LinkProof.tail fs n ((stars.getD (LinkProof.owner fs n d.val) #[]).getD k.val 0) =
      LinkProof.tail fs n ((stars.getD (LinkProof.owner fs n d.val) #[]).getD l.val 0)
    rw [hk,hl]; exact ht)
  apply Fin.ext
  exact hk.symm.trans ((congrArg (fun j => (stars.getD (LinkProof.owner fs n d.val) #[]).getD j.val 0) hkl).trans hl)

theorem dart_head_is_tail (fs : Array Face) (n : Nat) (stars : LinkProof.Stars)
    (hr : LinkProof.rowsCheck fs n stars = true) (hc : LinkProof.coverageCheck fs n stars = true)
    (d : Fin (12*fs.size)) : ∃ e : Fin (12*fs.size),
      LinkProof.owner fs n e.val = LinkProof.owner fs n d.val ∧
      LinkProof.tail fs n e.val = LinkProof.head fs n d.val := by
  obtain ⟨hd,k,hk⟩ := LinkProof.coverageCheck_sound fs n stars hc d
  let row := stars.getD (LinkProof.owner fs n d.val) #[]
  have hrow := LinkProof.rowCheck_sound fs n _ _ ((LinkProof.rowsCheck_sound fs n stars hr).2 ⟨_,hd⟩)
  have hsize : 3 ≤ row.size := hrow.1
  let l : Fin row.size := ⟨(k.val+1)%row.size,Nat.mod_lt _ (by omega)⟩
  refine ⟨⟨row.getD l.val 0,(hrow.2.2 l).1⟩,(hrow.2.2 l).2.1,?_⟩
  exact ((hrow.2.2 k).2.2.trans (by rfl)).symm.trans (congrArg (LinkProof.head fs n) hk)

theorem dart_reverse_exists (fs : Array Face) (n : Nat) (stars : LinkProof.Stars)
    (hr : LinkProof.rowsCheck fs n stars = true) (hc : LinkProof.coverageCheck fs n stars = true)
    (d : Fin (12*fs.size)) : ∃ e : Fin (12*fs.size),
      LinkProof.owner fs n e.val = LinkProof.tail fs n d.val ∧
      LinkProof.tail fs n e.val = LinkProof.owner fs n d.val := by
  obtain ⟨t,j,rfl⟩ := triangleDart_surjective fs d
  let j' : Fin 3 := ⟨(j.val+1)%3,Nat.mod_lt _ (by decide)⟩
  obtain ⟨e,ho,ht⟩ := dart_head_is_tail fs n stars hr hc (triangleDart fs t j')
  refine ⟨e,ho.trans ?_,ht.trans ?_⟩
  · rw [triangleDart_owner,triangleDart_tail]
  · rw [triangleDart_head,triangleDart_owner]
    congr 1
    dsimp [j']
    have := j.isLt
    omega

theorem dart_vertices (fs : Array Face) (n : Nat) (d : Fin (12*fs.size)) :
    ∃ t : Fin (4*fs.size), LinkProof.owner fs n d.val ∈ encodedCells fs n t ∧
      LinkProof.tail fs n d.val ∈ encodedCells fs n t := by
  obtain ⟨t,j,rfl⟩ := triangleDart_surjective fs d
  refine ⟨t,?_⟩
  rw [triangleDart_owner,triangleDart_tail]
  fin_cases j <;> simp [encodedCells]

theorem dart_owner_ne_tail (fs : Array Face) (n : Nat)
    (ht : ∀ t : Fin (4*fs.size), Function.Injective (fun j : Fin 3 => LinkProof.triangleVertex fs n t.val j.val))
    (d : Fin (12*fs.size)) : LinkProof.owner fs n d.val ≠ LinkProof.tail fs n d.val := by
  obtain ⟨t,j,rfl⟩ := triangleDart_surjective fs d
  rw [triangleDart_owner,triangleDart_tail]
  intro he
  have hj := ht t (a₁ := j) (a₂ := ⟨(j.val+1)%3,by omega⟩) he
  have := congrArg Fin.val hj
  change j.val = (j.val+1)%3 at this
  have := j.isLt
  omega

/-- Every ordered pair of distinct vertices in one triangle occurs as the
owner and tail of a certified dart, including the reversed orientations. -/
theorem triangle_pair_dart (fs : Array Face) (n : Nat) (stars : LinkProof.Stars)
    (hr : LinkProof.rowsCheck fs n stars = true) (hc : LinkProof.coverageCheck fs n stars = true)
    (t : Fin (4*fs.size)) {a b : Nat} (ha : a ∈ encodedCells fs n t)
    (hb : b ∈ encodedCells fs n t) (hab : a ≠ b) :
    ∃ d : Fin (12*fs.size), LinkProof.owner fs n d.val = a ∧ LinkProof.tail fs n d.val = b := by
  have hf (j : Fin 3) : ∃ d : Fin (12*fs.size),
      LinkProof.owner fs n d.val = LinkProof.triangleVertex fs n t.val j.val ∧
      LinkProof.tail fs n d.val = LinkProof.triangleVertex fs n t.val ((j.val+1)%3) :=
    ⟨triangleDart fs t j,triangleDart_owner fs n t j,triangleDart_tail fs n t j⟩
  have hb' (j : Fin 3) : ∃ d : Fin (12*fs.size),
      LinkProof.owner fs n d.val = LinkProof.triangleVertex fs n t.val ((j.val+1)%3) ∧
      LinkProof.tail fs n d.val = LinkProof.triangleVertex fs n t.val j.val := by
    obtain ⟨d,ho,ht⟩ := dart_reverse_exists fs n stars hr hc (triangleDart fs t j)
    exact ⟨d,ho.trans (triangleDart_tail fs n t j),ht.trans (triangleDart_owner fs n t j)⟩
  simp only [encodedCells,Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals first | exact False.elim (hab rfl) | exact hf 0 | exact hf 1 | exact hf 2 | exact hb' 0 | exact hb' 1 | exact hb' 2

#print axioms dart_endpoints_injective
#print axioms triangle_pair_dart
end Venn17.Topology
