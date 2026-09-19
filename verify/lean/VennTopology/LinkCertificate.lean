import VennCore.Links
import VennTopology.LinkData
import Mathlib.Data.List.Nodup

namespace Venn17.LinkProof

theorem rowCheck_sound (fs : Array Face) (n v : Nat) (row : Array Nat)
    (h : rowCheck fs n v row = true) :
    3 ≤ row.size ∧
    Function.Injective (fun k : Fin row.size => tail fs n (row.getD k.val 0)) ∧
    ∀ k : Fin row.size,
      row.getD k.val 0 < 12*fs.size ∧ owner fs n (row.getD k.val 0) = v ∧
      head fs n (row.getD k.val 0) = tail fs n (row.getD ((k.val+1)%row.size) 0) := by
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1, ?_, ?_⟩
  · intro k l he
    have hk : k.val < (row.map (tail fs n)).toList.length := by simp
    have hl : l.val < (row.map (tail fs n)).toList.length := by simp
    apply Fin.ext
    apply (List.Nodup.getElem_inj_iff h.1.2 (hi := hk) (hj := hl)).mp
    simpa [Array.getD, k.isLt, l.isLt] using he
  · intro k
    have hk := Array.all_eq_true.mp h.2 k.val (by simp)
    simpa only [Array.getElem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      and_assoc] using hk

theorem rowsCheck_sound (fs : Array Face) (n : Nat) (stars : Stars)
    (h : rowsCheck fs n stars = true) :
    stars.size = n+fs.size ∧ ∀ v : Fin stars.size,
      rowCheck fs n v.val (stars.getD v.val #[]) = true := by
  simp only [rowsCheck, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  intro v
  have hv := Array.all_eq_true.mp h.2 v.val (by simp)
  simpa only [Array.getElem_range] using hv

theorem coverageCheck_sound (fs : Array Face) (n : Nat) (stars : Stars)
    (h : coverageCheck fs n stars = true) (d : Fin (12*fs.size)) :
    owner fs n d.val < stars.size ∧
    ∃ k : Fin (stars.getD (owner fs n d.val) #[]).size,
      (stars.getD (owner fs n d.val) #[]).getD k.val 0 = d.val := by
  have h := Array.all_eq_true.mp h d.val (by simp)
  simp only [Array.getElem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1, ⟨⟨(positions fs stars).getD d.val 0, h.1.2⟩, h.2⟩⟩

end Venn17.LinkProof

namespace Venn17.Topology

attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars

theorem supplied_link_rows :
    suppliedLinkStars.size = 131072 + suppliedModel.oriented.size ∧
    ∀ v : Fin suppliedLinkStars.size,
      LinkProof.rowCheck suppliedModel.oriented 131072 v.val
        (suppliedLinkStars.getD v.val #[]) = true :=
  LinkProof.rowsCheck_sound _ _ _
    (Bool.and_eq_true_iff.mp supplied_link_stars_verified).1

/-- Every link is explicitly enumerated once, in cyclic order, with at least
three distinct neighbors. The enumerated darts refer to actual input triangles. -/
theorem every_link_has_cyclic_order (v : Fin suppliedLinkStars.size) :
    let row := suppliedLinkStars.getD v.val #[]
    3 ≤ row.size ∧
    Function.Injective (fun k : Fin row.size => LinkProof.tail suppliedModel.oriented 131072
      (row.getD k.val 0)) ∧
    ∀ k : Fin row.size,
      row.getD k.val 0 < 12*suppliedModel.oriented.size ∧
      LinkProof.owner suppliedModel.oriented 131072 (row.getD k.val 0) = v.val ∧
      LinkProof.head suppliedModel.oriented 131072 (row.getD k.val 0) =
        LinkProof.tail suppliedModel.oriented 131072 (row.getD ((k.val+1)%row.size) 0) :=
  LinkProof.rowCheck_sound _ _ _ _ (supplied_link_rows.2 v)

/-- No incident triangle is omitted from the cyclic enumeration. -/
theorem every_triangle_dart_occurs (d : Fin (12*suppliedModel.oriented.size)) :
    LinkProof.owner suppliedModel.oriented 131072 d.val < suppliedLinkStars.size ∧
    ∃ k : Fin (suppliedLinkStars.getD (LinkProof.owner suppliedModel.oriented 131072 d.val) #[]).size,
      (suppliedLinkStars.getD (LinkProof.owner suppliedModel.oriented 131072 d.val) #[]).getD k.val 0 =
        d.val :=
  LinkProof.coverageCheck_sound _ _ _
    (Bool.and_eq_true_iff.mp supplied_link_stars_verified).2 d

#print axioms every_link_has_cyclic_order
#print axioms every_triangle_dart_occurs

end Venn17.Topology
