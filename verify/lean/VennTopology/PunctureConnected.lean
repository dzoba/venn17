import Mathlib.Topology.Connected.LocallyPathConnected

namespace Venn17.Topology
open Set

/-- Deleting a point cannot disconnect a connected set when that point has
an open neighborhood whose puncture is preconnected. -/
theorem preconnected_diff_singleton_of_neighborhood {X : Type*}
    [TopologicalSpace X] [T1Space X] {s N : Set X} {p : X}
    (hs : IsPreconnected s) (hN : IsOpen N) (hp : p ∈ N)
    (hNs : N ⊆ s) (hpunct : IsPreconnected (N \ {p})) :
    IsPreconnected (s \ {p}) := by
  classical
  intro u v hu hv hcover hsu hsv
  by_contra hmeet
  have hnoint : ∀ x ∈ s, x ≠ p → x ∈ u → x ∈ v → False := by
    intro x hx hxp hxu hxv
    exact hmeet ⟨x,⟨hx,hxp⟩,hxu,hxv⟩
  have hcoverN : N \ {p} ⊆ u ∪ v := fun _ hx => hcover ⟨hNs hx.1,hx.2⟩
  have hone : N \ {p} ⊆ u ∨ N \ {p} ⊆ v := by
    by_cases hnu : ((N \ {p}) ∩ u).Nonempty
    · left
      intro x hx
      rcases hcoverN hx with hxu | hxv
      · exact hxu
      · obtain ⟨y,hy,hyu,hyv⟩ := hpunct u v hu hv hcoverN hnu ⟨x,hx,hxv⟩
        exact False.elim (hnoint y (hNs hy.1) hy.2 hyu hyv)
    · right
      intro x hx
      exact (hcoverN hx).resolve_left (fun hxu => hnu ⟨x,hx,hxu⟩)
  have impossible (a b : Set X) (ha : IsOpen a) (hb : IsOpen b)
      (hcov : s \ {p} ⊆ a ∪ b)
      (hsa : ((s \ {p}) ∩ a).Nonempty) (hsb : ((s \ {p}) ∩ b).Nonempty)
      (hno : ∀ x ∈ s, x ≠ p → x ∈ a → x ∈ b → False)
      (hNa : N \ {p} ⊆ a) : False := by
    obtain ⟨x,hxs,hxa,hxb⟩ := hs (a ∪ N) (b \ {p}) (ha.union hN)
      (hb.sdiff isClosed_singleton)
      (by
        intro x hx
        by_cases he : x = p
        · exact Or.inl (Or.inr (he ▸ hp))
        · rcases hcov ⟨hx,he⟩ with hxa | hxb
          · exact Or.inl (Or.inl hxa)
          · exact Or.inr ⟨hxb,he⟩)
      (by obtain ⟨x,hx,ha⟩ := hsa; exact ⟨x,hx.1,Or.inl ha⟩)
      (by obtain ⟨x,hx,hb⟩ := hsb; exact ⟨x,hx.1,hb,hx.2⟩)
    exact hno x hxs hxb.2 (hxa.elim id (fun hx => hNa ⟨hx,hxb.2⟩)) hxb.1
  rcases hone with hone | hone
  · exact impossible u v hu hv hcover hsu hsv hnoint hone
  · exact impossible v u hv hu (fun _ hx => (hcover hx).symm) hsv hsu
      (fun x hx hp hv hu => hnoint x hx hp hu hv) hone

#print axioms preconnected_diff_singleton_of_neighborhood
end Venn17.Topology
