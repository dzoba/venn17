import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Subtype

noncomputable section
namespace Venn17.Topology
open Set

/-- Faces with exactly `k` vertices in a finite family of simplices. -/
def CellFace {T A : Type*} (cells : T → Finset A) (k : Nat) :=
  {s : Finset A // s.card = k ∧ ∃ t, s ⊆ cells t}

instance cellFace_finite {T A : Type*} [Finite T] (cells : T → Finset A) (k : Nat) :
    Finite (CellFace cells k) := by
  classical
  apply Set.Finite.to_subtype
  apply (Set.finite_iUnion (fun t : T => (cells t).powerset.finite_toSet)).subset
  rintro s ⟨_,t,ht⟩
  exact mem_iUnion.mpr ⟨t,Finset.mem_powerset.mpr ht⟩

def CellDirectedEdge {T A : Type*} (cells : T → Finset A) :=
  {p : A × A // p.1 ≠ p.2 ∧ ∃ t, p.1 ∈ cells t ∧ p.2 ∈ cells t}

def directedEdgeFlag {T A : Type*} (cells : T → Finset A) (d : CellDirectedEdge cells) :
    Σ e : CellFace cells 2, {a // a ∈ e.val} := by
  classical
  refine ⟨⟨{d.val.1,d.val.2},by simp [d.property.1],?_⟩,⟨d.val.1,by simp⟩⟩
  obtain ⟨t,ha,hb⟩ := d.property.2
  refine ⟨t,?_⟩
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  exact hx.elim (fun h => h ▸ ha) (fun h => h ▸ hb)

theorem directedEdgeFlag_bijective {T A : Type*} (cells : T → Finset A) :
    Function.Bijective (directedEdgeFlag cells) := by
  classical
  constructor
  · intro d e he
    have ha : d.val.1 = e.val.1 := congrArg (fun z => z.2.val) he
    have hs : ({d.val.1,d.val.2} : Finset A) = {e.val.1,e.val.2} :=
      congrArg (fun z => z.1.val) he
    apply Subtype.ext
    apply Prod.ext ha
    have hb : d.val.2 ∈ ({e.val.1,e.val.2} : Finset A) := hs ▸ (by simp)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hb
    exact hb.resolve_left (fun h => d.property.1 (ha.trans h.symm))
  · rintro ⟨e,a⟩
    obtain ⟨u,v,huv,he⟩ := Finset.card_eq_two.mp e.property.1
    have ha : a.val = u ∨ a.val = v := by simpa only [he,Finset.mem_insert,Finset.mem_singleton] using a.property
    have make (b : A) (hne : a.val ≠ b) (hs : e.val = {a.val,b}) :
        ∃ d, directedEdgeFlag cells d = ⟨e,a⟩ := by
      obtain ⟨t,ht⟩ := e.property.2
      have hb : b ∈ e.val := hs.symm ▸ (by simp : b ∈ ({a.val,b} : Finset A))
      let d : CellDirectedEdge cells := ⟨(a.val,b),hne,t,ht a.property,ht hb⟩
      refine ⟨d,?_⟩
      apply Sigma.ext
      · exact Subtype.ext hs.symm
      · exact (Subtype.heq_iff_coe_eq
          (p := fun x => x ∈ ({a.val,b} : Finset A)) (q := fun x => x ∈ e.val)
          (fun x => Iff.of_eq (congrArg (fun s : Finset A => x ∈ s) hs.symm))).mpr rfl
    rcases ha with ha | ha
    · exact make v (by simpa only [ha] using huv) (by simpa only [ha] using he)
    · exact make u (by simpa only [ha] using huv.symm) (by simpa only [ha,Finset.pair_comm] using he)

def directedEdgeFlagEquiv {T A : Type*} (cells : T → Finset A) :
    CellDirectedEdge cells ≃ Σ e : CellFace cells 2, {a // a ∈ e.val} :=
  Equiv.ofBijective (directedEdgeFlag cells) (directedEdgeFlag_bijective cells)

theorem directedEdge_card {T A : Type*} [Finite T] (cells : T → Finset A) :
    Nat.card (CellDirectedEdge cells) = 2 * Nat.card (CellFace cells 2) := by
  classical
  letI : Fintype (CellFace cells 2) := Fintype.ofFinite _
  rw [Nat.card_congr (directedEdgeFlagEquiv cells),Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card,Fintype.card_coe]
  simp only [show ∀ e : CellFace cells 2, e.val.card = 2 from fun e => e.property.1]
  simp [Nat.mul_comm]

/-- Top-dimensional faces are exactly the original cells when all cells have
the same size and none is duplicated. -/
def topCellEquiv {T A : Type*} (cells : T → Finset A) (k : Nat)
    (hc : ∀ t, (cells t).card = k) (hi : Function.Injective cells) : T ≃ CellFace cells k :=
  Equiv.ofBijective (fun t => ⟨cells t,hc t,t,Finset.Subset.refl _⟩) (by
    constructor
    · intro t u h; exact hi (congrArg Subtype.val h)
    · rintro ⟨s,hs,t,ht⟩
      exact ⟨t,Subtype.ext (Finset.eq_of_subset_of_card_le ht (by rw [hc t,hs])).symm⟩)

/-- Injectively relabelling vertices preserves the actual face sets. -/
def cellFaceMapEquiv {T A B : Type*} (cells : T → Finset A) (f : A ↪ B) (k : Nat) :
    CellFace cells k ≃ CellFace (fun t => (cells t).map f) k :=
  Equiv.ofBijective (fun s => ⟨s.val.map f,by simpa using s.property.1,by
    obtain ⟨t,ht⟩ := s.property.2
    exact ⟨t,Finset.map_subset_map.mpr ht⟩⟩) (by
    classical
    constructor
    · intro s t h
      exact Subtype.ext (Finset.map_injective f (congrArg Subtype.val h))
    · rintro ⟨s,hcard,t,ht⟩
      let r := (cells t).filter (fun a => f a ∈ s)
      have he : r.map f = s := by
        ext b
        constructor
        · intro hb
          obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hb
          exact (Finset.mem_filter.mp ha).2
        · intro hb
          obtain ⟨a,ha,he⟩ := Finset.mem_map.mp (ht hb)
          exact Finset.mem_map.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,he ▸ hb⟩,he⟩
      refine ⟨⟨r,?_,t,Finset.filter_subset _ _⟩,Subtype.ext he⟩
      rw [← Finset.card_map f,he,hcard])

def cellFaceCongr {T U A : Type*} (cells : T → Finset A) (other : U → Finset A) (k : Nat)
    (h : ∀ s : Finset A, (∃ t, s ⊆ cells t) ↔ ∃ u, s ⊆ other u) :
    CellFace cells k ≃ CellFace other k :=
  Equiv.subtypeEquivRight (fun s => and_congr_right (fun _ => h s))

#print axioms directedEdge_card
#print axioms topCellEquiv
end Venn17.Topology
