import VennTopology.CurveSides

noncomputable section
namespace Venn17.Topology
open Set
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

theorem diagramSide_isOpen (i : Fin 17) (b : Bool) : IsOpen (diagramSide i b) :=
  isOpen_lt continuous_const (continuous_const.mul (diagramBitField_continuous i))

theorem diagramSide_subset_complement (i : Fin 17) (b : Bool) :
    diagramSide i b ⊆ (diagramCurve i)ᶜ := by
  intro x hx hc
  have hz := (diagram_curve_iff_field_zero i x).mp hc
  change 0 < sideSign b * diagramBitField i x at hx
  rw [hz,mul_zero] at hx
  exact lt_irrefl _ hx

theorem diagramSide_disjoint (i : Fin 17) : Disjoint (diagramSide i false) (diagramSide i true) := by
  rw [Set.disjoint_left]
  intro x hx hy
  change 0 < sideSign false * diagramBitField i x at hx
  change 0 < sideSign true * diagramBitField i x at hy
  norm_num [sideSign] at hx hy
  linarith

theorem diagramSide_cover (i : Fin 17) : (⋃ b : Bool, diagramSide i b) = (diagramCurve i)ᶜ := by
  ext x
  constructor
  · intro hx; obtain ⟨b,hb⟩ := mem_iUnion.mp hx
    exact diagramSide_subset_complement i b hb
  · intro hx
    have hn : diagramBitField i x ≠ 0 := fun h => hx ((diagram_curve_iff_field_zero i x).mpr h)
    rcases lt_or_gt_of_ne hn with h | h
    · refine mem_iUnion.mpr ⟨false,?_⟩
      change 0 < sideSign false * diagramBitField i x
      simpa [sideSign] using h
    · refine mem_iUnion.mpr ⟨true,?_⟩
      change 0 < sideSign true * diagramBitField i x
      simpa [sideSign] using h

def diagramCurveComplement (i : Fin 17) : Set Diagram := (diagramCurve i)ᶜ

def curveComplementSide (i : Fin 17) (b : Bool) : Set (diagramCurveComplement i) :=
  Subtype.val ⁻¹' diagramSide i b

theorem curveComplementSide_isOpen (i : Fin 17) (b : Bool) : IsOpen (curveComplementSide i b) :=
  (diagramSide_isOpen i b).preimage continuous_subtype_val

theorem curveComplementSide_pairwise (i : Fin 17) :
    Pairwise (Function.onFun Disjoint (curveComplementSide i)) := by
  intro b c hbc
  cases b <;> cases c
  · exact False.elim (hbc rfl)
  · exact (diagramSide_disjoint i).preimage Subtype.val
  · exact (diagramSide_disjoint i).symm.preimage Subtype.val
  · exact False.elim (hbc rfl)

theorem curveComplementSide_cover (i : Fin 17) : (⋃ b, curveComplementSide i b) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x.val ∈ ⋃ b, diagramSide i b := by rw [diagramSide_cover]; exact x.property
  obtain ⟨b,hb⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨b,hb⟩

theorem curveComplementSide_isClopen (i : Fin 17) (b : Bool) : IsClopen (curveComplementSide i b) := by
  have he : (curveComplementSide i b)ᶜ = curveComplementSide i (!b) := by
    ext x
    have hc := mem_iUnion.mp (show x ∈ ⋃ c, curveComplementSide i c by rw [curveComplementSide_cover]; trivial)
    have hd := Set.disjoint_left.mp (curveComplementSide_pairwise i (show b ≠ !b by cases b <;> decide))
    constructor
    · intro hx
      obtain ⟨c,hc⟩ := hc
      cases b <;> cases c <;> simp_all
    · exact fun hx hy => hd hy hx
  exact ⟨isOpen_compl_iff.mp (he ▸ curveComplementSide_isOpen i (!b)),curveComplementSide_isOpen i b⟩

theorem curveComplementSide_pathConnected (i : Fin 17) (b : Bool) :
    IsPathConnected (curveComplementSide i b) :=
  (diagramSide_pathConnected i b).preimage_coe (diagramSide_subset_complement i b)

/-- The complement of each individual circle has exactly the two geometric
sides certified by the finite bit data. -/
def diagramSideComponentsEquiv (i : Fin 17) : ConnectedComponents (diagramCurveComplement i) ≃ Bool :=
  ConnectedComponents.equivOfIsClopenOfIsConnected (curveComplementSide_isClopen i)
    (curveComplementSide_pairwise i) (curveComplementSide_cover i)
    (fun b => (curveComplementSide_pathConnected i b).isConnected)

theorem diagram_curve_complement_component_count (i : Fin 17) :
    Nat.card (ConnectedComponents (diagramCurveComplement i)) = 2 := by
  rw [Nat.card_congr (diagramSideComponentsEquiv i)]
  simp

theorem diagram_region_side_iff (i : Fin 17) (v : Fin 131072) (b : Bool)
    {x : Diagram} (hx : x ∈ diagramRegion v) :
    x ∈ diagramSide i b ↔ v.val.testBit i.val = b := by
  have h := diagram_region_field_sign i v hx
  change 0 < sideSign b * diagramBitField i x ↔ _
  unfold bitSign at h
  cases b <;> cases hb : v.val.testBit i.val <;>
    norm_num [sideSign,hb] at h ⊢
  all_goals linarith

theorem pattern_eq_of_bits {u v : Fin 131072}
    (h : ∀ i : Fin 17, u.val.testBit i.val = v.val.testBit i.val) : u = v := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 17
  · exact h ⟨i,hi⟩
  · have hp : 131072 ≤ 2^i := by
      calc
        131072 = 2^17 := by norm_num
        _ ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le u.isLt hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le v.isLt hp)]

/-- Regions are exactly the intersections specified by their 17 geometric
side choices, not merely sets containing correctly labelled vertices. -/
theorem diagramRegion_eq_sides (v : Fin 131072) :
    diagramRegion v = ⋂ i : Fin 17, diagramSide i (v.val.testBit i.val) := by
  ext x
  constructor
  · intro hx
    exact mem_iInter.mpr (fun i => (diagram_region_side_iff i v _ hx).mpr rfl)
  · intro hx
    have hs := mem_iInter.mp hx
    have hc : x ∉ ⋃ i : Fin 17, diagramCurve i := by
      intro hc
      obtain ⟨i,hi⟩ := mem_iUnion.mp hc
      exact diagramSide_subset_complement i _ (hs i) hi
    obtain ⟨w,hw,_⟩ := (diagram_complement_unique_region x).mp hc
    have he : w = v := pattern_eq_of_bits (fun i => (diagram_region_side_iff i w _ hw).mp (hs i))
    exact he ▸ hw

/-- Both sides are nonempty and path connected; all points in every region
have precisely the bits of that region's index. Boundedness requires a plane
homeomorphism and is not asserted here. -/
theorem diagram_sides_verified (i : Fin 17) :
    (∀ b, IsOpen (diagramSide i b) ∧ IsPathConnected (diagramSide i b)) ∧
    Disjoint (diagramSide i false) (diagramSide i true) ∧
    (⋃ b, diagramSide i b) = (diagramCurve i)ᶜ ∧
    Nat.card (ConnectedComponents (diagramCurveComplement i)) = 2 ∧
    (∀ v : Fin 131072, ∀ b : Bool, ∀ x ∈ diagramRegion v,
      x ∈ diagramSide i b ↔ v.val.testBit i.val = b) :=
  ⟨fun b => ⟨diagramSide_isOpen i b,diagramSide_pathConnected i b⟩,
    diagramSide_disjoint i,diagramSide_cover i,diagram_curve_complement_component_count i,
    fun v b _ hx => diagram_region_side_iff i v b hx⟩

#print axioms diagram_sides_verified
#print axioms diagramRegion_eq_sides
end Venn17.Topology
