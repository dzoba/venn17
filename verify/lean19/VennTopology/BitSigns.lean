import VennTopology.CrossingCharts
import Mathlib.Data.Nat.Bitwise

noncomputable section
namespace Venn19.Topology
open Set

/-- Bit 0 has sign -1 and bit 1 has sign +1. -/
def bitSign (i v : Nat) : ℝ := if v.testBit i then 1 else -1

theorem bitSign_cases (i v : Nat) : bitSign i v = 1 ∨ bitSign i v = -1 := by
  unfold bitSign
  split <;> simp

theorem bitSign_sq (i v : Nat) : bitSign i v * bitSign i v = 1 := by
  rcases bitSign_cases i v with h | h <;> rw [h] <;> norm_num

theorem bitSign_flip {u v j : Nat} (h : u ^^^ v = 2^j) (i : Nat) :
    bitSign i v = if i = j then -bitSign i u else bitSign i u := by
  have hv : v = u ^^^ 2^j := by rw [← h,Nat.xor_xor_cancel_left]
  rw [hv]
  by_cases hi : i = j
  · subst i
    simp [bitSign]
    cases u.testBit j <;> norm_num
  · simp [bitSign,hi,Ne.symm hi]

theorem bitSign_same_iff {u v j : Nat} (h : u ^^^ v = 2^j) (i : Nat) :
    bitSign i u = bitSign i v ↔ i ≠ j := by
  rw [bitSign_flip h]
  split_ifs with hi
  · subst i
    rcases bitSign_cases j u with h | h <;> norm_num [h]
  · simp [hi]

namespace Quad
variable {F : Type*} (q : Quad Nat F)

def faceSign (i : Nat) (f : F) : ℝ :=
  (bitSign i (q.corner f 0) + bitSign i (q.corner f 1) +
    bitSign i (q.corner f 2) + bitSign i (q.corner f 3))/4

/-- A bit-square has either a constant sign, or a zero center value and an
edge on which that bit changes. This is a symbolic consequence of its labels. -/
theorem faceSign_cases (f : F) {a b : Nat} (hab : a ≠ b)
    (h01 : q.corner f 0 ^^^ q.corner f 1 = 2^a)
    (h12 : q.corner f 1 ^^^ q.corner f 2 = 2^b)
    (h23 : q.corner f 2 ^^^ q.corner f 3 = 2^a) (i : Nat) :
    (∀ k : Fin 4, bitSign i (q.corner f k) = q.faceSign i f) ∨
      (q.faceSign i f = 0 ∧ ∃ k : Fin 4, q.corner f k ^^^ q.corner f (next k) = 2^i) := by
  have h1 := bitSign_flip h01 i
  have h2 := bitSign_flip h12 i
  have h3 := bitSign_flip h23 i
  by_cases hi : i = a
  · subst i
    right
    refine ⟨?_,0,?_⟩
    · simp [hab] at h1 h2 h3
      unfold faceSign
      rw [h3,h2,h1]
      ring
    · exact h01
  · by_cases hj : i = b
    · subst i
      right
      refine ⟨?_,1,?_⟩
      · simp [Ne.symm hab] at h1 h2 h3
        unfold faceSign
        rw [h3,h2,h1]
        ring
      · exact h12
    · simp only [if_neg hi,if_neg hj] at h1 h2 h3
      left
      intro k
      unfold faceSign
      rw [h3,h2,h1]
      fin_cases k <;> simp_all <;> ring

end Quad

attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

theorem diagram_faceSign_cases (i : Fin 19) (f : Fin suppliedModel.oriented.size) :
    (∀ k : Fin 4, bitSign i.val (diagramQuad.corner f k) = diagramQuad.faceSign i.val f) ∨
      (diagramQuad.faceSign i.val f = 0 ∧ ∃ k : Fin 4,
        diagramQuad.corner f k ^^^ diagramQuad.corner f (Quad.next k) = 2^i.val) := by
  obtain ⟨a,b,hab,ha,hb⟩ := crossing_labels_alternate suppliedModel.oriented 524288 19
    supplied_curve_labels_verified supplied_crossing_labels_verified f
  exact diagramQuad.faceSign_cases f (fun h => hab (Fin.ext h))
    ((ha 0).mpr rfl) ((hb 1).mpr rfl) ((ha 2).mpr rfl) i.val

theorem diagram_edge_bitSign (f : Fin suppliedModel.oriented.size) (k : Fin 4) (i : Fin 19) :
    bitSign i.val (diagramQuad.corner f k) ≠ bitSign i.val (diagramQuad.corner f (Quad.next k)) ↔
      diagramQuad.corner f k ^^^ diagramQuad.corner f (Quad.next k) = 2^i.val := by
  let t : Fin (4*suppliedModel.oriented.size) := ⟨4*f.val+k.val,by have := f.isLt; omega⟩
  obtain ⟨j,hj⟩ := CurveProof.labelsCheck_sound _ _ _ supplied_curve_labels_verified t
  have hm : diagramQuad.corner f k ^^^ diagramQuad.corner f (Quad.next k) = 2^j.val := by
    apply (edgeMask_face _ 524288 f k).symm.trans
    simpa only [CurveProof.edgeMask,CurveProof.hasLabel,beq_iff_eq,t] using hj
  simp only [ne_eq,bitSign_same_iff hm i.val,not_not,hm,
    Nat.pow_right_inj (by decide : 1 < 2)]
  exact eq_comm

#print axioms diagram_faceSign_cases
end Venn19.Topology
