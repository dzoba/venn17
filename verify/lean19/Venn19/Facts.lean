import Venn19.GraphCertificate
import VennCore.Symmetry

namespace Venn19

/- Proof elaboration must not expand the 131,070-face input by kernel reduction.
Native computation still evaluates these ordinary definitions. -/
attribute [local irreducible] suppliedModel suppliedFaces


theorem region_graph_connected :
    GraphProof.ConnectedOn suppliedModel.graph (fun _ => true) := by
  apply GraphProof.connectedCheck_sound
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp graph_certificates_pass).1).1

theorem each_curve_connected (i : Nat) (hi : i < 19) :
    GraphProof.ConnectedOn suppliedModel.curves[i]!
      (curveActive suppliedModel.curves[i]!) := by
  apply GraphProof.connectedCheck_sound
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp graph_certificates_pass).1).2
  have h := Array.all_eq_true.mp h i (by simpa using hi)
  simp only [Array.getElem_range] at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem each_curve_degree_two (i f : Nat) (hi : i < 19)
    (hf : f < suppliedModel.curves[i]!.size)
    (ha : curveActive suppliedModel.curves[i]! f = true) :
    suppliedModel.curves[i]![f]!.size = 2 := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp graph_certificates_pass).1).2
  have h := Array.all_eq_true.mp h i (by simpa using hi)
  simp only [Array.getElem_range] at h
  exact GraphProof.degree_two _ f hf ha (Bool.and_eq_true_iff.mp h).2

theorem each_side_connected (i : Nat) (hi : i < 19) (side : Bool) :
    GraphProof.ConnectedOn suppliedModel.graph (sideActive i side) := by
  apply GraphProof.connectedCheck_sound
  have h := (Bool.and_eq_true_iff.mp graph_certificates_pass).2
  have h := Array.all_eq_true.mp h i (by simpa using hi)
  have h := Array.all_eq_true_iff_forall_mem.mp h side (by cases side <;> simp)
  simpa using h



def rotationWitnessCheck : Bool := rotationWitnessCheckFor suppliedModel.oriented

theorem rotation_witnesses_pass : rotationWitnessCheck = true := by
  native_decide

theorem rotation_preserves_oriented_crossings (f : Nat)
    (hf : f < suppliedModel.oriented.size) :
    ∃ g, g < suppliedModel.oriented.size ∧
      suppliedModel.oriented[g]! ∈ cyclicShifts (suppliedModel.oriented[f]!.map rotate) := by
  have h := Array.all_eq_true.mp rotation_witnesses_pass f (by simpa using hf)
  simp only [Array.getElem_range, Bool.and_eq_true, decide_eq_true_eq,
    Array.contains_iff_mem] at h
  exact ⟨(rotationWitnesses suppliedModel.oriented)[f]!, h⟩

#print axioms region_graph_connected
#print axioms each_curve_connected
#print axioms each_side_connected
#print axioms rotation_preserves_oriented_crossings

end Venn19
