import VennTopology.PolygonVertices
import ClassificationOfSurfaces.FiniteCyclicCanonical

noncomputable section
namespace Venn17.Topology.PolygonVertices
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex NormalForm

def typedEndpoint {E : Type} [Fintype E] (w : List (SignedDart E)) (d : SignedDart E) :
    Vertex (ofOneFaceWord w) := endpoint _ (SignedDart.mapEquiv (Fintype.equivFin E) d)

theorem typedEndpoint_surjective {E : Type} [Fintype E] (w : List (SignedDart E)) :
    Function.Surjective (typedEndpoint w) := by
  intro x
  refine Quot.inductionOn x (fun d => ?_)
  obtain ⟨a, rfl⟩ := (SignedDart.mapEquiv (Fintype.equivFin E)).surjective d
  exact ⟨a, rfl⟩

theorem typed_corner_eq {E : Type} [Fintype E] (w : List (SignedDart E))
    (i j : Fin w.length) (h : i.val + 1 = j.val) :
    typedEndpoint w (w.get i).flip = typedEndpoint w (w.get j) := by
  apply Quot.sound
  let o : (ofOneFaceWord w).BoundaryOccurrence :=
    ⟨0, ⟨i.val, by simp [ofOneFaceWord_boundary_zero]⟩⟩
  refine ⟨o, ?_, ?_⟩
  · simp only [o, FiniteCyclicPresentation.BoundaryOccurrence.dart, ofOneFaceWord_boundary_zero,
      List.get_eq_getElem, List.getElem_map,
      SignedDart.mapEquiv_flip]
  · simp only [o, next, FiniteCyclicPresentation.BoundaryOccurrence.dart, ofOneFaceWord_boundary_zero,
      List.length_map, List.get_eq_getElem, List.getElem_map]
    congr 2
    rw [h, Nat.mod_eq_of_lt j.isLt]

theorem orientable_block_vertices (p : Nat) (i : Fin p) :
    typedEndpoint (orientableBoundaryWord p 0) (.neg (.a i)) =
      typedEndpoint (orientableBoundaryWord p 0) (.pos (.a i)) ∧
    typedEndpoint (orientableBoundaryWord p 0) (.pos (.b i)) =
      typedEndpoint (orientableBoundaryWord p 0) (.pos (.a i)) ∧
    typedEndpoint (orientableBoundaryWord p 0) (.neg (.b i)) =
      typedEndpoint (orientableBoundaryWord p 0) (.pos (.a i)) := by
  have h01 := typed_corner_eq (orientableBoundaryWord p 0)
    (orientableHandlePosition p 0 i 0) (orientableHandlePosition p 0 i 1) (by rfl)
  have h12 := typed_corner_eq (orientableBoundaryWord p 0)
    (orientableHandlePosition p 0 i 1) (orientableHandlePosition p 0 i 2) (by simp [orientableHandlePosition])
  have h23 := typed_corner_eq (orientableBoundaryWord p 0)
    (orientableHandlePosition p 0 i 2) (orientableHandlePosition p 0 i 3) (by simp [orientableHandlePosition])
  simp only [orientableBoundaryWord_get_handle_a_pos, orientableBoundaryWord_get_handle_a_neg,
    orientableBoundaryWord_get_handle_b_pos, orientableBoundaryWord_get_handle_b_neg,
    SignedDart.flip] at h01 h12 h23
  exact ⟨h12.symm.trans h23.symm, h01.symm.trans (h12.symm.trans h23.symm), h23.symm⟩

theorem orientable_neighbor_vertices (p : Nat) (i j : Fin p) (h : i.val + 1 = j.val) :
    typedEndpoint (orientableBoundaryWord p 0) (.pos (.a i)) =
      typedEndpoint (orientableBoundaryWord p 0) (.pos (.a j)) := by
  have hn := typed_corner_eq (orientableBoundaryWord p 0)
    (orientableHandlePosition p 0 i 3) (orientableHandlePosition p 0 j 0) (by
      simp only [orientableHandlePosition_val, Fin.val_zero]
      omega)
  simp only [orientableBoundaryWord_get_handle_b_neg, orientableBoundaryWord_get_handle_a_pos,
    SignedDart.flip] at hn
  exact (orientable_block_vertices p i).2.1.symm.trans hn

theorem orientable_vertex_count (p : Nat) (hp : 0 < p) :
    Nat.card (Vertex (NormalForm.orientable p 0).canonicalPresentation) = 1 := by
  let z : Fin p := ⟨0, hp⟩
  let x := typedEndpoint (orientableBoundaryWord p 0) (.pos (.a z))
  have hbase (i : Fin p) : typedEndpoint (orientableBoundaryWord p 0) (.pos (.a i)) = x := by
    obtain ⟨i, hi⟩ := i
    induction i with
    | zero => rfl
    | succ i ih =>
        exact (orientable_neighbor_vertices p ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl).symm.trans (ih (by omega))
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨x, ?_⟩
  intro y
  obtain ⟨d, rfl⟩ := typedEndpoint_surjective (orientableBoundaryWord p 0) y
  cases d with
  | pos e =>
      cases e with
      | a i => exact hbase i
      | b i => exact (orientable_block_vertices p i).2.1.trans (hbase i)
      | c i => exact Fin.elim0 i
      | h i => exact Fin.elim0 i
  | neg e =>
      cases e with
      | a i => exact (orientable_block_vertices p i).1.trans (hbase i)
      | b i => exact (orientable_block_vertices p i).2.2.trans (hbase i)
      | c i => exact Fin.elim0 i
      | h i => exact Fin.elim0 i

theorem nonOrientable_block_vertices (p : Nat) (i : Fin p) :
    typedEndpoint (nonOrientableBoundaryWord p 0) (.neg (.a i)) =
      typedEndpoint (nonOrientableBoundaryWord p 0) (.pos (.a i)) := by
  have h := typed_corner_eq (nonOrientableBoundaryWord p 0)
    (nonOrientableCrosscapPosition p 0 i 0) (nonOrientableCrosscapPosition p 0 i 1) (by rfl)
  rw [nonOrientableBoundaryWord_get_crosscap_block, nonOrientableBoundaryWord_get_crosscap_block] at h
  exact h

theorem nonOrientable_neighbor_vertices (p : Nat) (i j : Fin p) (h : i.val + 1 = j.val) :
    typedEndpoint (nonOrientableBoundaryWord p 0) (.pos (.a i)) =
      typedEndpoint (nonOrientableBoundaryWord p 0) (.pos (.a j)) := by
  have hn := typed_corner_eq (nonOrientableBoundaryWord p 0)
    (nonOrientableCrosscapPosition p 0 i 1) (nonOrientableCrosscapPosition p 0 j 0) (by
      simp only [nonOrientableCrosscapPosition_val, Fin.val_zero]
      omega)
  rw [nonOrientableBoundaryWord_get_crosscap_block, nonOrientableBoundaryWord_get_crosscap_block] at hn
  exact (nonOrientable_block_vertices p i).symm.trans hn

theorem nonOrientable_vertex_count (p : Nat) (hp : 0 < p) :
    Nat.card (Vertex (NormalForm.nonOrientable p 0).canonicalPresentation) = 1 := by
  let z : Fin p := ⟨0, hp⟩
  let x := typedEndpoint (nonOrientableBoundaryWord p 0) (.pos (.a z))
  have hbase (i : Fin p) : typedEndpoint (nonOrientableBoundaryWord p 0) (.pos (.a i)) = x := by
    obtain ⟨i, hi⟩ := i
    induction i with
    | zero => rfl
    | succ i ih =>
        exact (nonOrientable_neighbor_vertices p ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl).symm.trans (ih (by omega))
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨x, ?_⟩
  intro y
  obtain ⟨d, rfl⟩ := typedEndpoint_surjective (nonOrientableBoundaryWord p 0) y
  cases d with
  | pos e =>
      cases e with
      | a i => exact hbase i
      | c i => exact Fin.elim0 i
      | h i => exact Fin.elim0 i
  | neg e =>
      cases e with
      | a i => exact (nonOrientable_block_vertices p i).trans (hbase i)
      | c i => exact Fin.elim0 i
      | h i => exact Fin.elim0 i

def orientableEdgeEquiv (p : Nat) : OrientableEdge p 0 ≃ Fin p ⊕ Fin p where
  toFun
    | .a i => Sum.inl i
    | .b i => Sum.inr i
    | .c i => Fin.elim0 i
    | .h i => Fin.elim0 i
  invFun
    | .inl i => .a i
    | .inr i => .b i
  left_inv e := by cases e <;> first | rfl | exact Fin.elim0 ‹Fin 0›
  right_inv e := by cases e <;> rfl

def nonOrientableEdgeEquiv (p : Nat) : NonOrientableEdge p 0 ≃ Fin p where
  toFun
    | .a i => i
    | .c i => Fin.elim0 i
    | .h i => Fin.elim0 i
  invFun := .a
  left_inv e := by cases e <;> first | rfl | exact Fin.elim0 ‹Fin 0›
  right_inv _ := rfl

theorem orientable_euler_characteristic (p : Nat) (hp : 0 < p) :
    eulerCharacteristic (NormalForm.orientable p 0).canonicalPresentation = 2 - 2 * (p : ℤ) := by
  have he := Fintype.card_congr (orientableEdgeEquiv p)
  simp only [Fintype.card_sum, Fintype.card_fin] at he
  rw [eulerCharacteristic, orientable_vertex_count p hp]
  change (1 : ℤ) - Fintype.card (OrientableEdge p 0) + 1 = _
  rw [he]
  push_cast
  ring

theorem nonOrientable_euler_characteristic (p : Nat) (hp : 0 < p) :
    eulerCharacteristic (NormalForm.nonOrientable p 0).canonicalPresentation = 2 - (p : ℤ) := by
  have he := Fintype.card_congr (nonOrientableEdgeEquiv p)
  simp only [Fintype.card_fin] at he
  rw [eulerCharacteristic, nonOrientable_vertex_count p hp]
  change (1 : ℤ) - Fintype.card (NonOrientableEdge p 0) + 1 = _
  rw [he]
  ring

theorem sphere_vertex_count : Nat.card (Vertex NormalForm.sphere.canonicalPresentation) = 1 := by
  change Nat.card (Vertex twoMonogonSphere) = 1
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨endpoint twoMonogonSphere (.pos 0), ?_⟩
  intro y
  refine Quot.inductionOn y (fun d => ?_)
  cases d with
  | pos e =>
      have he : e = 0 := Subsingleton.elim _ _
      subst e
      rfl
  | neg e =>
      have he : e = 0 := Subsingleton.elim _ _
      subst e
      exact corner_eq (P := twoMonogonSphere) ⟨0, ⟨0, by decide⟩⟩

theorem sphere_euler_characteristic :
    eulerCharacteristic NormalForm.sphere.canonicalPresentation = 2 := by
  rw [eulerCharacteristic, sphere_vertex_count]
  rfl

#print axioms orientable_euler_characteristic
#print axioms nonOrientable_euler_characteristic
#print axioms sphere_euler_characteristic
end Venn17.Topology.PolygonVertices
