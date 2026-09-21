import VennTopology.Realization
import Mathlib.Logic.Function.Iterate

noncomputable section
namespace Venn19.Topology.Quad

open Set
variable {V F : Type*}

def coordinateLinear (σ : Equiv.Perm (V ⊕ F)) : Ambient V F →ₗ[ℝ] Ambient V F where
  toFun x a := x (σ.symm a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinateHomeomorph (σ : Equiv.Perm (V ⊕ F)) : Ambient V F ≃ₜ Ambient V F where
  toFun x a := x (σ.symm a)
  invFun x a := x (σ a)
  left_inv x := by ext a; simp
  right_inv x := by ext a; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem coordinateLinear_point (σ : Equiv.Perm (V ⊕ F)) (a : V ⊕ F) :
    coordinateLinear σ (point a) = point (σ a) := by
  classical
  ext b
  simp [coordinateLinear, point, Equiv.symm_apply_eq]

@[simp] theorem coordinateHomeomorph_point (σ : Equiv.Perm (V ⊕ F)) (a : V ⊕ F) :
    coordinateHomeomorph σ (point a) = point (σ a) := coordinateLinear_point σ a

theorem coordinate_iterate (σ : Equiv.Perm (V ⊕ F)) (n : Nat) (x : Ambient V F) (b : V ⊕ F) :
    ((coordinateHomeomorph σ)^[n] x) b = x (σ.symm^[n] b) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change ((coordinateHomeomorph σ)^[n] x) (σ.symm b) = _
    rw [ih, Function.iterate_succ_apply]

theorem coordinate_iterate_point (σ : Equiv.Perm (V ⊕ F)) (n : Nat) (b : V ⊕ F) :
    (coordinateHomeomorph σ)^[n] (point b) = point (σ^[n] b) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, coordinateHomeomorph_point,
      Function.iterate_succ_apply']

/-- A cyclic-order-preserving automorphism of the quadrilateral data. -/
structure Automorphism (q : Quad V F) where
  vertices : Equiv.Perm V
  faces : Equiv.Perm F
  corners : F → Equiv.Perm (Fin 4)
  next_eq : ∀ f k, corners f (next k) = next (corners f k)
  corner_eq : ∀ f k, vertices (q.corner f k) = q.corner (faces f) (corners f k)

namespace Automorphism
variable {q : Quad V F} (a : Automorphism q)

def labels : Equiv.Perm (V ⊕ F) := Equiv.sumCongr a.vertices a.faces

theorem triangle_image (f : F) (k : Fin 4) :
    coordinateHomeomorph a.labels '' q.triangle f k =
      q.triangle (a.faces f) (a.corners f k) := by
  change coordinateLinear a.labels '' convexHull ℝ (q.triangleVertices f k) = _
  rw [LinearMap.image_convexHull]
  unfold triangle triangleVertices
  congr 1
  simp [Set.image_insert_eq, labels, a.corner_eq, a.next_eq]

theorem space_image : coordinateHomeomorph a.labels '' q.space = q.space := by
  simp only [space, image_iUnion, a.triangle_image]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨f, k, h⟩
    exact ⟨a.faces f, a.corners f k, h⟩
  · rintro ⟨f, k, h⟩
    refine ⟨a.faces.symm f, (a.corners (a.faces.symm f)).symm k, ?_⟩
    simpa using h

/-- The action is a genuine homeomorphism of the realized space, with its
subspace topology, not merely a permutation of the input labels. -/
def homeomorph : q.Realization ≃ₜ q.Realization :=
  (coordinateHomeomorph a.labels).subtype fun x => by
    change x ∈ q.space ↔ coordinateHomeomorph a.labels x ∈ q.space
    constructor
    · intro hx
      rw [← a.space_image]
      exact mem_image_of_mem _ hx
    · intro hx
      rw [← a.space_image] at hx
      obtain ⟨y, hy, he⟩ := hx
      exact (coordinateHomeomorph a.labels).injective he ▸ hy

@[simp] theorem homeomorph_val (x : q.Realization) :
    (a.homeomorph x).val = coordinateHomeomorph a.labels x.val := rfl

theorem homeomorph_iterate_val (n : Nat) (x : q.Realization) :
    ((a.homeomorph)^[n] x).val = (coordinateHomeomorph a.labels)^[n] x.val := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', homeomorph_val, ih]

theorem labels_iterate_inl (n : Nat) (v : V) :
    a.labels^[n] (.inl v) = .inl (a.vertices^[n] v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    rfl

theorem labels_iterate_inr (n : Nat) (f : F) :
    a.labels^[n] (.inr f) = .inr (a.faces^[n] f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    rfl

theorem homeomorph_period (n : Nat)
    (hv : ∀ v, a.vertices^[n] v = v) (hf : ∀ f, a.faces^[n] f = f)
    (x : q.Realization) : a.homeomorph^[n] x = x := by
  have hp (b : V ⊕ F) : a.labels^[n] b = b := by
    cases b with
    | inl v => rw [a.labels_iterate_inl, hv]
    | inr f => rw [a.labels_iterate_inr, hf]
  have hi (b : V ⊕ F) : a.labels.symm^[n] b = b := by
    have h := (Function.LeftInverse.iterate a.labels.apply_symm_apply n) b
    rwa [hp] at h
  apply Subtype.ext
  rw [a.homeomorph_iterate_val]
  funext b
  rw [coordinate_iterate, hi]

theorem point_fixed {v : V} (hv : a.vertices v = v)
    (hmem : point (.inl v) ∈ q.space) :
    a.homeomorph ⟨point (.inl v), hmem⟩ = ⟨point (.inl v), hmem⟩ := by
  apply Subtype.ext
  change coordinateHomeomorph a.labels (point (.inl v)) = point (.inl v)
  simp [labels, hv]

end Automorphism

#print axioms Automorphism.homeomorph

end Venn19.Topology.Quad
