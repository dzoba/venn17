import VennTopology.Realization
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion

noncomputable section
namespace Venn19.Topology.Quad

open Set
variable {V F : Type*}

theorem point_affineIndependent : AffineIndependent ℝ (point (V := V) (F := F)) := by
  classical
  have he : point (V := V) (F := F) = fun a => Pi.single a (1 : ℝ) := by
    funext a b
    simp [point, Pi.single_apply, eq_comm]
  rw [he]
  exact (Pi.linearIndependent_single_one (V ⊕ F) ℝ).affineIndependent

def triangleFinset (q : Quad V F) (f : F) (k : Fin 4) : Finset (Ambient V F) := by
  classical
  exact {point (.inr f), point (.inl (q.corner f k)), point (.inl (q.corner f (next k)))}

@[simp] theorem triangleFinset_coe (q : Quad V F) (f : F) (k : Fin 4) :
    (q.triangleFinset f k : Set (Ambient V F)) = q.triangleVertices f k := by
  classical
  simp [triangleFinset, triangleVertices]

theorem next_ne (k : Fin 4) : next k ≠ k := by decide +revert

theorem triangle_card (q : Quad V F) (f : F) (k : Fin 4)
    (hf : Function.Injective (q.corner f)) : (q.triangleFinset f k).card = 3 := by
  classical
  have hne : q.corner f k ≠ q.corner f (next k) := fun h => next_ne k (hf h).symm
  simp [triangleFinset, point_injective.eq_iff, hne]

theorem triangleVertices_subset_range (q : Quad V F) (f : F) (k : Fin 4) :
    q.triangleVertices f k ⊆ range point := by
  intro x hx
  simp only [triangleVertices, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> exact mem_range_self _

/-- Two realized triangles meet exactly in the convex hull of their shared
vertices. Thus the coordinate realization introduces no accidental overlaps. -/
theorem triangle_inter (q : Quad V F) (f g : F) (k l : Fin 4) :
    q.triangle f k ∩ q.triangle g l =
      convexHull ℝ (q.triangleVertices f k ∩ q.triangleVertices g l) := by
  classical
  have hs : AffineIndependent ℝ
      ((↑) : ↑(q.triangleFinset f k ∪ q.triangleFinset g l) → Ambient V F) := by
    apply point_affineIndependent.range.mono
    simp only [Finset.coe_union, triangleFinset_coe]
    exact union_subset (q.triangleVertices_subset_range f k) (q.triangleVertices_subset_range g l)
  simpa only [triangleFinset_coe, triangle] using hs.convexHull_inter'.symm

/-- The triangles together with every nonempty face of every triangle. -/
def abstractComplex (q : Quad V F) : PreAbstractSimplicialComplex (Ambient V F) where
  faces := {s | s.Nonempty ∧ ∃ f k, s ⊆ q.triangleFinset f k}
  isRelLowerSet_faces := by
    rintro s ⟨hne, f, k, hs⟩
    exact ⟨hne, fun t ht htne => ⟨htne, f, k, ht.trans hs⟩⟩

/-- A Mathlib geometric simplicial complex, with the subspace realization
already used above. Nondegeneracy of the triangles is a separate input fact. -/
def complex (q : Quad V F) : Geometry.SimplicialComplex ℝ (Ambient V F) := by
  classical
  refine .ofAffineIndependent q.abstractComplex (point_affineIndependent.range.mono ?_)
  intro x hx
  obtain ⟨s, ⟨_, f, k, hs⟩, hx⟩ := mem_iUnion₂.mp hx
  apply q.triangleVertices_subset_range f k
  rw [← triangleFinset_coe]
  exact hs hx

theorem complex_space (q : Quad V F) : q.complex.space = q.space := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, ⟨_, f, k, hs⟩, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    apply q.triangle_subset_space f k
    apply convexHull_mono (s := (s : Set (Ambient V F))) _ hx
    rw [← triangleFinset_coe]
    exact hs
  · intro hx
    obtain ⟨f, k, hx⟩ := mem_iUnion.mp hx |>.imp (fun f => mem_iUnion.mp)
    apply Geometry.SimplicialComplex.mem_space_iff.mpr
    refine ⟨q.triangleFinset f k, ⟨?_, f, k, Finset.Subset.refl _⟩, ?_⟩
    · simp [triangleFinset]
    · simpa only [triangleFinset_coe, triangle] using hx

theorem complex_faces_finite [Finite F] (q : Quad V F) : q.complex.faces.Finite := by
  classical
  have he : q.complex.faces = ⋃ f, ⋃ k, {s | s.Nonempty ∧ s ∈ (q.triangleFinset f k).powerset} := by
    ext s
    simp only [complex, Geometry.SimplicialComplex.ofAffineIndependent, abstractComplex,
      mem_setOf_eq, mem_iUnion, Finset.mem_powerset]
    aesop
  rw [he]
  apply Set.finite_iUnion
  intro f
  apply Set.finite_iUnion
  intro k
  exact (q.triangleFinset f k).powerset.finite_toSet.subset fun _ h => h.2

#print axioms triangle_inter
#print axioms complex_space

end Venn19.Topology.Quad
