import VennTopology.Stars
import VennTopology.Certificate

noncomputable section
namespace Venn19.Topology

open Set
open scoped Classical

namespace Quad
variable {V F : Type*} (q : Quad V F)

local instance : DecidableEq (V ⊕ F) := Classical.decEq _

theorem coordinates_vertex_eq (a : V ⊕ F) : Coordinates.vertex a = point a := by
  funext b
  by_cases h : b = a <;> simp [Coordinates.vertex, point, h]

def cellLabels (t : F × Fin 4) : Finset (V ⊕ F) :=
  {.inr t.1, .inl (q.corner t.1 t.2), .inl (q.corner t.1 (next t.2))}

theorem triangle_eq_simplex (f : F) (k : Fin 4) :
    q.triangle f k = Coordinates.simplex (q.cellLabels (f,k)) := by
  unfold triangle triangleVertices Coordinates.simplex cellLabels
  simp only [Finset.coe_insert, Finset.coe_singleton, image_insert_eq, image_singleton]
  simp only [coordinates_vertex_eq]

theorem realization_eq_space : Coordinates.realization q.cellLabels = q.space := by
  ext x
  simp only [Coordinates.realization, space, triangle_eq_simplex, mem_iUnion, Prod.exists]

theorem cellLabels_card (hc : ∀ f, Function.Injective (q.corner f)) (t : F × Fin 4) :
    (q.cellLabels t).card = 3 := by
  have hne : q.corner t.1 t.2 ≠ q.corner t.1 (next t.2) :=
    fun h => next_ne t.2 (hc t.1 h).symm
  simp [cellLabels, hne]

theorem cellLabels_erase_nonempty (hc : ∀ f, Function.Injective (q.corner f))
    (t : F × Fin 4) (a : V ⊕ F) (ha : a ∈ q.cellLabels t) :
    ((q.cellLabels t).erase a).Nonempty := by
  apply Finset.card_pos.mp
  rw [Finset.card_erase_of_mem ha, q.cellLabels_card hc]
  norm_num

def geometricLink (a : V ⊕ F) : Set (Ambient V F) := Coordinates.link q.cellLabels a

/-- Radial coordinates for a punctured vertex neighborhood in the original
quadrilateral realization. The link has not been replaced by an abstract flag. -/
def puncturedStarHomeomorph (hc : ∀ f, Function.Injective (q.corner f)) (a : V ⊕ F) :
    {x : Ambient V F | x ∈ q.space ∧ 0 < x a ∧ x a < 1} ≃ₜ
      (q.geometricLink a × Ioo (0 : ℝ) 1) :=
  (Homeomorph.setCongr (by rw [← q.realization_eq_space]; rfl)).trans
    (Coordinates.puncturedStarHomeomorph q.cellLabels (q.cellLabels_erase_nonempty hc) a)

theorem open_stars_cover (x : q.Realization) : ∃ a, 0 < x.val a := by
  have hx : x.val ∈ Coordinates.realization q.cellLabels := by
    rw [q.realization_eq_space]
    exact x.property
  obtain ⟨a, _, ha⟩ := Coordinates.open_stars_cover q.cellLabels hx
  exact ⟨a, ha⟩

theorem open_star_isOpen (a : V ⊕ F) : IsOpen {x : q.Realization | 0 < x.val a} :=
  isOpen_lt continuous_const ((continuous_apply a).comp continuous_subtype_val)

end Quad

def diagram_punctured_star_homeomorph (a : Nat ⊕ Fin suppliedModel.oriented.size) :
    {x : Quad.Ambient Nat (Fin suppliedModel.oriented.size) |
      x ∈ diagramQuad.space ∧ 0 < x a ∧ x a < 1} ≃ₜ
    (diagramQuad.geometricLink a × Ioo (0 : ℝ) 1) :=
  diagramQuad.puncturedStarHomeomorph diagram_corners_injective a

#print axioms diagram_punctured_star_homeomorph

end Venn19.Topology
