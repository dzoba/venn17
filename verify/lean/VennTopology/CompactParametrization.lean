import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section
namespace Venn17.Topology

variable {X Y Z : Type*}

def parametrizationFactor (f : X → Y) (hf : Function.Surjective f) (g : X → Z) :
    Y → Set.range g := fun y => ⟨g (Function.surjInv hf y), ⟨_, rfl⟩⟩

theorem parametrizationFactor_comp (f : X → Y) (hf : Function.Surjective f) (g : X → Z)
    (he : ∀ x x', g x = g x' ↔ f x = f x') (x : X) :
    (parametrizationFactor f hf g (f x)).val = g x :=
  (he _ _).mpr (Function.surjInv_eq hf _)

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [CompactSpace X] [CompactSpace Y] [T2Space Y] [T2Space Z]

/-- Continuous parametrizations from a compact space with identical fibers
induce a homeomorphism of their images. -/
def compactParametrizationHomeomorph (f : X → Y) (hf : Function.Surjective f)
    (g : X → Z) (cf : Continuous f) (cg : Continuous g)
    (he : ∀ x x', g x = g x' ↔ f x = f x') : Y ≃ₜ Set.range g := by
  have cb : Continuous (parametrizationFactor f hf g) := by
    apply (cf.isClosedMap.isQuotientMap cf hf).continuous_iff.mpr
    apply Continuous.subtype_mk
    exact cg.congr (fun x => (parametrizationFactor_comp f hf g he x).symm)
  have hb : Function.Bijective (parametrizationFactor f hf g) := by
    constructor
    · intro y y' h
      have h' := (he _ _).mp (congrArg Subtype.val h)
      simpa only [Function.surjInv_eq] using h'
    · rintro ⟨_, x, rfl⟩
      exact ⟨f x, Subtype.ext (parametrizationFactor_comp f hf g he x)⟩
  exact cb.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hb)

theorem compactParametrizationHomeomorph_apply (f : X → Y) (hf : Function.Surjective f)
    (g : X → Z) (cf : Continuous f) (cg : Continuous g)
    (he : ∀ x x', g x = g x' ↔ f x = f x') (x : X) :
    (compactParametrizationHomeomorph f hf g cf cg he (f x)).val = g x :=
  parametrizationFactor_comp f hf g he x

end Venn17.Topology
