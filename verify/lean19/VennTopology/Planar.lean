import JordanCurve.Main

namespace Venn19.Topology

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev UnitCircle := Metric.sphere (0 : Plane) 1

/-- The Jordan separation theorem is now available as a proved dependency.
Applying it to this dataset still requires constructing the circle embeddings. -/
theorem planar_jordan_separation (r : UnitCircle → Plane)
    (hc : Continuous r) (hi : Function.Injective r) :
    Nat.card (ConnectedComponents ((Set.range r)ᶜ : Set Plane)) = 2 :=
  JordanCurve.jordan_curve r hc hi

/-- The same proved separation theorem in the circle model used by our
geometric-link and polygon constructions. -/
theorem planar_jordan_separation_circle (r : Circle → Plane)
    (hc : Continuous r) (hi : Function.Injective r) :
    Nat.card (ConnectedComponents ((Set.range r)ᶜ : Set Plane)) = 2 := by
  let e := JordanCurve.Arcs.spherePlaneHomeoCircle
  have h := planar_jordan_separation (r ∘ e) (hc.comp e.continuous) (hi.comp e.injective)
  have hr : Set.range (r ∘ e) = Set.range r := by
    ext x
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨e z, hz⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := e.surjective z
      exact ⟨w, rfl⟩
  exact (congrArg (fun s : Set Plane => Nat.card (ConnectedComponents (sᶜ : Set Plane))) hr).symm.trans h

#print axioms planar_jordan_separation
#print axioms planar_jordan_separation_circle

end Venn19.Topology
