import VennTopology.Regions

noncomputable section
namespace Venn17.Topology
open Set
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons

theorem regionStep_lt {v : Nat} (hv : v < 131072) : regionStep v < 131072 := by
  have h := Array.all_eq_true.mp region_rotation_verified v (by simpa using hv)
  simp only [Array.getElem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  simpa [regionStep, hv] using h.1

/-- The certified bit rotation restricted to the actual pattern set. -/
def patternRotation : Equiv.Perm (Fin 131072) :=
  Fin.equivSubtype.trans ((regionPermutation.subtypeEquiv
    (p := fun v => v < 131072) (q := fun v => v < 131072) (by
    intro v
    change v < 131072 ↔ regionStep v < 131072
    constructor
    · exact regionStep_lt
    · intro h
      by_contra hv
      simpa [regionStep, hv] using h)).trans Fin.equivSubtype.symm)

@[simp] theorem patternRotation_val (v : Fin 131072) :
    (patternRotation v).val = regionStep v.val := rfl

theorem diagram_encoded_region_coordinate (x : Diagram) (v : Fin 131072) :
    (diagramEncodedHomeomorph x).val v.val = x.val (.inl v.val) := by
  change Coordinates.reindex (Coordinates.labelEquiv 131072 suppliedModel.oriented.size) x.val v.val = _
  rw [Coordinates.reindex_apply]
  apply congrArg x.val
  exact (Coordinates.labelEquiv 131072 suppliedModel.oriented.size).symm_apply_eq.mpr
    (Coordinates.labelEquiv_region _ _ _ v.isLt).symm

theorem diagram_rotation_region_coordinate (x : Diagram) (v : Fin 131072) :
    (diagramEncodedHomeomorph (diagramRotation x)).val (patternRotation v).val =
      (diagramEncodedHomeomorph x).val v.val := by
  rw [diagram_encoded_region_coordinate, diagram_encoded_region_coordinate]
  change x.val (diagramAutomorphism.labels.symm
    (diagramAutomorphism.labels (.inl v.val))) = x.val (.inl v.val)
  rw [Equiv.symm_apply_apply]

/-- The actual open regions, including their interiors, follow the bit shift. -/
theorem diagram_rotation_mem_region (x : Diagram) (v : Fin 131072) :
    diagramRotation x ∈ diagramRegion (patternRotation v) ↔ x ∈ diagramRegion v := by
  change Coordinates.Dominates _ _ _ ↔ Coordinates.Dominates _ _ _
  unfold Coordinates.Dominates
  rw [diagram_rotation_region_coordinate]
  constructor
  · rintro ⟨hp,h⟩
    refine ⟨hp,fun w hw => ?_⟩
    have hn : (patternRotation w).val ≠ (patternRotation v).val := by
      intro he
      exact hw (congrArg Fin.val (patternRotation.injective (Fin.ext he)))
    simpa only [diagram_rotation_region_coordinate] using h (patternRotation w) hn
  · rintro ⟨hp,h⟩
    refine ⟨hp,fun w hw => ?_⟩
    obtain ⟨u,rfl⟩ := patternRotation.surjective w
    rw [diagram_rotation_region_coordinate]
    exact h u (fun he => hw (congrArg (fun a => (patternRotation a).val) (Fin.ext he)))

theorem diagram_rotation_region_image (v : Fin 131072) :
    diagramRotation '' diagramRegion v = diagramRegion (patternRotation v) := by
  ext x
  obtain ⟨y,rfl⟩ := diagramRotation.surjective x
  rw [diagramRotation.injective.mem_set_image,diagram_rotation_mem_region]

theorem diagram_rotation_preserves_complement (x : Diagram) :
    diagramRotation x ∈ diagramComplement ↔ x ∈ diagramComplement := by
  change diagramRotation x ∉ ⋃ i, diagramCurve i ↔ x ∉ ⋃ i, diagramCurve i
  rw [diagram_complement_unique_region,diagram_complement_unique_region]
  constructor
  · rintro ⟨v,hv,_⟩
    obtain ⟨u,rfl⟩ := patternRotation.surjective v
    have hu := (diagram_rotation_mem_region x u).mp hv
    refine ⟨u,hu,fun w hw => ?_⟩
    exact Fin.ext (Coordinates.dominates_disjoint w.isLt u.isLt hw hu)
  · rintro ⟨v,hv,_⟩
    have hu := (diagram_rotation_mem_region x v).mpr hv
    refine ⟨patternRotation v,hu,fun w hw => ?_⟩
    exact Fin.ext (Coordinates.dominates_disjoint w.isLt (patternRotation v).isLt hw hu)

#print axioms diagram_rotation_region_image
end Venn17.Topology
