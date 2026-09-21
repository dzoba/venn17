import VennTopology.MeridianParameterEquality
import VennTopology.SectorGluing

/-! The boundary compatibility is proved, so the sector homeomorphisms glue
unconditionally to a global conjugacy with the rigid Euclidean sphere rotation. -/
noncomputable section
namespace Venn19.Topology
open Set Coordinates LeanEval.Topology.ClassificationOfSurfaces
attribute [local irreducible] suppliedModel suppliedFaces suppliedSectorColors suppliedSectorMasks
attribute [local irreducible] sectorConjugacy

theorem meridian_boundary_parameter_compatibility (k l a b : Fin 19) (z w : Circle) :
    diagramMeridianBoundaryMap k l z = diagramMeridianBoundaryMap a b w ↔
      sphereMeridianBoundary (rigidDirection k) (rigidDirection l) z =
        sphereMeridianBoundary (rigidDirection a) (rigidDirection b) w := by
  obtain ⟨t, ht⟩ := meridianCircleParameter_halves z
  obtain ⟨u, hu⟩ := meridianCircleParameter_halves w
  rcases ht with rfl | rfl <;> rcases hu with rfl | rfl
  all_goals
    simp only [diagramMeridianBoundaryMap_front, diagramMeridianBoundaryMap_back,
      sphereMeridianBoundary_front, sphereMeridianBoundary_back]
    exact meridian_parameter_compatibility _ _ _ _

/-- Equality of the actual constructed boundary points is preserved in both directions. -/
theorem sector_boundary_compatibility : SectorBoundaryCompatibility := by
  intro k l z w
  exact meridian_boundary_parameter_compatibility k (cyclicNext k) l (cyclicNext l) _ _

/-- An unconditional global sphere conjugacy, extending the constructed sector maps. -/
theorem exists_rigidSphereConjugacy :
    ∃ H : Diagram ≃ₜ SphereRepresentative,
      (∀ k x (hx : x ∈ diagramSector k), H x = (sectorConjugacy k ⟨x, hx⟩).val) ∧
      (∀ x, H (diagramRotation x) = rigidSphereRotation rigidGenerator (H x)) :=
  sphere_conjugacy_of_boundary_compatibility sector_boundary_compatibility

def rigidSphereConjugacy : Diagram ≃ₜ SphereRepresentative :=
  Classical.choose exists_rigidSphereConjugacy

theorem rigidSphereConjugacy_sector (k : Fin 19) (x : Diagram) (hx : x ∈ diagramSector k) :
    rigidSphereConjugacy x = (sectorConjugacy k ⟨x, hx⟩).val :=
  (Classical.choose_spec exists_rigidSphereConjugacy).1 k x hx

theorem rigidSphereConjugacy_rotation (x : Diagram) :
    rigidSphereConjugacy (diagramRotation x) =
      rigidSphereRotation rigidGenerator (rigidSphereConjugacy x) :=
  (Classical.choose_spec exists_rigidSphereConjugacy).2 x

theorem rigidSphereConjugacy_boundary (k : Fin 19) (z : UnitCircle) :
    rigidSphereConjugacy (sectorBoundaryParam k z) = rigidSectorParam k z := by
  rw [rigidSphereConjugacy_sector k _ (sectorBoundaryParam_subset k (mem_range_self z)),
    sectorConjugacy_boundary]

theorem rigidSphereConjugacy_meridian (k : Fin 19) (t : MeridianParameter) :
    rigidSphereConjugacy (diagramMeridianMap k t) = rigidMeridianMap k t := by
  have h := rigidSphereConjugacy_boundary k
    (JordanCurve.Arcs.spherePlaneHomeoCircle.symm (meridianCircleParameter t))
  simpa only [sectorBoundaryParam, rigidSectorParam, sphereLuneParam, Function.comp_apply,
    Homeomorph.apply_symm_apply, diagramMeridianMap, rigidMeridianMap] using h

def rigidNorth : SphereRepresentative := rigidMeridianMap 0 meridianStart
def rigidSouth : SphereRepresentative := rigidMeridianMap 0 meridianEnd

theorem rigidNorth_val : rigidNorth.val = fromHorizontal 0 1 := by
  simp [rigidNorth, rigidMeridianMap_val, meridianCircleParameter_start]
theorem rigidSouth_val : rigidSouth.val = fromHorizontal 0 (-1) := by
  simp [rigidSouth, rigidMeridianMap_val, meridianCircleParameter_end]

theorem rigidSphereConjugacy_zero : rigidSphereConjugacy (patternPoint 0) = rigidNorth := by
  have h := rigidSphereConjugacy_meridian 0 meridianStart
  rw [show diagramMeridianMap 0 meridianStart = patternPoint 0 from diagramMeridianMap_zero 0] at h
  exact h

theorem rigidSphereConjugacy_one : rigidSphereConjugacy (patternPoint 524287) = rigidSouth := by
  have h := rigidSphereConjugacy_meridian 0 meridianEnd
  rw [show diagramMeridianMap 0 meridianEnd = patternPoint 524287 from diagramMeridianMap_one 0] at h
  exact h

end Venn19.Topology
