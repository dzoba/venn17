import VennTopology.SphereReduction
import VennTopology.PlanarSides
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! Stereographic projection turns the proved sphere realization into a
planar Venn diagram, with the all-zero region containing infinity. This does
not yet identify the induced order-17 homeomorphism with a rigid rotation. -/

noncomputable section
namespace Venn17.Topology
open Set
open LeanEval.Topology.ClassificationOfSurfaces
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

/-- Remove any chosen point of the standard two-sphere and project to the plane. -/
def sphereWithoutPointHomeomorph (p : SphereRepresentative) :
    {x : SphereRepresentative // x ≠ p} ≃ₜ Plane := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let s := stereographic' 2 p
  have hs : {x : SphereRepresentative | x ≠ p} = s.source := by
    simp only [s, stereographic'_source, compl_singleton_eq]
  have ht : s.target = (univ : Set Plane) := stereographic'_target p
  exact (Homeomorph.setCongr hs).trans (s.toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr ht).trans (Homeomorph.Set.univ Plane)))

/-- The removed all-zero point is sent to the stereographic projection pole. -/
def puncturedSphereHomeomorph : PuncturedDiagram ≃ₜ
    {x : SphereRepresentative // x ≠ diagramSphereHomeomorph (patternPoint 0)} :=
  diagramSphereHomeomorph.subtype (fun _ => not_congr diagramSphereHomeomorph.injective.eq_iff.symm)

/-- Unconditional Euclidean plane realization of the certified punctured diagram. -/
def diagramPlaneHomeomorph : PuncturedDiagram ≃ₜ Plane :=
  puncturedSphereHomeomorph.trans
    (sphereWithoutPointHomeomorph (diagramSphereHomeomorph (patternPoint 0)))

def realizedPlaneCurve (i : Fin 17) : Set Plane := planeCurve diagramPlaneHomeomorph i
def realizedPlaneSide (i : Fin 17) (b : Bool) : Set Plane := planeSide diagramPlaneHomeomorph i b
def realizedPlaneRegion (v : Fin 131072) : Set Plane := planeRegion diagramPlaneHomeomorph v

/-- Actual planar Jordan curves with all 2^17 nonempty connected membership
regions. No sphere or plane homeomorphism is assumed. -/
theorem planar_venn_diagram_verified :
    (∀ i : Fin 17,
      (∃ f : Circle → Plane, Continuous f ∧ Function.Injective f ∧ range f = realizedPlaneCurve i) ∧
      (∀ b, IsOpen (realizedPlaneSide i b) ∧ IsPathConnected (realizedPlaneSide i b)) ∧
      Disjoint (realizedPlaneSide i false) (realizedPlaneSide i true) ∧
      (⋃ b, realizedPlaneSide i b) = (realizedPlaneCurve i)ᶜ ∧
      Bornology.IsBounded (realizedPlaneSide i true) ∧
      ¬ Bornology.IsBounded (realizedPlaneSide i false)) ∧
    (∀ v : Fin 131072, IsPathConnected (realizedPlaneRegion v) ∧
      realizedPlaneRegion v = ⋂ i : Fin 17, realizedPlaneSide i (v.val.testBit i.val)) ∧
    (∀ x : Plane, x ∉ ⋃ i : Fin 17, realizedPlaneCurve i ↔
      ∃! v : Fin 131072, x ∈ realizedPlaneRegion v) ∧
    (∀ b : Fin 17 → Bool, IsPathConnected (⋂ i : Fin 17, realizedPlaneSide i (b i))) :=
  planar_sides_verified diagramPlaneHomeomorph

#print axioms diagramPlaneHomeomorph
#print axioms planar_venn_diagram_verified
end Venn17.Topology
