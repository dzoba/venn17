import VennTopology.SideComponents
import VennTopology.PuncturedArrangement
import VennTopology.PunctureConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.WithSeminorms

noncomputable section
namespace Venn17.Topology
open Set
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

theorem zero_region_subset_false_side (i : Fin 17) : diagramRegion 0 ⊆ diagramSide i false := by
  intro x hx
  exact (diagram_region_side_iff i 0 false hx).mpr (by simp)

theorem pole_not_true_side (i : Fin 17) : patternPoint 0 ∉ diagramSide i true := by
  intro hx
  have h := (diagram_region_side_iff i 0 true (patternPoint_mem_region 0)).mp hx
  simpa using h

theorem diagramSide_punctured_pathConnected (i : Fin 17) (b : Bool) :
    IsPathConnected (diagramSide i b \ {patternPoint 0}) := by
  cases b
  · letI : LocallyPathConnectedSpace Diagram := ChartedSpace.locallyPathConnectedSpace ℂ Diagram
    apply ((diagramSide_isOpen i false).sdiff isClosed_singleton).isConnected_iff_isPathConnected.mp
    refine ⟨?_,preconnected_diff_singleton_of_neighborhood
      (diagramSide_pathConnected i false).isConnected.isPreconnected
      (diagramRegion_isOpen 0) (patternPoint_mem_region 0) (zero_region_subset_false_side i)
      (diagramRegion_punctured_pathConnected 0).isConnected.isPreconnected⟩
    obtain ⟨x,hx⟩ := (diagramRegion_punctured_pathConnected 0).nonempty
    exact ⟨x,zero_region_subset_false_side i hx.1,hx.2⟩
  · have he : diagramSide i true \ {patternPoint 0} = diagramSide i true := by
      ext x
      exact ⟨And.left,fun hx => ⟨hx,fun he => pole_not_true_side i (he ▸ hx)⟩⟩
    rw [he]
    exact diagramSide_pathConnected i true

def puncturedSide (i : Fin 17) (b : Bool) : Set PuncturedDiagram := Subtype.val ⁻¹' diagramSide i b

theorem puncturedSide_isOpen (i : Fin 17) (b : Bool) : IsOpen (puncturedSide i b) :=
  (diagramSide_isOpen i b).preimage continuous_subtype_val

theorem puncturedSide_pathConnected (i : Fin 17) (b : Bool) : IsPathConnected (puncturedSide i b) := by
  have h := (diagramSide_punctured_pathConnected i b).preimage_coe (fun _ hx => hx.2)
  have he : (Subtype.val : PuncturedDiagram → Diagram) ⁻¹' (diagramSide i b \ {patternPoint 0}) =
      puncturedSide i b := by
    ext x; exact and_iff_left x.property
  exact he ▸ h

theorem puncturedSide_cover (i : Fin 17) : (⋃ b, puncturedSide i b) = (puncturedCurve i)ᶜ := by
  change (⋃ b, Subtype.val ⁻¹' diagramSide i b) = (Subtype.val ⁻¹' diagramCurve i)ᶜ
  rw [← preimage_iUnion,diagramSide_cover,preimage_compl]

theorem puncturedSide_disjoint (i : Fin 17) : Disjoint (puncturedSide i false) (puncturedSide i true) :=
  (diagramSide_disjoint i).preimage Subtype.val

theorem puncturedRegion_eq_sides (v : Fin 131072) :
    puncturedRegion v = ⋂ i : Fin 17, puncturedSide i (v.val.testBit i.val) := by
  change Subtype.val ⁻¹' diagramRegion v = ⋂ i : Fin 17, Subtype.val ⁻¹' diagramSide i (v.val.testBit i.val)
  rw [diagramRegion_eq_sides,preimage_iInter]

def puncturedCurveComplement (i : Fin 17) : Set PuncturedDiagram := (puncturedCurve i)ᶜ

def puncturedCurveComplementSide (i : Fin 17) (b : Bool) : Set (puncturedCurveComplement i) :=
  Subtype.val ⁻¹' puncturedSide i b

def curveComplementForget (i : Fin 17) (x : puncturedCurveComplement i) : diagramCurveComplement i :=
  ⟨x.val.val,x.property⟩

theorem puncturedCurveComplementSide_isClopen (i : Fin 17) (b : Bool) :
    IsClopen (puncturedCurveComplementSide i b) := by
  have hc : Continuous (curveComplementForget i) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have h := (curveComplementSide_isClopen i b).preimage hc
  convert h using 1
  ext x
  rfl

theorem puncturedCurveComplementSide_pathConnected (i : Fin 17) (b : Bool) :
    IsPathConnected (puncturedCurveComplementSide i b) :=
  (puncturedSide_pathConnected i b).preimage_coe (fun _ hx => diagramSide_subset_complement i b hx)

def puncturedSideComponentsEquiv (i : Fin 17) : ConnectedComponents (puncturedCurveComplement i) ≃ Bool :=
  ConnectedComponents.equivOfIsClopenOfIsConnected (puncturedCurveComplementSide_isClopen i)
    (fun b c hbc => (curveComplementSide_pairwise i hbc).preimage (curveComplementForget i))
    (by
      apply Set.eq_univ_of_forall
      intro x
      have hx : x.val ∈ ⋃ b, puncturedSide i b := by rw [puncturedSide_cover]; exact x.property
      obtain ⟨b,hb⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨b,hb⟩)
    (fun b => (puncturedCurveComplementSide_pathConnected i b).isConnected)

theorem punctured_curve_complement_component_count (i : Fin 17) :
    Nat.card (ConnectedComponents (puncturedCurveComplement i)) = 2 := by
  rw [Nat.card_congr (puncturedSideComponentsEquiv i)]
  simp

#print axioms puncturedSide_pathConnected
#print axioms punctured_curve_complement_component_count
#print axioms puncturedRegion_eq_sides
end Venn17.Topology
