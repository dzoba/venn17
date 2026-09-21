import VennTopology.GeometricLinks
import VennTopology.OpenStarDisk
import Mathlib.Geometry.Manifold.ChartedSpace

noncomputable section
namespace Venn19.Topology
open Set
open scoped Classical

attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars

/-- Every vertex that has a positive coordinate at a point of the diagram is
among the vertices covered by the finite link certificate. -/
theorem diagram_active_vertex_bound (x : Diagram)
    (a : Nat ⊕ Fin suppliedModel.oriented.size) (ha : 0 < x.val a) :
    Coordinates.labelEquiv 524288 suppliedModel.oriented.size a < suppliedLinkStars.size := by
  rw [supplied_link_rows.1]
  cases a with
  | inr f => simp only [Coordinates.labelEquiv_face]; omega
  | inl v =>
    have hx : x.val ∈ Coordinates.realization diagramQuad.cellLabels := by
      rw [diagramQuad.realization_eq_space]
      exact x.property
    obtain ⟨t, ht⟩ := mem_iUnion.mp hx
    have hm := Coordinates.positive_coordinate_in_cell diagramQuad.cellLabels ht ha
    simp only [Quad.cellLabels, Finset.mem_insert, Finset.mem_singleton,
      Sum.inl.injEq, Sum.inl_ne_inr, false_or] at hm
    have hv : v < 524288 := by
      rcases hm with rfl | rfl
      · exact cornersCheck_sound _ _ supplied_corners_bounded t.1 t.2
      · exact cornersCheck_sound _ _ supplied_corners_bounded t.1 (Quad.next t.2)
    rw [Coordinates.labelEquiv_region _ _ _ hv]
    omega

/-- The open star, as an open subset of the original realized diagram. -/
def diagramOpenStar (a : Nat ⊕ Fin suppliedModel.oriented.size) : Set Diagram :=
  {x | 0 < x.val a}

theorem diagramOpenStar_isOpen (a : Nat ⊕ Fin suppliedModel.oriented.size) :
    IsOpen (diagramOpenStar a) := diagramQuad.open_star_isOpen a

def diagramOpenStarHomeomorph (a : Nat ⊕ Fin suppliedModel.oriented.size)
    (ha : Coordinates.labelEquiv 524288 suppliedModel.oriented.size a < suppliedLinkStars.size) :
    diagramOpenStar a ≃ₜ Metric.ball (0 : ℂ) 1 :=
  (subtypeConjunction diagramQuad.space (fun x => 0 < x a)).trans
    (Homeomorph.setCongr (by rw [← diagramQuad.realization_eq_space]; rfl)) |>.trans
    (Coordinates.openStarDiskHomeomorph diagramQuad.cellLabels a
      (diagramQuad.cellLabels_erase_nonempty diagram_corners_injective)
      (diagram_geometric_link_circle a ha)).symm

/-- Every point, including edge and triangle interiors, lies in an open disk
neighborhood. Together with Hausdorff and second countability this is the
local topological surface theorem for the actual input realization. -/
theorem diagram_locally_open_disk (x : Diagram) :
    ∃ U : Set Diagram, IsOpen U ∧ x ∈ U ∧ Nonempty (U ≃ₜ Metric.ball (0 : ℂ) 1) := by
  obtain ⟨a, ha⟩ := diagramQuad.open_stars_cover x
  exact ⟨diagramOpenStar a, diagramOpenStar_isOpen a, ha,
    ⟨diagramOpenStarHomeomorph a (diagram_active_vertex_bound x a ha)⟩⟩

theorem diagram_second_countable : SecondCountableTopology Diagram := inferInstance

/-- Convert an open disk neighborhood into a chart with values in the complex
plane, viewed as a two-dimensional real topological space. -/
def openDiskChart {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (hN : Nonempty U) (h : U ≃ₜ Metric.ball (0 : ℂ) 1) : OpenPartialHomeomorph X ℂ :=
  (((⟨U, hU⟩ : TopologicalSpace.Opens X).openPartialHomeomorphSubtypeCoe hN).symm.transHomeomorph h).trans
    ((⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩ : TopologicalSpace.Opens ℂ).openPartialHomeomorphSubtypeCoe ⟨⟨0, by simp⟩⟩)

theorem openDiskChart_source {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (hN : Nonempty U) (h : U ≃ₜ Metric.ball (0 : ℂ) 1) :
    (openDiskChart U hU hN h).source = U := by
  simp [openDiskChart, OpenPartialHomeomorph.transHomeomorph_source]

def diagramChart (x : Diagram) : OpenPartialHomeomorph Diagram ℂ :=
  let U := (diagram_locally_open_disk x).choose
  let h := (diagram_locally_open_disk x).choose_spec
  openDiskChart U h.1 ⟨⟨x, h.2.1⟩⟩ h.2.2.some

theorem diagramChart_contains (x : Diagram) : x ∈ (diagramChart x).source := by
  unfold diagramChart
  rw [openDiskChart_source]
  exact (diagram_locally_open_disk x).choose_spec.2.1

/-- A genuine Mathlib charted-space structure on the dataset's realization. -/
instance diagramChartedSpace : ChartedSpace ℂ Diagram where
  atlas := Set.range diagramChart
  chartAt := diagramChart
  mem_chart_source := diagramChart_contains
  chart_mem_atlas x := ⟨x, rfl⟩

/-- The actual candidate is a compact connected topological surface without
boundary. Sphere classification and the labelled Venn curves remain separate. -/
theorem diagram_compact_connected_surface :
    CompactSpace Diagram ∧ T2Space Diagram ∧ SecondCountableTopology Diagram ∧
    ConnectedSpace Diagram ∧ Nonempty (ChartedSpace ℂ Diagram) :=
  ⟨diagram_compact, diagram_hausdorff, diagram_second_countable,
    diagram_connected, ⟨diagramChartedSpace⟩⟩

#print axioms diagram_compact_connected_surface
#print axioms diagram_locally_open_disk
#print axioms diagram_second_countable

end Venn19.Topology
