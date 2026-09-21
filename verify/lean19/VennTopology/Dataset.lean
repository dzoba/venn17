import VennTopology.Incidence
import Venn19.GraphCertificate

namespace Venn19.Topology

def suppliedIncidenceCheck : Bool :=
  incidenceCheck suppliedModel.oriented suppliedModel.graph

theorem supplied_incidence_verified : suppliedIncidenceCheck = true := by
  native_decide

theorem supplied_distinct_corners_verified : distinctCornersCheck suppliedModel.oriented = true := by
  native_decide

noncomputable def diagramQuad := quadOfFaces suppliedModel.oriented

theorem diagram_corners_injective (f : Fin suppliedModel.oriented.size) :
    Function.Injective (diagramQuad.corner f) :=
  distinctCornersCheck_sound _ supplied_distinct_corners_verified f

/-- The geometric candidate, not yet proved to be a surface or a sphere. -/
abbrev Diagram := diagramQuad.Realization

theorem diagram_compact : CompactSpace Diagram := inferInstance
theorem diagram_hausdorff : T2Space Diagram := inferInstance

theorem diagram_pathConnected : IsPathConnected diagramQuad.space :=
  incidenceCheck_pathConnected _ _ supplied_incidence_verified

instance : PathConnectedSpace Diagram :=
  isPathConnected_iff_pathConnectedSpace.mp diagram_pathConnected

theorem diagram_connected : ConnectedSpace Diagram := inferInstance

#print axioms diagram_compact
#print axioms diagram_hausdorff
#print axioms diagram_pathConnected

end Venn19.Topology
