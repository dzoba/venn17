import VennCore.CurvePolygon
import Venn17.GraphCertificate

namespace Venn17.Topology

def suppliedCurvePolygons : Array CurveProof.Polygon :=
  (Array.range 17).map fun i => CurveProof.propose suppliedModel.oriented 131072 i

theorem supplied_curve_polygons_verified :
    (Array.range 17).all (fun i =>
      CurveProof.check suppliedModel.oriented 131072 i
        (suppliedCurvePolygons.getD i default) &&
      (suppliedCurvePolygons.getD i default).vertices.size == 30840) = true := by
  native_decide

theorem supplied_curve_labels_verified :
    CurveProof.labelsCheck suppliedModel.oriented 131072 17 = true := by native_decide

theorem supplied_crossing_labels_verified :
    CurveProof.crossingLabelsCheck suppliedModel.oriented 131072 = true := by native_decide

end Venn17.Topology
