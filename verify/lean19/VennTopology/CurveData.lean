import VennCore.CurvePolygon
import Venn19.GraphCertificate

namespace Venn19.Topology

def suppliedCurvePolygons : Array CurveProof.Polygon :=
  (Array.range 19).map fun i => CurveProof.propose suppliedModel.oriented 524288 i

theorem supplied_curve_polygons_verified :
    (Array.range 19).all (fun i =>
      CurveProof.check suppliedModel.oriented 524288 i
        (suppliedCurvePolygons.getD i default) &&
      (suppliedCurvePolygons.getD i default).vertices.size == 110376) = true := by
  native_decide

theorem supplied_curve_labels_verified :
    CurveProof.labelsCheck suppliedModel.oriented 524288 19 = true := by native_decide

theorem supplied_crossing_labels_verified :
    CurveProof.crossingLabelsCheck suppliedModel.oriented 524288 = true := by native_decide

end Venn19.Topology
