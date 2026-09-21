import VennCore.Links
import VennTopology.Dataset

namespace Venn19.Topology

def suppliedLinkStars : LinkProof.Stars :=
  LinkProof.propose suppliedModel.oriented 524288

theorem supplied_link_stars_verified :
    LinkProof.check suppliedModel.oriented 524288 suppliedLinkStars = true := by
  native_decide

end Venn19.Topology
