import VennTopology.LinkData
import VennCore.Symmetry
import VennCore.Rotation

/-! Small additional certificates for the geometric pole-link action. They
check the actual 34-vertex triangulated links, not a topological conjugacy. -/
namespace Venn17.Topology

def encodedRotationStepWith (table : Array Nat) (x : Nat) : Nat :=
  if x < 131072 then regionStep x else 131072 + table.getD (x - 131072) 0

def encodedRotationStep (fs : Array Face) (x : Nat) : Nat :=
  encodedRotationStepWith (rotationWitnesses fs) x

def poleLinkActionCheck (fs : Array Face) (stars : LinkProof.Stars) (pole step : Nat) : Bool :=
  let row := stars.getD pole #[]
  let table := rotationWitnesses fs
  row.size == 34 && (Array.range row.size).all fun i =>
    let v := LinkProof.tail fs 131072 (row.getD i 0)
    decide (v < 131072 + fs.size) &&
      encodedRotationStepWith table v == LinkProof.tail fs 131072 (row.getD ((i + step) % row.size) 0)

theorem supplied_pole_link_action_verified :
    poleLinkActionCheck suppliedModel.oriented suppliedLinkStars 0 2 = true ∧
    poleLinkActionCheck suppliedModel.oriented suppliedLinkStars 131071 32 = true := by
  native_decide

end Venn17.Topology
