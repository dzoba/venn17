import Venn17.Proof
import VennCore.Connectivity

namespace Venn17

def suppliedModel : Model := makeModel suppliedFaces

def sideActive (i : Nat) (side : Bool) (v : Nat) : Bool :=
  ((v / 2^i) % 2 == 1) == side

def curveActive (g : Graph) (v : Nat) : Bool := !g[v]!.isEmpty

/-- Independent spanning-tree certificates, checked against actual graph edges. -/
def graphCertificates (m : Model) : Bool :=
  GraphProof.connectedCheck m.graph (fun _ => true) &&
  (Array.range 17).all (fun i =>
    let g := m.curves[i]!
    GraphProof.connectedCheck g (curveActive g) &&
    g.all (fun ns => ns.isEmpty || ns.size == 2)) &&
  (Array.range 17).all (fun i => (#[false, true]).all fun side =>
    GraphProof.connectedCheck m.graph (sideActive i side))

theorem graph_certificates_pass : graphCertificates suppliedModel = true := by
  native_decide


end Venn17
