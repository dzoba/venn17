import VennTopology.SectorData
import VennTopology.DiagramSymmetry

/-! Finite certificates for the proposed sector cover. No disk homeomorphism
or topological assertion is inferred by native computation. -/
namespace Venn17.Topology

def sectorColorCheck (fs : Array Face) (cs : Array Nat) : Bool :=
  let rotations := rotationWitnesses fs
  cs.size == fs.size && (Array.range fs.size).all fun f =>
    cs.getD f 17 < 17 && cs.getD (rotations.getD f 0) 17 == (cs.getD f 17 + 1) % 17

def sectorVertexMasks (fs : Array Face) (cs : Array Nat) : Array Nat := Id.run do
  let mut masks := Array.replicate 131072 0
  for f in [:fs.size] do
    for v in fs[f]! do
      masks := masks.modify v (fun m => m ||| 2^(cs.getD f 17))
  return masks

def sectorCornerCheck (fs : Array Face) (cs masks : Array Nat) : Bool :=
  (Array.range fs.size).all fun f => (Array.range 4).all fun i =>
    let v := (fs.getD f #[]).getD i 0
    v < 131072 && (masks.getD v 0).testBit (cs.getD f 17)

def sectorBoundaryTriangle (fs : Array Face) (k : Fin 17) (j : Fin 34) : Nat :=
  let f := (sectorBoundaryFaces.getD k.val #[]).getD j.val fs.size
  let a := meridianBoundaryLabel k (Coordinates.cyclicNext k) j
  let b := meridianBoundaryLabel k (Coordinates.cyclicNext k) (Coordinates.cyclicNext j)
  4*f + (Array.range 4).findIdx (fun i =>
    let u := (fs.getD f #[]).getD i 0
    let v := (fs.getD f #[]).getD ((i+1)%4) 0
    (u == a && v == b) || (u == b && v == a))

def sectorBoundaryRows : Array (Array Nat) := Array.ofFn fun k : Fin 17 =>
  Array.ofFn (meridianBoundaryLabel k (Coordinates.cyclicNext k))

/-- Shared coordinates of a triangle with any other color lie on one of the
34 boundary edges of its own sector. This is only a finite support statement. -/
def sectorOverlapCheck (fs : Array Face) (cs masks : Array Nat) : Bool :=
  let rows := sectorBoundaryRows
  (Array.range fs.size).all fun f => (Array.range 4).all fun i =>
    let u := (fs.getD f #[]).getD i 0
    let v := (fs.getD f #[]).getD ((i+1)%4) 0
    let k := cs.getD f 17
    let row := rows.getD k #[]
    (Array.range 17).all fun l => l == k || (Array.range 34).any fun j =>
      let a := row.getD j 0
      let b := row.getD ((j+1)%34) 0
      (!(masks.getD u 0).testBit l || u == a || u == b) &&
      (!(masks.getD v 0).testBit l || v == a || v == b)

def sectorDualCheck (fs : Array Face) (g : Graph) : Bool :=
  g.size == fs.size && (Array.range fs.size).all fun f => (g.getD f #[]).all fun h =>
    h < fs.size && (Array.range 4).any fun i => (Array.range 4).any fun j =>
      (fs.getD f #[]).getD i 0 == (fs.getD h #[]).getD j 0

def suppliedSectorMasks : Array Nat := sectorVertexMasks suppliedModel.oriented suppliedSectorColors

theorem sector_colors_verified : sectorColorCheck suppliedModel.oriented suppliedSectorColors = true := by
  native_decide

theorem sector_corners_verified :
    sectorCornerCheck suppliedModel.oriented suppliedSectorColors suppliedSectorMasks = true := by
  native_decide

theorem sector_overlaps_verified :
    sectorOverlapCheck suppliedModel.oriented suppliedSectorColors suppliedSectorMasks = true := by
  native_decide

theorem sector_boundary_verified : ∀ k j,
    let t := sectorBoundaryTriangle suppliedModel.oriented k j
    let a := meridianBoundaryLabel k (Coordinates.cyclicNext k) j
    let b := meridianBoundaryLabel k (Coordinates.cyclicNext k) (Coordinates.cyclicNext j)
    t < 4 * suppliedModel.oriented.size ∧ suppliedSectorColors.getD (t/4) 17 = k.val ∧
    ((LinkProof.triangleVertex suppliedModel.oriented 131072 t 1 = a ∧
      LinkProof.triangleVertex suppliedModel.oriented 131072 t 2 = b) ∨
     (LinkProof.triangleVertex suppliedModel.oriented 131072 t 1 = b ∧
      LinkProof.triangleVertex suppliedModel.oriented 131072 t 2 = a)) := by
  native_decide

theorem sector_dual_verified : sectorDualCheck suppliedModel.oriented suppliedModel.dual = true := by
  native_decide

theorem sector_connected_verified : ∀ k : Fin 17,
    GraphProof.connectedCheck suppliedModel.dual
      (fun f => suppliedSectorColors.getD f 17 == k.val) = true := by
  native_decide

theorem sector_face_counts_verified : ∀ k : Fin 17,
    (suppliedSectorColors.filter (· == k.val)).size = 7710 := by
  native_decide

end Venn17.Topology
