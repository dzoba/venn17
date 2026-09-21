import VennTopology.MeridianData
import VennTopology.LinkData
import VennTopology.CyclicPolygon

/-! Finite witnesses for a system of pole-to-pole meridians. These assertions
only concern labels and triangle incidences; the geometric conclusions are
proved separately. -/
namespace Venn19.Topology

def meridianLabel (k : Fin 19) (j : Fin 20) : Nat :=
  steps regionStep k.val (meridianSeed.getD j.val 0)

/-- Go north along meridian `k`, then south along meridian `l`. -/
def meridianBoundaryLabel (k l : Fin 19) (j : Fin 38) : Nat :=
  if h : j.val < 20 then meridianLabel k ⟨j.val, h⟩
  else meridianLabel l ⟨38 - j.val, by omega⟩

def meridianBoundaryTriangle (fs : Array Face) (k l : Fin 19) (j : Fin 38) : Nat :=
  let f := if j.val < 19 then (meridianFaceRows.getD k.val #[]).getD j.val 0
    else (meridianFaceRows.getD l.val #[]).getD (37 - j.val) 0
  let a := meridianBoundaryLabel k l j
  let b := meridianBoundaryLabel k l (Coordinates.cyclicNext j)
  4 * f + (Array.range 4).findIdx (fun i =>
    let u := (fs.getD f #[]).getD i 0
    let v := (fs.getD f #[]).getD ((i+1)%4) 0
    (u == a && v == b) || (u == b && v == a))

theorem meridian_labels_verified :
    (∀ k, meridianLabel k 0 = 0 ∧ meridianLabel k 19 = 524287) ∧
    (∀ k j, meridianLabel k j < 524288 ∧
      regionStep (meridianLabel k j) = meridianLabel (Coordinates.cyclicNext k) j) ∧
    (∀ k l, k ≠ l → Function.Injective (meridianBoundaryLabel k l)) := by
  native_decide

theorem meridian_triangles_verified : ∀ k l j,
    let t := meridianBoundaryTriangle suppliedModel.oriented k l j
    let a := meridianBoundaryLabel k l j
    let b := meridianBoundaryLabel k l (Coordinates.cyclicNext j)
    t < 4 * suppliedModel.oriented.size ∧
    ((LinkProof.triangleVertex suppliedModel.oriented 524288 t 1 = a ∧
      LinkProof.triangleVertex suppliedModel.oriented 524288 t 2 = b) ∨
     (LinkProof.triangleVertex suppliedModel.oriented 524288 t 1 = b ∧
      LinkProof.triangleVertex suppliedModel.oriented 524288 t 2 = a)) := by
  native_decide

end Venn19.Topology
