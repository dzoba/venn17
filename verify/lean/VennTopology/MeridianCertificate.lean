import VennTopology.MeridianData
import VennTopology.LinkData
import VennTopology.CyclicPolygon

/-! Finite witnesses for a system of pole-to-pole meridians. These assertions
only concern labels and triangle incidences; the geometric conclusions are
proved separately. -/
namespace Venn17.Topology

def meridianLabel (k : Fin 17) (j : Fin 18) : Nat :=
  steps regionStep k.val (meridianSeed.getD j.val 0)

/-- Go north along meridian `k`, then south along meridian `l`. -/
def meridianBoundaryLabel (k l : Fin 17) (j : Fin 34) : Nat :=
  if h : j.val < 18 then meridianLabel k ⟨j.val, h⟩
  else meridianLabel l ⟨34 - j.val, by omega⟩

def meridianBoundaryTriangle (fs : Array Face) (k l : Fin 17) (j : Fin 34) : Nat :=
  let f := if j.val < 17 then (meridianFaceRows.getD k.val #[]).getD j.val 0
    else (meridianFaceRows.getD l.val #[]).getD (33 - j.val) 0
  let a := meridianBoundaryLabel k l j
  let b := meridianBoundaryLabel k l (Coordinates.cyclicNext j)
  4 * f + (Array.range 4).findIdx (fun i =>
    let u := (fs.getD f #[]).getD i 0
    let v := (fs.getD f #[]).getD ((i+1)%4) 0
    (u == a && v == b) || (u == b && v == a))

theorem meridian_labels_verified :
    (∀ k, meridianLabel k 0 = 0 ∧ meridianLabel k 17 = 131071) ∧
    (∀ k j, meridianLabel k j < 131072 ∧
      regionStep (meridianLabel k j) = meridianLabel (Coordinates.cyclicNext k) j) ∧
    (∀ k l, k ≠ l → Function.Injective (meridianBoundaryLabel k l)) := by
  native_decide

theorem meridian_triangles_verified : ∀ k l j,
    let t := meridianBoundaryTriangle suppliedModel.oriented k l j
    let a := meridianBoundaryLabel k l j
    let b := meridianBoundaryLabel k l (Coordinates.cyclicNext j)
    t < 4 * suppliedModel.oriented.size ∧
    ((LinkProof.triangleVertex suppliedModel.oriented 131072 t 1 = a ∧
      LinkProof.triangleVertex suppliedModel.oriented 131072 t 2 = b) ∨
     (LinkProof.triangleVertex suppliedModel.oriented 131072 t 1 = b ∧
      LinkProof.triangleVertex suppliedModel.oriented 131072 t 2 = a)) := by
  native_decide

end Venn17.Topology
