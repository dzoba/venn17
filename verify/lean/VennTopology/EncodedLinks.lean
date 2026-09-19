import VennTopology.LinkCircles
import VennTopology.LocalGeometry

noncomputable section
namespace Venn17.Topology

open Set
open scoped Classical
local instance : DecidableEq Nat := Classical.decEq _

/-- The same triangulation, using contiguous natural-number labels for region
vertices and quadrilateral centers. -/
def encodedCells (fs : Array Face) (n : Nat) (t : Fin (4*fs.size)) : Finset Nat :=
  {LinkProof.triangleVertex fs n t.val 0,
   LinkProof.triangleVertex fs n t.val 1,
   LinkProof.triangleVertex fs n t.val 2}

def triangleDart (fs : Array Face) (t : Fin (4*fs.size)) (j : Fin 3) : Fin (12*fs.size) :=
  ⟨3*t.val+j.val, by omega⟩

theorem triangleDart_owner (fs : Array Face) (n : Nat) (t : Fin (4*fs.size)) (j : Fin 3) :
    LinkProof.owner fs n (triangleDart fs t j).val = LinkProof.triangleVertex fs n t.val j.val := by
  have hdiv : (3*t.val+j.val)/3 = t.val := by omega
  have hmod : (3*t.val+j.val)%3 = j.val := by omega
  simp only [triangleDart, LinkProof.owner, hdiv, hmod]

theorem triangleDart_tail (fs : Array Face) (n : Nat) (t : Fin (4*fs.size)) (j : Fin 3) :
    LinkProof.tail fs n (triangleDart fs t j).val =
      LinkProof.triangleVertex fs n t.val ((j.val+1)%3) := by
  have hdiv : (3*t.val+j.val)/3 = t.val := by omega
  have hmod : (3*t.val+j.val+1)%3 = (j.val+1)%3 := by omega
  simp only [triangleDart, LinkProof.tail, hdiv, hmod]

theorem triangleDart_head (fs : Array Face) (n : Nat) (t : Fin (4*fs.size)) (j : Fin 3) :
    LinkProof.head fs n (triangleDart fs t j).val =
      LinkProof.triangleVertex fs n t.val ((j.val+2)%3) := by
  have hdiv : (3*t.val+j.val)/3 = t.val := by omega
  have hmod : (3*t.val+j.val+2)%3 = (j.val+2)%3 := by omega
  simp only [triangleDart, LinkProof.head, hdiv, hmod]

theorem triangleDart_surjective (fs : Array Face) (d : Fin (12*fs.size)) :
    ∃ t j, triangleDart fs t j = d := by
  refine ⟨⟨d.val/3, by omega⟩, ⟨d.val%3, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [triangleDart]
  omega

theorem encodedCell_erase (fs : Array Face) (n : Nat)
    (ht : ∀ t : Fin (4*fs.size), Function.Injective
      (fun j : Fin 3 => LinkProof.triangleVertex fs n t.val j.val))
    (t : Fin (4*fs.size)) (j : Fin 3) :
    (encodedCells fs n t).erase (LinkProof.owner fs n (triangleDart fs t j).val) =
      {LinkProof.tail fs n (triangleDart fs t j).val,
       LinkProof.head fs n (triangleDart fs t j).val} := by
  have h01 : LinkProof.triangleVertex fs n t.val 0 ≠ LinkProof.triangleVertex fs n t.val 1 :=
    fun h => (by decide : (0 : Fin 3) ≠ 1) (ht t h)
  have h02 : LinkProof.triangleVertex fs n t.val 0 ≠ LinkProof.triangleVertex fs n t.val 2 :=
    fun h => (by decide : (0 : Fin 3) ≠ 2) (ht t h)
  have h12 : LinkProof.triangleVertex fs n t.val 1 ≠ LinkProof.triangleVertex fs n t.val 2 :=
    fun h => (by decide : (1 : Fin 3) ≠ 2) (ht t h)
  rw [triangleDart_owner, triangleDart_tail, triangleDart_head]
  fin_cases j <;> ext a <;>
    simp [encodedCells] <;> grind

theorem encoded_link_eq_dartLink (fs : Array Face) (n v : Nat)
    (ht : ∀ t : Fin (4*fs.size), Function.Injective
      (fun j : Fin 3 => LinkProof.triangleVertex fs n t.val j.val)) :
    Coordinates.link (encodedCells fs n) v = dartLink fs n v := by
  ext x
  simp only [Coordinates.link, dartLink, mem_iUnion]
  constructor
  · rintro ⟨t, hv, hx⟩
    have hv' : ∃ j : Fin 3, LinkProof.triangleVertex fs n t.val j.val = v := by
      simp only [encodedCells, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with h | h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
    obtain ⟨j, hj⟩ := hv'
    have ho : LinkProof.owner fs n (triangleDart fs t j).val = v := by rw [triangleDart_owner, hj]
    refine ⟨triangleDart fs t j, ho, ?_⟩
    rw [← ho, encodedCell_erase fs n ht] at hx
    simpa [Coordinates.simplex, image_insert_eq, image_singleton, convexHull_pair] using hx
  · rintro ⟨d, ho, hx⟩
    obtain ⟨t,j,rfl⟩ := triangleDart_surjective fs d
    refine ⟨t, ?_, ?_⟩
    · rw [← ho, triangleDart_owner]
      fin_cases j <;> simp [encodedCells]
    · rw [← ho, encodedCell_erase fs n ht]
      simpa [Coordinates.simplex, image_insert_eq, image_singleton, convexHull_pair] using hx

def triangleFace (fs : Array Face) (t : Fin (4*fs.size)) : Fin fs.size :=
  ⟨t.val/4, by omega⟩

def triangleCorner (fs : Array Face) (t : Fin (4*fs.size)) : Fin 4 :=
  ⟨t.val%4, by omega⟩

theorem triangleVertex_zero (fs : Array Face) (n : Nat) (t : Fin (4*fs.size)) :
    LinkProof.triangleVertex fs n t.val 0 = n+(triangleFace fs t).val := by
  simp [LinkProof.triangleVertex, triangleFace]

theorem triangleVertex_one (fs : Array Face) (n : Nat) (t : Fin (4*fs.size)) :
    LinkProof.triangleVertex fs n t.val 1 =
      (quadOfFaces fs).corner (triangleFace fs t) (triangleCorner fs t) := by
  simp [LinkProof.triangleVertex, quadOfFaces, triangleFace, triangleCorner,
    Array.getD, getElem!_def, getElem?_def, (show t.val/4 < fs.size by omega)]
  split <;> rfl

theorem triangleVertex_two (fs : Array Face) (n : Nat) (t : Fin (4*fs.size)) :
    LinkProof.triangleVertex fs n t.val 2 =
      (quadOfFaces fs).corner (triangleFace fs t) (Quad.next (triangleCorner fs t)) := by
  simp [LinkProof.triangleVertex, quadOfFaces, triangleFace, triangleCorner, Quad.next,
    Array.getD, getElem!_def, getElem?_def, (show t.val/4 < fs.size by omega)]
  split <;> rfl

theorem triangleVertices_injective (fs : Array Face) (n : Nat)
    (hc : cornersCheck fs n = true) (hd : distinctCornersCheck fs = true)
    (t : Fin (4*fs.size)) : Function.Injective
      (fun j : Fin 3 => LinkProof.triangleVertex fs n t.val j.val) := by
  have h1 := cornersCheck_sound fs n hc (triangleFace fs t) (triangleCorner fs t)
  have h2 := cornersCheck_sound fs n hc (triangleFace fs t) (Quad.next (triangleCorner fs t))
  have hne := Quad.next_ne (triangleCorner fs t)
  have hi := distinctCornersCheck_sound fs hd (triangleFace fs t)
  have h12 : (quadOfFaces fs).corner (triangleFace fs t) (triangleCorner fs t) ≠
      (quadOfFaces fs).corner (triangleFace fs t) (Quad.next (triangleCorner fs t)) :=
    fun h => hne (hi h).symm
  intro j k he
  fin_cases j <;> fin_cases k <;>
    simp only [triangleVertex_zero, triangleVertex_one, triangleVertex_two] at he ⊢ <;>
    first | rfl | omega

end Venn17.Topology
