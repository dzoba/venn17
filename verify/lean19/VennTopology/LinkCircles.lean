import VennTopology.LabeledPolygon
import VennTopology.LinkCertificate

noncomputable section
namespace Venn19.Topology

open Set
open scoped Classical

/-- The geometric link described by every incident triangle dart, in real
coordinates indexed by the region and face-center numbers. -/
def dartLink (fs : Array Face) (n v : Nat) : Set (Coordinates.Point Nat) :=
  ⋃ d : Fin (12*fs.size), ⋃ (_ : LinkProof.owner fs n d.val = v),
    segment ℝ (Coordinates.vertex (LinkProof.tail fs n d.val))
      (Coordinates.vertex (LinkProof.head fs n d.val))

def rowVertices (fs : Array Face) (n : Nat) (row : Array Nat) (k : Fin row.size) : Nat :=
  LinkProof.tail fs n (row.getD k.val 0)

theorem dartLink_eq_polygon (fs : Array Face) (n v : Nat) (row : Array Nat)
    (hr : LinkProof.rowCheck fs n v row = true)
    (hc : ∀ d : Fin (12*fs.size), LinkProof.owner fs n d.val = v →
      ∃ k : Fin row.size, row.getD k.val 0 = d.val) :
    dartLink fs n v = Coordinates.labeledPolygon (rowVertices fs n row) := by
  obtain ⟨_, _, hs⟩ := LinkProof.rowCheck_sound fs n v row hr
  ext x
  simp only [dartLink, Coordinates.labeledPolygon, mem_iUnion]
  constructor
  · rintro ⟨d, hd, hx⟩
    obtain ⟨k, hk⟩ := hc d hd
    refine ⟨k, ?_⟩
    have he := (hs k).2.2
    rw [hk] at he
    simpa only [rowVertices, hk, he, Coordinates.cyclicNext] using hx
  · rintro ⟨k, hk⟩
    obtain ⟨hb, ho, he⟩ := hs k
    refine ⟨⟨row.getD k.val 0, hb⟩, ho, ?_⟩
    simpa only [he, rowVertices, Coordinates.cyclicNext] using hk

/-- A checked, complete cyclic dart enumeration supplies an actual circle
homeomorphism onto the union of its geometric link segments. -/
def dartLinkHomeomorph (fs : Array Face) (n v : Nat) (row : Array Nat)
    (hr : LinkProof.rowCheck fs n v row = true)
    (hc : ∀ d : Fin (12*fs.size), LinkProof.owner fs n d.val = v →
      ∃ k : Fin row.size, row.getD k.val 0 = d.val) :
    Circle ≃ₜ dartLink fs n v :=
  (Coordinates.labeledPolygonHomeomorph (rowVertices fs n row)
    (LinkProof.rowCheck_sound fs n v row hr).2.1
    (LinkProof.rowCheck_sound fs n v row hr).1).trans
    (Homeomorph.setCongr (dartLink_eq_polygon fs n v row hr hc).symm)

attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars

/-- For every one of the 1048574 certified vertices, its complete dart link
is geometrically a circle, not merely a graph with a cyclic-order flag. -/
def supplied_dart_link_circle (v : Fin suppliedLinkStars.size) :
    Circle ≃ₜ dartLink suppliedModel.oriented 524288 v.val :=
  dartLinkHomeomorph _ _ _ _ (supplied_link_rows.2 v) (by
    intro d hd
    obtain ⟨k, hk⟩ := (every_triangle_dart_occurs d).2
    refine ⟨⟨k.val, by simpa only [hd] using k.isLt⟩, ?_⟩
    change (suppliedLinkStars.getD v.val #[]).getD k.val 0 = d.val
    rw [← hd]
    exact hk)

#print axioms supplied_dart_link_circle

end Venn19.Topology
