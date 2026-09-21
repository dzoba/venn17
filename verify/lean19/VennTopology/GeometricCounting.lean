import VennTopology.TriangulationCounts

noncomputable section
namespace Venn19.Topology
open Set

/-- A face of the actual geometric simplicial complex, with `k` vertices. -/
def GeometricFace {V F : Type*} (q : Quad V F) (k : Nat) :=
  {s : Finset (Quad.Ambient V F) // s ∈ q.complex.faces ∧ s.card = k}

def geometricFaceEquiv {V F : Type*} (q : Quad V F) (k : Nat) (hk : 0 < k) :
    CellFace (fun p : F × Fin 4 => q.triangleFinset p.1 p.2) k ≃ GeometricFace q k :=
  Equiv.subtypeEquivRight (fun s => by
    change (s.card = k ∧ ∃ p : F × Fin 4, s ⊆ q.triangleFinset p.1 p.2) ↔
      (s.Nonempty ∧ ∃ f j, s ⊆ q.triangleFinset f j) ∧ s.card = k
    constructor
    · rintro ⟨hc,⟨f,j⟩,hs⟩
      exact ⟨⟨Finset.card_pos.mp (hc ▸ hk),f,j,hs⟩,hc⟩
    · rintro ⟨⟨_,f,j,hs⟩,hc⟩
      exact ⟨hc,(f,j),hs⟩)

def labelGeometricFaceEquiv {V F : Type*} (q : Quad V F) (k : Nat) (hk : 0 < k) :
    CellFace q.cellLabels k ≃ GeometricFace q k := by
  classical
  let e : (V ⊕ F) ↪ Quad.Ambient V F := ⟨Quad.point,Quad.point_injective⟩
  have he : (fun p => (q.cellLabels p).map e) = (fun p : F × Fin 4 => q.triangleFinset p.1 p.2) := by
    funext p
    simp [Quad.cellLabels,Quad.triangleFinset,e]
  exact (cellFaceMapEquiv q.cellLabels e k).trans
    ((Equiv.cast (congrArg (fun cells => CellFace cells k) he)).trans (geometricFaceEquiv q k hk))

def encodedLabelFaceEquiv (fs : Array Face) (n : Nat) (hc : cornersCheck fs n = true) (k : Nat) :
    CellFace (encodedCells fs n) k ≃ CellFace (quadOfFaces fs).cellLabels k := by
  let q := quadOfFaces fs
  let e := Coordinates.labelEquiv n fs.size
  have h : ∀ s : Finset Nat, (∃ t, s ⊆ encodedCells fs n t) ↔
      ∃ p, s ⊆ (q.cellLabels p).map e.toEmbedding := by
    intro s
    constructor
    · rintro ⟨t,ht⟩
      exact ⟨(triangleFace fs t,triangleCorner fs t),cellLabels_encoded fs n hc t ▸ ht⟩
    · rintro ⟨p,hp⟩
      obtain ⟨t,he⟩ := triangleFaceCorner_surjective fs p
      subst p
      exact ⟨t,(cellLabels_encoded fs n hc t) ▸ hp⟩
  exact (cellFaceCongr (encodedCells fs n) (fun p => (q.cellLabels p).map e.toEmbedding) k h).trans
    (cellFaceMapEquiv q.cellLabels e.toEmbedding k).symm

/-- The combinatorial face counts refer to the very same geometric complex
whose realization was proved to be the constructed surface. -/
def encodedGeometricFaceEquiv (fs : Array Face) (n : Nat) (hc : cornersCheck fs n = true)
    (k : Nat) (hk : 0 < k) :
    CellFace (encodedCells fs n) k ≃ GeometricFace (quadOfFaces fs) k :=
  (encodedLabelFaceEquiv fs n hc k).trans (labelGeometricFaceEquiv (quadOfFaces fs) k hk)

theorem geometric_vertex_count (fs : Array Face) (n : Nat)
    (hc : cornersCheck fs n = true) (hcov : coverageCheck fs n = true) :
    Nat.card (GeometricFace (quadOfFaces fs) 1) = n+fs.size := by
  rw [← Nat.card_congr (encodedGeometricFaceEquiv fs n hc 1 (by decide))]
  exact encoded_vertex_count fs n hc hcov

theorem geometric_edge_count (fs : Array Face) (n : Nat) (stars : LinkProof.Stars)
    (hc : cornersCheck fs n = true) (hd : distinctCornersCheck fs = true)
    (hr : LinkProof.rowsCheck fs n stars = true) (hcov : LinkProof.coverageCheck fs n stars = true) :
    Nat.card (GeometricFace (quadOfFaces fs) 2) = 6*fs.size := by
  rw [← Nat.card_congr (encodedGeometricFaceEquiv fs n hc 2 (by decide))]
  exact encoded_edge_count fs n stars hr hcov (triangleVertices_injective fs n hc hd)

theorem geometric_triangle_count (fs : Array Face) (n : Nat)
    (hc : cornersCheck fs n = true) (hd : distinctCornersCheck fs = true) :
    Nat.card (GeometricFace (quadOfFaces fs) 3) = 4*fs.size := by
  rw [← Nat.card_congr (encodedGeometricFaceEquiv fs n hc 3 (by decide))]
  exact encoded_triangle_count fs n hc hd

theorem geometric_no_higher_faces {V F : Type*} (q : Quad V F) (k : Nat) (hk : 3 < k) :
    IsEmpty (GeometricFace q k) := by
  classical
  refine ⟨fun s => ?_⟩
  obtain ⟨_,f,j,hs⟩ := s.property.1
  have hle := Finset.card_le_card hs
  have ht : (q.triangleFinset f j).card ≤ 3 := by
    unfold Quad.triangleFinset
    exact le_trans (Finset.card_insert_le _ _) (by
      have h := Finset.card_insert_le (Quad.point (F := F) (.inl (q.corner f j))) {Quad.point (.inl (q.corner f (Quad.next j)))}
      simp only [Finset.card_singleton] at h
      omega)
  have hc := s.property.2
  omega

#print axioms encodedGeometricFaceEquiv
#print axioms geometric_edge_count
end Venn19.Topology
