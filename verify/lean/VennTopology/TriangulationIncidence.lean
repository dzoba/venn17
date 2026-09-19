import VennTopology.FiniteTriangulation

noncomputable section
namespace Venn17.Topology
open Set
open scoped Classical
open Coordinates
open Coordinates.FiniteCoordinates
open LeanEval.Topology.ClassificationOfSurfaces
local instance triangulationIncidenceDecidableEq {I : Type*} : DecidableEq I := Classical.decEq _
local instance triangulationIncidenceFinDecidableEq (N : Nat) : DecidableEq (Fin N) := Classical.decEq _

/-- An edge of a triangle has one of its two orientations among that
triangle's own three darts. -/
theorem triangle_pair_internal_dart (fs : Array Face) (n : Nat)
    (t : Fin (4 * fs.size)) {a b : Nat} (ha : a ∈ encodedCells fs n t)
    (hb : b ∈ encodedCells fs n t) (hab : a ≠ b) :
    ∃ j : Fin 3,
      (LinkProof.owner fs n (triangleDart fs t j).val = a ∧
       LinkProof.tail fs n (triangleDart fs t j).val = b) ∨
      (LinkProof.owner fs n (triangleDart fs t j).val = b ∧
       LinkProof.tail fs n (triangleDart fs t j).val = a) := by
  simp only [triangleDart_owner, triangleDart_tail]
  simp only [encodedCells, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals first
    | exact False.elim (hab rfl)
    | exact ⟨0, Or.inl ⟨rfl, rfl⟩⟩
    | exact ⟨1, Or.inl ⟨rfl, rfl⟩⟩
    | exact ⟨2, Or.inl ⟨rfl, rfl⟩⟩
    | exact ⟨0, Or.inr ⟨rfl, rfl⟩⟩
    | exact ⟨1, Or.inr ⟨rfl, rfl⟩⟩
    | exact ⟨2, Or.inr ⟨rfl, rfl⟩⟩

theorem triangleDart_triangle_injective (fs : Array Face)
    {t u : Fin (4 * fs.size)} {j k : Fin 3}
    (h : triangleDart fs t j = triangleDart fs u k) : t = u := by
  have h' := congrArg Fin.val h
  dsimp only [triangleDart] at h'
  apply Fin.ext
  have := j.isLt
  have := k.isLt
  omega

/-- Unique directed-edge darts bound every geometric edge's triangle valence. -/
theorem encoded_edge_valence_le_two (fs : Array Face) (n : Nat) (stars : LinkProof.Stars)
    (hr : LinkProof.rowsCheck fs n stars = true) (hc : LinkProof.coverageCheck fs n stars = true)
    {a b : Nat} (hab : a ≠ b) :
    (Finset.univ.filter (fun t : Fin (4 * fs.size) =>
      a ∈ encodedCells fs n t ∧ b ∈ encodedCells fs n t)).card ≤ 2 := by
  classical
  let s := Finset.univ.filter (fun t : Fin (4 * fs.size) =>
    a ∈ encodedCells fs n t ∧ b ∈ encodedCells fs n t)
  by_cases hs : s.Nonempty
  · obtain ⟨t, ht⟩ := hs
    have ht' := (Finset.mem_filter.mp ht).2
    obtain ⟨d, hda, hdb⟩ := triangle_pair_dart fs n stars hr hc t ht'.1 ht'.2 hab
    obtain ⟨e, hea, heb⟩ := dart_reverse_exists fs n stars hr hc d
    obtain ⟨u, j, rfl⟩ := triangleDart_surjective fs d
    obtain ⟨v, k, rfl⟩ := triangleDart_surjective fs e
    have hsub : s ⊆ {u, v} := by
      intro w hw
      have hw' := (Finset.mem_filter.mp hw).2
      obtain ⟨l, hl | hl⟩ := triangle_pair_internal_dart fs n w hw'.1 hw'.2 hab
      · have heq := dart_endpoints_injective fs n stars hr hc
          (Prod.ext (hl.1.trans hda.symm) (hl.2.trans hdb.symm))
        exact Finset.mem_insert.mpr (Or.inl (triangleDart_triangle_injective fs heq))
      · have heq := dart_endpoints_injective fs n stars hr hc
          (Prod.ext (hl.1.trans (hea.trans hdb).symm) (hl.2.trans (heb.trans hda).symm))
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
          (triangleDart_triangle_injective fs heq)))
    exact (Finset.card_le_card hsub).trans (by simpa using Finset.card_insert_le u {v})
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change s.card ≤ 2
    simp [he]

/-- The reverse dart lies in a different triangle, so every actual edge has
exactly two incident triangles. In particular there are no boundary edges. -/
theorem encoded_edge_valence_eq_two (fs : Array Face) (n : Nat) (stars : LinkProof.Stars)
    (hr : LinkProof.rowsCheck fs n stars = true) (hc : LinkProof.coverageCheck fs n stars = true)
    (ht : ∀ t : Fin (4 * fs.size), Function.Injective
      (fun j : Fin 3 => LinkProof.triangleVertex fs n t.val j.val))
    {a b : Nat} (hab : a ≠ b) (hex : ∃ t, a ∈ encodedCells fs n t ∧ b ∈ encodedCells fs n t) :
    (Finset.univ.filter (fun t : Fin (4 * fs.size) =>
      a ∈ encodedCells fs n t ∧ b ∈ encodedCells fs n t)).card = 2 := by
  classical
  apply le_antisymm (encoded_edge_valence_le_two fs n stars hr hc hab)
  obtain ⟨t, ha, hb⟩ := hex
  obtain ⟨d, hda, hdb⟩ := triangle_pair_dart fs n stars hr hc t ha hb hab
  obtain ⟨e, hea, heb⟩ := dart_reverse_exists fs n stars hr hc d
  obtain ⟨u, j, rfl⟩ := triangleDart_surjective fs d
  obtain ⟨v, k, rfl⟩ := triangleDart_surjective fs e
  have huv : u ≠ v := by
    intro heq
    subst v
    rw [triangleDart_owner, triangleDart_tail] at hea heb
    have hj := ht u (a₁ := j) (a₂ := ⟨(k.val + 1) % 3, by omega⟩) heb.symm
    have hk := ht u (a₁ := k) (a₂ := ⟨(j.val + 1) % 3, by omega⟩) hea
    have hj' := congrArg Fin.val hj
    have hk' := congrArg Fin.val hk
    dsimp only at hj' hk'
    have := j.isLt
    have := k.isLt
    omega
  have hm (w : Fin (4 * fs.size)) (l : Fin 3) :
      LinkProof.owner fs n (triangleDart fs w l).val ∈ encodedCells fs n w ∧
      LinkProof.tail fs n (triangleDart fs w l).val ∈ encodedCells fs n w := by
    rw [triangleDart_owner, triangleDart_tail]
    fin_cases l <;> simp [encodedCells]
  have hu : a ∈ encodedCells fs n u ∧ b ∈ encodedCells fs n u := by
    simpa only [hda, hdb] using hm u j
  have hv : a ∈ encodedCells fs n v ∧ b ∈ encodedCells fs n v := by
    have h := hm v k
    rw [hea, heb, hda, hdb] at h
    exact h.symm
  have hsub : {u, v} ⊆ Finset.univ.filter (fun t : Fin (4 * fs.size) =>
      a ∈ encodedCells fs n t ∧ b ∈ encodedCells fs n t) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
    · obtain rfl := Finset.mem_singleton.mp hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
  simpa only [Finset.card_pair huv] using Finset.card_le_card hsub

/-- Connected geometric vertex links imply the combinatorial connectivity
required by the classification library. All adjacency steps stay at the
chosen vertex. -/
theorem strongVertexStarConnected_of_links {I T : Type*} [Fintype I] [Fintype T]
    (cells : T → Finset I) (hc : ∀ t, (cells t).card = 3)
    (hl : ∀ v, IsPreconnected (Coordinates.link cells v)) :
    TriangleFamily.IsStrongVertexStarConnected (geometricFaces cells) := by
  classical
  intro v f g hvf hvg
  let L := {f : TriangleFamily.Face (geometricFaces cells) // v ∈ f.val}
  let s : L → Set (Point I) := fun f => simplex (f.val.val.erase v)
  have hcard (f : TriangleFamily.Face (geometricFaces cells)) : f.val.card = 3 := by
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp f.property
    exact ht ▸ hc t
  have hs : (⋃ f : L, s f) = Coordinates.link cells v := by
    ext x
    constructor
    · intro hx
      obtain ⟨f, hf⟩ := mem_iUnion.mp hx
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp f.val.property
      exact mem_iUnion₂.mpr ⟨t, ht ▸ f.property, by simpa only [s, ht] using hf⟩
    · intro hx
      obtain ⟨t, hvt, ht⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨⟨⟨cells t, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩,
        hvt⟩, ht⟩
  have hclosed (f : L) : IsClosed (s f) := by
    change IsClosed (simplex (f.val.val.erase v))
    rw [simplex_eq_geometricFace]
    exact LeanEval.Topology.ClassificationOfSurfaces.GeometricFace.isClosed _
  have hne (f : L) : (s f).Nonempty := by
    have he : (f.val.val.erase v).card = 2 := by
      rw [Finset.card_erase_of_mem f.property, hcard]
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (f.val.val.erase v).card)
    exact ⟨vertex w, vertex_mem_simplex hw⟩
  have hpre : IsPreconnected (⋃ f : L, s f) := hs.symm ▸ hl v
  have hchain := hpre.transGen_of_finite_iUnion hclosed
    (⟨f, hvf⟩ : L) (⟨g, hvg⟩ : L) (hne _) (hne _)
  have hadj {a b : L} (h : (s a ∩ s b).Nonempty) :
      TriangleFamily.FaceAdjacentAtVertex (geometricFaces cells) v a.val b.val := by
    obtain ⟨x, hx, hy⟩ := h
    obtain ⟨w, hw, hp⟩ := simplex_has_positive_coordinate hx
    have hw' : w ∈ b.val.val.erase v := by
      by_contra hn
      exact (ne_of_gt hp) (simplex_zero hy hn)
    have hwv := (Finset.mem_erase.mp hw).1
    refine ⟨{v, w}, by simp [Ne.symm hwv], by simp, ?_, ?_⟩
    · exact Finset.insert_subset_iff.mpr ⟨a.property,
        Finset.singleton_subset_iff.mpr (Finset.mem_of_mem_erase hw)⟩
    · exact Finset.insert_subset_iff.mpr ⟨b.property,
        Finset.singleton_subset_iff.mpr (Finset.mem_of_mem_erase hw')⟩
  have hmap {a b : L} (h : Relation.TransGen (fun a b => (s a ∩ s b).Nonempty) a b) :
      Relation.ReflTransGen (TriangleFamily.FaceAdjacentAtVertex (geometricFaces cells) v)
        a.val b.val := by
    induction h with
    | single h => exact Relation.ReflTransGen.single (hadj h)
    | tail _ h ih => exact ih.tail (hadj h)
  exact hmap hchain

theorem finite_encoded_edge_valence_le_two (fs : Array Face) (n N : Nat)
    (stars : LinkProof.Stars) (hr : LinkProof.rowsCheck fs n stars = true)
    (hc : LinkProof.coverageCheck fs n stars = true) (e : Finset (Fin N)) (he : e.card = 2) :
    ((geometricFaces (fun t => cell N (encodedCells fs n t))).filter
      (fun f => e ⊆ f)).card ≤ 2 := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he
  let triangles := Finset.univ.filter (fun t : Fin (4 * fs.size) =>
    a.val ∈ encodedCells fs n t ∧ b.val ∈ encodedCells fs n t)
  have hsub : ((geometricFaces (fun t => cell N (encodedCells fs n t))).filter
      (fun f => {a, b} ⊆ f)) ⊆ triangles.image (fun t => cell N (encodedCells fs n t)) := by
    intro f hf
    obtain ⟨hf, habf⟩ := Finset.mem_filter.mp hf
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
    refine Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact ⟨mem_cell.mp (habf (by simp)), mem_cell.mp (habf (by simp))⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans
    (encoded_edge_valence_le_two fs n stars hr hc (fun h => hab (Fin.ext h))))

theorem finite_pair_incidence_card {T : Type*} [Fintype T] (cells : T → Finset Nat)
    (N : Nat) (hb : ∀ t i, i ∈ cells t → i < N) (hi : Function.Injective cells)
    (a b : Fin N) :
    ((geometricFaces (fun t => cell N (cells t))).filter
      (fun f => {a, b} ⊆ f)).card =
    (Finset.univ.filter (fun t => a.val ∈ cells t ∧ b.val ∈ cells t)).card := by
  classical
  have hinj : Function.Injective (fun t => cell N (cells t)) := by
    intro t u h
    apply hi
    have hh := congrArg (Finset.map Fin.valEmbedding) h
    simpa only [map_cell (hb _)] using hh
  have hf : ((geometricFaces (fun t => cell N (cells t))).filter
      (fun f => {a, b} ⊆ f)) =
      (Finset.univ.filter (fun t => a.val ∈ cells t ∧ b.val ∈ cells t)).image
        (fun t => cell N (cells t)) := by
    ext f
    constructor
    · intro h
      obtain ⟨hf, hab⟩ := Finset.mem_filter.mp h
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
      exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        mem_cell.mp (hab (by simp)), mem_cell.mp (hab (by simp))⟩, rfl⟩
    · intro h
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      have hab := (Finset.mem_filter.mp ht).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩, ?_⟩
      exact Finset.insert_subset_iff.mpr ⟨mem_cell.mpr hab.1,
        Finset.singleton_subset_iff.mpr (mem_cell.mpr hab.2)⟩
  rw [hf, Finset.card_image_of_injective _ hinj]

attribute [local irreducible] suppliedModel suppliedFaces suppliedLinkStars suppliedCurvePolygons

theorem diagram_encoded_link_preconnected (v : Fin (131072 + suppliedModel.oriented.size)) :
    IsPreconnected (Coordinates.link (encodedCells suppliedModel.oriented 131072) v.val) := by
  rw [encoded_link_eq_dartLink _ _ _ (triangleVertices_injective _ _
    supplied_corners_bounded supplied_distinct_corners_verified)]
  let e := supplied_dart_link_circle ⟨v.val, by simpa only [supplied_link_rows.1] using v.isLt⟩
  have h := isPreconnected_range (continuous_subtype_val.comp e.continuous)
  have he : Set.range (fun z : Circle => (e z).val) =
      dartLink suppliedModel.oriented 131072 v.val := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (e z).property
    · intro hx
      obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
      exact ⟨z, congrArg Subtype.val hz⟩
  exact he ▸ h

theorem diagram_finite_vertex_stars_connected :
    TriangleFamily.IsStrongVertexStarConnected diagramFiniteTriangulation.faces := by
  apply strongVertexStarConnected_of_links
    (fun t => cell (131072 + suppliedModel.oriented.size)
      (encodedCells suppliedModel.oriented 131072 t))
  · intro t
    exact (cell_card (diagram_cells_bounded t)).trans (diagram_encoded_cell_card t)
  · intro v
    rw [← restrict_link_image _ _ diagram_cells_bounded]
    exact (diagram_encoded_link_preconnected v).image _ (continuous_restrict _).continuousOn

theorem diagram_finite_surface_incidence : diagramFiniteTriangulation.SurfaceIncidence := by
  refine ⟨diagramFiniteTriangulation.faces_nonempty, ?_, ?_⟩
  · intro e he
    exact finite_encoded_edge_valence_le_two suppliedModel.oriented 131072
      (131072 + suppliedModel.oriented.size) suppliedLinkStars
      (Bool.and_eq_true_iff.mp supplied_link_stars_verified).1
      (Bool.and_eq_true_iff.mp supplied_link_stars_verified).2 e
      (diagramFiniteTriangulation.card_of_mem_edges he)
  · exact diagramFiniteTriangulation.faces_isDualConnected_of_isStrongVertexStarConnected
      diagram_finite_vertex_stars_connected

theorem diagram_finite_no_boundary_edges (e : diagramFiniteTriangulation.Edge) :
    (diagramFiniteTriangulation.faces.filter (fun f => e.val ⊆ f)).card = 2 := by
  classical
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp (diagramFiniteTriangulation.edge_card e)
  have hex : ∃ t, a.val ∈ encodedCells suppliedModel.oriented 131072 t ∧
      b.val ∈ encodedCells suppliedModel.oriented 131072 t := by
    obtain ⟨f, hf, hef⟩ := Finset.mem_biUnion.mp e.property
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
    have hs := (Finset.mem_powersetCard.mp hef).1
    rw [he] at hs
    exact ⟨t, mem_cell.mp (hs (by simp)), mem_cell.mp (hs (by simp))⟩
  rw [he]
  apply (finite_pair_incidence_card _ _ diagram_cells_bounded
    (encoded_cells_injective _ _ supplied_corners_bounded supplied_distinct_corners_verified) a b).trans
  exact encoded_edge_valence_eq_two _ _ suppliedLinkStars
    (Bool.and_eq_true_iff.mp supplied_link_stars_verified).1
    (Bool.and_eq_true_iff.mp supplied_link_stars_verified).2
    (triangleVertices_injective _ _ supplied_corners_bounded supplied_distinct_corners_verified)
    (fun h => hab (Fin.ext h)) hex

theorem diagram_classification_input_verified :
    diagramFiniteTriangulation.SurfaceIncidence ∧
    (∀ e : diagramFiniteTriangulation.Edge,
      (diagramFiniteTriangulation.faces.filter (fun f => e.val ⊆ f)).card = 2) ∧
    (Fintype.card diagramFiniteTriangulation.Vertex : ℤ) -
      diagramFiniteTriangulation.edges.card + diagramFiniteTriangulation.faces.card = 2 :=
  ⟨diagram_finite_surface_incidence, diagram_finite_no_boundary_edges,
    diagram_finite_euler_characteristic⟩

#print axioms encoded_edge_valence_le_two
#print axioms encoded_edge_valence_eq_two
#print axioms strongVertexStarConnected_of_links
#print axioms diagram_finite_surface_incidence
#print axioms diagram_classification_input_verified
end Venn17.Topology
