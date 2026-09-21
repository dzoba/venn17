import VennTopology.SectorGeometry

/-! Soundness of the spanning-tree certificate: each closed sector is path
connected in the actual coordinate realization. -/
noncomputable section
namespace Venn19.Topology
open Set Coordinates
attribute [local irreducible] suppliedModel suppliedFaces suppliedSectorColors

theorem sector_dual_size : suppliedModel.dual.size = suppliedModel.oriented.size := by
  have h := sector_dual_verified
  simp only [sectorDualCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem sector_dual_edge (f : Fin suppliedModel.oriented.size) (g : Nat)
    (hg : g ∈ suppliedModel.dual[f.val]!) :
    ∃ hb : g < suppliedModel.oriented.size, ∃ i j : Fin 4,
      diagramQuad.corner f i = diagramQuad.corner ⟨g, hb⟩ j := by
  have h := sector_dual_verified
  simp only [sectorDualCheck, Bool.and_eq_true] at h
  have hf := Array.all_eq_true.mp h.2 f.val (by simp)
  simp only [Array.getElem_range] at hf
  have hm : g ∈ suppliedModel.dual.getD f.val #[] := by
    simpa only [Array.getElem!_eq_getD, show (default : Array Nat) = #[] from rfl] using hg
  have hh := Array.all_eq_true_iff_forall_mem.mp hf g hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
  obtain ⟨i, hi, hh'⟩ := Array.any_eq_true.mp hh.2
  obtain ⟨j, hj, he⟩ := Array.any_eq_true.mp hh'
  have hi' : i < 4 := by simpa using hi
  have hj' : j < 4 := by simpa using hj
  refine ⟨hh.1, ⟨i, hi'⟩, ⟨j, hj'⟩, ?_⟩
  simpa [diagramQuad, quadOfFaces, Array.getElem!_eq_getD,
    show (default : Array Nat) = #[] from rfl, show (default : Nat) = 0 from rfl, hh.1] using he

theorem sector_triangle_subset (k : Fin 19) (f : Fin suppliedModel.oriented.size)
    (hf : sectorColor f = k) (j : Fin 4) : diagramQuad.triangle f j ⊆ sectorSpace k := by
  intro x hx
  exact mem_iUnion.mpr ⟨f, mem_iUnion₂.mpr ⟨hf, j, hx⟩⟩

theorem sector_centers_joined (k : Fin 19) (f g : Fin suppliedModel.oriented.size)
    (hf : sectorColor f = k) (hg : sectorColor g = k) (i j : Fin 4)
    (he : diagramQuad.corner f i = diagramQuad.corner g j) :
    JoinedIn (sectorSpace k) (Quad.point (.inr f)) (Quad.point (.inr g)) := by
  have h1 := ((diagramQuad.triangle_pathConnected f i).joinedIn _
    (diagramQuad.center_mem_triangle f i) _ (diagramQuad.corner_mem_triangle f i)).mono
      (sector_triangle_subset k f hf i)
  have h2 := ((diagramQuad.triangle_pathConnected g j).joinedIn _
    (diagramQuad.corner_mem_triangle g j) _ (diagramQuad.center_mem_triangle g j)).mono
      (sector_triangle_subset k g hg j)
  rw [he] at h1
  exact h1.trans h2

theorem sector_walk_joined (k : Fin 19) {u v : Nat}
    (hw : GraphProof.Walk suppliedModel.dual (fun f => suppliedSectorColors.getD f 19 == k.val) u v)
    (hu : u < suppliedModel.oriented.size) (hv : v < suppliedModel.oriented.size) :
    JoinedIn (sectorSpace k) (Quad.point (.inr ⟨u, hu⟩)) (Quad.point (.inr ⟨v, hv⟩)) := by
  induction hw with
  | refl v ha =>
      apply JoinedIn.refl
      exact sector_triangle_subset k ⟨v, hv⟩ (Fin.ext (beq_iff_eq.mp ha)) 0
        (diagramQuad.center_mem_triangle _ _)
  | @step u v w ha hedge hw ih =>
      obtain ⟨hb, i, j, he⟩ := sector_dual_edge ⟨u, hu⟩ v hedge
      have hav : (suppliedSectorColors.getD v 19 == k.val) = true := by
        cases hw with
        | refl _ h => exact h
        | step h _ _ => exact h
      exact (sector_centers_joined k ⟨u, hu⟩ ⟨v, hb⟩ (Fin.ext (beq_iff_eq.mp ha))
        (Fin.ext (beq_iff_eq.mp hav)) i j he).trans (ih hb hv)

theorem sectorSpace_pathConnected (k : Fin 19) : IsPathConnected (sectorSpace k) := by
  obtain ⟨root, hr, ha, reach⟩ := GraphProof.connectedCheck_sound _ _ (sector_connected_verified k)
  rw [sector_dual_size] at hr
  let f : Fin suppliedModel.oriented.size := ⟨root, hr⟩
  have hf : sectorColor f = k := Fin.ext (beq_iff_eq.mp ha)
  refine ⟨Quad.point (.inr f), sector_triangle_subset k f hf 0
    (diagramQuad.center_mem_triangle f 0), ?_⟩
  intro x hx
  obtain ⟨g, hg, j, hx⟩ := mem_iUnion.mp hx |>.imp (fun _ => mem_iUnion₂.mp)
  have h1 := ((diagramQuad.triangle_pathConnected g j).joinedIn _ hx _
    (diagramQuad.center_mem_triangle g j)).mono (sector_triangle_subset k g hg j)
  have h2 := sector_walk_joined k (reach g.val (by rw [sector_dual_size]; exact g.isLt)
    (beq_iff_eq.mpr (congrArg Fin.val hg))) g.isLt hr
  exact (h1.trans h2).symm

theorem diagramSector_pathConnected (k : Fin 19) : IsPathConnected (diagramSector k) :=
  (sectorSpace_pathConnected k).preimage_coe (sectorSpace_subset_space k)

#print axioms diagramSector_pathConnected
end Venn19.Topology
