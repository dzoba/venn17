import VennTopology.RigidPlaneConjugacy
import VennTopology.PlaneArrangement

/-! The supplied diagram has a simple, rigidly rotational planar Venn realization.
The file's generator decreases curve labels. Reversing their cyclic ordering
expresses the positive rigid rotation as `i ↦ i+1`, as in the Venn definition. -/
noncomputable section
namespace Venn17.Topology
open Set Coordinates
attribute [local irreducible] suppliedModel suppliedFaces suppliedCurvePolygons suppliedLinkStars

def rigidPlaneCurve (i : Fin 17) : Set Plane := planeCurve rigidPlaneHomeomorph i
def rigidPlaneSide (i : Fin 17) (b : Bool) : Set Plane := planeSide rigidPlaneHomeomorph i b
def rigidPlaneRegion (v : Fin 131072) : Set Plane := planeRegion rigidPlaneHomeomorph v
def rigidPlaneCrossing (f : Fin suppliedModel.oriented.size) : Plane :=
  rigidPlaneHomeomorph (puncturedCrossingPoint f)

theorem rigidPlaneCurve_mem (x : PuncturedDiagram) (i : Fin 17) :
    rigidPlaneHomeomorph x ∈ rigidPlaneCurve i ↔ x ∈ puncturedCurve i :=
  rigidPlaneHomeomorph.injective.mem_set_image

theorem rigidPlane_curve_rotation (i : Fin 17) :
    rigidPlaneRotation '' rigidPlaneCurve i = rigidPlaneCurve (curveRotation i) := by
  change rigidPlaneRotation '' (rigidPlaneHomeomorph '' puncturedCurve i) = _
  rw [← image_comp]
  have he : rigidPlaneRotation ∘ rigidPlaneHomeomorph = rigidPlaneHomeomorph ∘ puncturedRotation :=
    funext (fun x => (rigidPlaneHomeomorph_rotation x).symm)
  rw [he, image_comp, punctured_rotation_curve_image]
  rfl

theorem rigidPlane_region_rotation (v : Fin 131072) :
    rigidPlaneRotation '' rigidPlaneRegion v = rigidPlaneRegion (patternRotation v) := by
  change rigidPlaneRotation '' (rigidPlaneHomeomorph '' puncturedRegion v) = _
  rw [← image_comp]
  have he : rigidPlaneRotation ∘ rigidPlaneHomeomorph = rigidPlaneHomeomorph ∘ puncturedRotation :=
    funext (fun x => (rigidPlaneHomeomorph_rotation x).symm)
  rw [he, image_comp, punctured_rotation_region_image]
  rfl

/-- The original file's pattern labels are retained by the rigid realization. -/
theorem rigidPlane_membership_verified :
    (∀ v : Fin 131072, IsPathConnected (rigidPlaneRegion v) ∧
      rigidPlaneRegion v = ⋂ i : Fin 17, rigidPlaneSide i (v.val.testBit i.val)) ∧
    (∀ x : Plane, x ∉ ⋃ i : Fin 17, rigidPlaneCurve i ↔
      ∃! v : Fin 131072, x ∈ rigidPlaneRegion v) :=
  ⟨fun v => ⟨planeRegion_pathConnected rigidPlaneHomeomorph v,
      planeRegion_eq_sides rigidPlaneHomeomorph v⟩,
    plane_complement_unique_region rigidPlaneHomeomorph⟩

theorem rigidPlaneRotation_iterate (n : ℕ) (x : PuncturedDiagram) :
    rigidPlaneRotation^[n] (rigidPlaneHomeomorph x) = rigidPlaneHomeomorph (puncturedRotation^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, ← rigidPlaneHomeomorph_rotation]

theorem rigidPlaneRotation_period (x : Plane) : rigidPlaneRotation^[17] x = x := by
  obtain ⟨y, rfl⟩ := rigidPlaneHomeomorph.surjective x
  rw [rigidPlaneRotation_iterate, punctured_rotation_period]

theorem rigidPlaneRotation_no_short_period (k : ℕ) (hk : 0 < k) (hk17 : k < 17) :
    ∃ x : Plane, rigidPlaneRotation^[k] x ≠ x := by
  obtain ⟨x, hx⟩ := punctured_rotation_no_short_period k hk hk17
  refine ⟨rigidPlaneHomeomorph x, ?_⟩
  rw [rigidPlaneRotation_iterate, ne_eq, rigidPlaneHomeomorph.injective.eq_iff]
  exact hx

theorem rigidPlane_no_triple (i j k : Fin 17) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : Plane) : x ∈ rigidPlaneCurve i → x ∈ rigidPlaneCurve j → x ∉ rigidPlaneCurve k := by
  obtain ⟨y, rfl⟩ := rigidPlaneHomeomorph.surjective x
  simpa only [rigidPlaneCurve_mem] using punctured_no_triple_intersections i j k hij hik hjk y

theorem rigidPlane_crossing_iff (x : Plane) :
    (∃ i j : Fin 17, i ≠ j ∧ x ∈ rigidPlaneCurve i ∧ x ∈ rigidPlaneCurve j) ↔
      ∃ f : Fin suppliedModel.oriented.size, x = rigidPlaneCrossing f := by
  obtain ⟨y, rfl⟩ := rigidPlaneHomeomorph.surjective x
  simpa only [rigidPlaneCurve_mem, rigidPlaneCrossing, rigidPlaneHomeomorph.injective.eq_iff]
    using punctured_crossing_iff y

theorem rigidPlane_transverse_crossing (f : Fin suppliedModel.oriented.size) :
    ∃ i j : Fin 17, i ≠ j ∧ CrossingSquare.HasCrossingChart
      (rigidPlaneCurve i) (rigidPlaneCurve j) (rigidPlaneCrossing f) := by
  obtain ⟨i, j, hij, h⟩ := punctured_transverse_crossing f
  exact ⟨i, j, hij, h.image rigidPlaneHomeomorph⟩

theorem planeSymmetryConjugacy_rotation (x : Plane) :
    planeSymmetryConjugacy (realizedPlaneSymmetry x) = rigidPlaneRotation (planeSymmetryConjugacy x) := by
  obtain ⟨y, rfl⟩ := diagramPlaneHomeomorph.surjective x
  rw [planar_symmetry_apply]
  simpa only [planeSymmetryConjugacy, Homeomorph.trans_apply, Homeomorph.symm_apply_apply] using
    rigidPlaneHomeomorph_rotation y

/-- Reverse the file's decreasing cyclic order to obtain the successor convention. -/
def vennIndexOrder : Equiv.Perm (Fin 17) := Equiv.neg _

theorem vennIndexOrder_next (i : Fin 17) :
    curveRotation (vennIndexOrder i) = vennIndexOrder (cyclicNext i) := by
  decide +revert

def rotationalVennCurve (i : Fin 17) : Set Plane := rigidPlaneCurve (vennIndexOrder i)
def rotationalVennSide (i : Fin 17) (b : Bool) : Set Plane := rigidPlaneSide (vennIndexOrder i) b

theorem rotationalVenn_rotation (i : Fin 17) :
    rigidPlaneRotation '' rotationalVennCurve i = rotationalVennCurve (cyclicNext i) := by
  exact (rigidPlane_curve_rotation (vennIndexOrder i)).trans
    (congrArg rigidPlaneCurve (vennIndexOrder_next i))

theorem rotationalVenn_all_patterns (b : Fin 17 → Bool) :
    IsPathConnected (⋂ i, rotationalVennSide i (b i)) := by
  have he : (⋂ i, rotationalVennSide i (b i)) =
      ⋂ j, rigidPlaneSide j (b (vennIndexOrder.symm j)) := by
    ext x
    constructor
    · intro hx
      apply mem_iInter.mpr
      intro j
      have h := mem_iInter.mp hx (vennIndexOrder.symm j)
      simpa only [rotationalVennSide, Equiv.apply_symm_apply] using h
    · intro hx
      apply mem_iInter.mpr
      intro i
      have h := mem_iInter.mp hx (vennIndexOrder i)
      simpa only [rotationalVennSide, Equiv.symm_apply_apply] using h
  rw [he]
  exact plane_every_membership_pattern rigidPlaneHomeomorph _

/-- The full geometric definition, using the proved rigid positive rotation of
angle `2π/17` about zero. `IsPathConnected` includes nonemptiness. -/
structure SimpleRotationalVenn (C : Fin 17 → Set Plane) (S : Fin 17 → Bool → Set Plane) : Prop where
  jordan : ∀ i, ∃ f : Circle → Plane, Continuous f ∧ Function.Injective f ∧ range f = C i
  sides : ∀ i b, IsOpen (S i b) ∧ IsPathConnected (S i b)
  disjoint : ∀ i, Disjoint (S i false) (S i true)
  complement : ∀ i, (⋃ b, S i b) = (C i)ᶜ
  inside_bounded : ∀ i, Bornology.IsBounded (S i true)
  outside_unbounded : ∀ i, ¬ Bornology.IsBounded (S i false)
  regions : ∀ b : Fin 17 → Bool, IsPathConnected (⋂ i, S i (b i))
  no_triple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∀ x, x ∈ C i → x ∈ C j → x ∉ C k
  crossings : ∀ x, (∃ i j, i ≠ j ∧ x ∈ C i ∧ x ∈ C j) →
    ∃ i j, i ≠ j ∧ CrossingSquare.HasCrossingChart (C i) (C j) x
  rotation : ∀ i, rigidPlaneRotation '' C i = C (cyclicNext i)

/-- All geometric obligations are discharged for the realization built from
the supplied file; no sphere, plane, or conjugacy hypothesis remains. -/
theorem supplied_simple_rotational_venn : SimpleRotationalVenn rotationalVennCurve rotationalVennSide where
  jordan i := plane_curves_are_embedded_circles rigidPlaneHomeomorph (vennIndexOrder i)
  sides i b := ⟨planeSide_isOpen rigidPlaneHomeomorph (vennIndexOrder i) b,
    planeSide_pathConnected rigidPlaneHomeomorph (vennIndexOrder i) b⟩
  disjoint i := planeSide_disjoint rigidPlaneHomeomorph (vennIndexOrder i)
  complement i := planeSide_cover rigidPlaneHomeomorph (vennIndexOrder i)
  inside_bounded i := planeSide_true_bounded rigidPlaneHomeomorph (vennIndexOrder i)
  outside_unbounded i := planeSide_false_unbounded rigidPlaneHomeomorph (vennIndexOrder i)
  regions := rotationalVenn_all_patterns
  no_triple i j k hij hik hjk x := rigidPlane_no_triple _ _ _
    (fun h => hij (vennIndexOrder.injective h))
    (fun h => hik (vennIndexOrder.injective h))
    (fun h => hjk (vennIndexOrder.injective h)) x
  crossings x hx := by
    obtain ⟨i, j, hij, hi, hj⟩ := hx
    have hr : ∃ a b, a ≠ b ∧ x ∈ rigidPlaneCurve a ∧ x ∈ rigidPlaneCurve b :=
      ⟨vennIndexOrder i, vennIndexOrder j, (fun h => hij (vennIndexOrder.injective h)), hi, hj⟩
    obtain ⟨f, rfl⟩ := (rigidPlane_crossing_iff x).mp hr
    obtain ⟨a, b, hab, hc⟩ := rigidPlane_transverse_crossing f
    refine ⟨vennIndexOrder.symm a, vennIndexOrder.symm b,
      (fun h => hab (vennIndexOrder.symm.injective h)), ?_⟩
    simpa only [rotationalVennCurve, Equiv.apply_symm_apply] using hc
  rotation := rotationalVenn_rotation

theorem exists_simple_rotational_venn_17 :
    ∃ (C : Fin 17 → Set Plane) (S : Fin 17 → Bool → Set Plane), SimpleRotationalVenn C S :=
  ⟨rotationalVennCurve, rotationalVennSide, supplied_simple_rotational_venn⟩

end Venn17.Topology
