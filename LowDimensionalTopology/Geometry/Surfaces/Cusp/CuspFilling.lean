module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Surfaces.Cusp.ParabolicCusps
@[expose] public section
noncomputable section
open Set Topology TopologicalSpace
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Surfaces

/-- A genuine punctured-disc coordinate on an open subset of the original space. -/
structure PunctureFillData (X : Type*) [TopologicalSpace X] where
  chart : OpenPartialHomeomorph X ℂ
  radius : ℝ
  radius_pos : 0 < radius
  target_eq : chart.target = {z : ℂ | z ≠ 0 ∧ ‖z‖ < radius}

/-- The old space with exactly one additional point. Its topology is specified below. -/
def PunctureFill {X : Type*} [TopologicalSpace X] (_C : PunctureFillData X) := Option X

def punctureFillSome {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) : X → PunctureFill C := some

def punctureFillInfinity {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) : PunctureFill C := none

def punctureFillDisc {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) : Set ℂ :=
  Metric.ball 0 C.radius

/-- The ordinary disc fills precisely the missing coordinate value. -/
def punctureFillDiscMap {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) :
    punctureFillDisc C → PunctureFill C :=
  fun z => if z.val = 0 then punctureFillInfinity C else punctureFillSome C (C.chart.symm z.val)

/-- The final topology glues the old open space and an ordinary filled disc. -/
instance punctureFillTopology {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) :
    TopologicalSpace (PunctureFill C) :=
  TopologicalSpace.coinduced (punctureFillSome C) inferInstance ⊔
    TopologicalSpace.coinduced (punctureFillDiscMap C) inferInstance

theorem punctureFillSome_injective {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) :
    Function.Injective (punctureFillSome C) := Option.some_injective _

theorem punctureFillDiscMap_eq_some {X : Type*} [TopologicalSpace X] (C : PunctureFillData X)
    (z : punctureFillDisc C) (x : X) :
    punctureFillDiscMap C z = punctureFillSome C x ↔
      x ∈ C.chart.source ∧ C.chart x = z.val := by
  have hzr : ‖z.val‖ < C.radius := by simpa only [punctureFillDisc, Metric.mem_ball, dist_zero_right] using z.property
  change (if z.val = 0 then (none : Option X) else some (C.chart.symm z.val)) = some x ↔ _
  split
  next hz =>
    constructor
    · intro hn
      cases hn
    · rintro ⟨hx, he⟩
      have ht := C.chart.map_source hx
      rw [C.target_eq] at ht
      exact (ht.1 (he.trans hz)).elim
  next hz =>
    have hzt : z.val ∈ C.chart.target := by rw [C.target_eq]; exact ⟨hz, hzr⟩
    rw [Option.some.injEq]
    constructor
    · intro he
      subst x
      exact ⟨C.chart.map_target hzt, C.chart.right_inv hzt⟩
    · rintro ⟨hx, he⟩
      rw [← he]
      exact C.chart.left_inv hx

theorem punctureFillDiscMap_eq_infinity {X : Type*} [TopologicalSpace X] (C : PunctureFillData X)
    (z : punctureFillDisc C) :
    punctureFillDiscMap C z = punctureFillInfinity C ↔ z.val = 0 := by
  change (if z.val = 0 then (none : Option X) else some (C.chart.symm z.val)) = none ↔ _
  split
  next hz => exact ⟨fun _ => hz, fun _ => rfl⟩
  next hz =>
    constructor
    · intro hn
      cases hn
    · intro he
      exact (hz he).elim

theorem punctureFillDiscMap_injective {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) :
    Function.Injective (punctureFillDiscMap C) := by
  intro z w he
  by_cases hz : z.val = 0
  · have hw : w.val = 0 := (punctureFillDiscMap_eq_infinity C w).mp
      (he.symm.trans ((punctureFillDiscMap_eq_infinity C z).mpr hz))
    exact Subtype.ext (hz.trans hw.symm)
  · have ht : z.val ∈ C.chart.target := by
      rw [C.target_eq]
      exact ⟨hz, by simpa only [punctureFillDisc, Metric.mem_ball, dist_zero_right] using z.property⟩
    have hze : punctureFillDiscMap C z = punctureFillSome C (C.chart.symm z.val) :=
      (punctureFillDiscMap_eq_some C z _).mpr ⟨C.chart.map_target ht, C.chart.right_inv ht⟩
    have hw := (punctureFillDiscMap_eq_some C w (C.chart.symm z.val)).mp (he.symm.trans hze)
    exact Subtype.ext ((C.chart.right_inv ht).symm.trans hw.2)

theorem punctureFillSome_continuous {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) :
    Continuous (punctureFillSome C) :=
  continuous_iff_coinduced_le.mpr le_sup_left

theorem punctureFillDiscMap_continuous {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) :
    Continuous (punctureFillDiscMap C) :=
  continuous_iff_coinduced_le.mpr le_sup_right

theorem punctureFillSome_isOpenMap {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) :
    IsOpenMap (punctureFillSome C) := by
  intro U hU
  apply isOpen_sup.mpr
  constructor
  · change IsOpen ((punctureFillSome C) ⁻¹' ((punctureFillSome C) '' U))
    simpa only [preimage_image_eq _ (punctureFillSome_injective C)] using hU
  · change IsOpen ((punctureFillDiscMap C) ⁻¹' ((punctureFillSome C) '' U))
    have heq : (punctureFillDiscMap C) ⁻¹' ((punctureFillSome C) '' U) =
        Subtype.val ⁻¹' (C.chart.target ∩ C.chart.symm ⁻¹' U) := by
      ext w
      constructor
      · rintro ⟨x, hx, he⟩
        have hm := (punctureFillDiscMap_eq_some C w x).mp he.symm
        refine ⟨?_, ?_⟩
        · rw [← hm.2]
          exact C.chart.map_source hm.1
        · change C.chart.symm w.val ∈ U
          rw [← hm.2, C.chart.left_inv hm.1]
          exact hx
      · rintro ⟨hwt, hwU⟩
        exact ⟨C.chart.symm w.val, hwU,
          ((punctureFillDiscMap_eq_some C w _).mpr
            ⟨C.chart.map_target hwt, C.chart.right_inv hwt⟩).symm⟩
    rw [heq]
    exact (C.chart.isOpen_inter_preimage_symm hU).preimage continuous_subtype_val

theorem punctureFillDiscMap_isOpenMap {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) :
    IsOpenMap (punctureFillDiscMap C) := by
  intro V hV
  apply isOpen_sup.mpr
  constructor
  · change IsOpen ((punctureFillSome C) ⁻¹' ((punctureFillDiscMap C) '' V))
    have heq : (punctureFillSome C) ⁻¹' ((punctureFillDiscMap C) '' V) =
        C.chart.source ∩ C.chart ⁻¹' (Subtype.val '' V) := by
      ext x
      constructor
      · rintro ⟨w, hw, he⟩
        have hm := (punctureFillDiscMap_eq_some C w x).mp he
        exact ⟨hm.1, w, hw, hm.2.symm⟩
      · rintro ⟨hx, w, hw, he⟩
        exact ⟨w, hw, (punctureFillDiscMap_eq_some C w x).mpr ⟨hx, he.symm⟩⟩
    rw [heq]
    exact C.chart.isOpen_inter_preimage (Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap V hV)
  · change IsOpen ((punctureFillDiscMap C) ⁻¹' ((punctureFillDiscMap C) '' V))
    simpa only [preimage_image_eq _ (punctureFillDiscMap_injective C)] using hV

theorem punctureFillSome_isOpenEmbedding {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) :
    Topology.IsOpenEmbedding (punctureFillSome C) :=
  .of_continuous_injective_isOpenMap (punctureFillSome_continuous C)
    (punctureFillSome_injective C) (punctureFillSome_isOpenMap C)

theorem punctureFillDiscMap_isOpenEmbedding {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) :
    Topology.IsOpenEmbedding (punctureFillDiscMap C) :=
  .of_continuous_injective_isOpenMap (punctureFillDiscMap_continuous C)
    (punctureFillDiscMap_injective C) (punctureFillDiscMap_isOpenMap C)

theorem punctureFill_ranges_cover {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) :
    Set.range (punctureFillSome C) ∪ Set.range (punctureFillDiscMap C) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  change Option X at p
  cases p with
  | none =>
      right
      refine ⟨⟨0, by simpa only [punctureFillDisc, Metric.mem_ball, dist_self] using C.radius_pos⟩, ?_⟩
      exact (punctureFillDiscMap_eq_infinity C _).mpr rfl
  | some x => exact Or.inl ⟨x, rfl⟩

/-- The punctured coordinate approaches an end of the old space, rather than an old point. -/
def PunctureFillData.Escapes {X : Type*} [TopologicalSpace X] (C : PunctureFillData X) : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ C.chart.target, ‖z‖ < ε → C.chart.symm z ∉ U

theorem punctureFill_infinity_separation {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) (hescape : C.Escapes) (x : X) :
    ∃ U V : Set (PunctureFill C), IsOpen U ∧ IsOpen V ∧
      punctureFillInfinity C ∈ U ∧ punctureFillSome C x ∈ V ∧ Disjoint U V := by
  obtain ⟨W, hW, hxW, ε, hε, he⟩ := hescape x
  let V : Set (punctureFillDisc C) := {z | ‖z.val‖ < ε}
  have hV : IsOpen V := isOpen_lt continuous_subtype_val.norm continuous_const
  refine ⟨(punctureFillDiscMap C) '' V, (punctureFillSome C) '' W,
    punctureFillDiscMap_isOpenMap C V hV, punctureFillSome_isOpenMap C W hW, ?_,
    ⟨x, hxW, rfl⟩, ?_⟩
  · refine ⟨⟨0, by simpa only [punctureFillDisc, Metric.mem_ball, dist_self] using C.radius_pos⟩,
      ?_, (punctureFillDiscMap_eq_infinity C _).mpr rfl⟩
    change ‖(0 : ℂ)‖ < ε
    simpa only [norm_zero] using hε
  · apply Set.disjoint_left.mpr
    rintro _ ⟨z, hz, rfl⟩ ⟨y, hy, heq⟩
    have hm := (punctureFillDiscMap_eq_some C z y).mp heq.symm
    have hzt : z.val ∈ C.chart.target := hm.2 ▸ C.chart.map_source hm.1
    have hnot := he z.val hzt hz
    apply hnot
    rw [← hm.2, C.chart.left_inv hm.1]
    exact hy

/-- End escape is exactly the additional separation input required for the one-point filling. -/
theorem punctureFill_t2Space {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : PunctureFillData X) (hescape : C.Escapes) : T2Space (PunctureFill C) := by
  constructor
  intro p q hpq
  change Option X at p q
  cases p with
  | none =>
    cases q with
    | none => exact (hpq rfl).elim
    | some y => exact punctureFill_infinity_separation C hescape y
  | some x =>
    cases q with
    | none =>
      obtain ⟨U, V, hU, hV, hp, hq, hd⟩ := punctureFill_infinity_separation C hescape x
      exact ⟨V, U, hV, hU, hq, hp, hd.symm⟩
    | some y =>
      have hxy : x ≠ y := fun he => hpq (congrArg some he)
      obtain ⟨U, V, hU, hV, hx, hy, hd⟩ := t2_separation hxy
      refine ⟨(punctureFillSome C) '' U, (punctureFillSome C) '' V,
        punctureFillSome_isOpenMap C U hU, punctureFillSome_isOpenMap C V hV,
        ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ?_⟩
      apply Set.disjoint_left.mpr
      rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
      have hvu := punctureFillSome_injective C he
      subst v
      exact Set.disjoint_left.mp hd hu hv

theorem punctureFillData_source_nonempty {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) : C.chart.source.Nonempty := by
  let z : ℂ := (C.radius / 2 : ℝ)
  have hzpos : 0 < C.radius / 2 := half_pos C.radius_pos
  have hzn : ‖z‖ = C.radius / 2 := by
    change ‖((C.radius / 2 : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzpos]
  have hzt : z ∈ C.chart.target := by
    rw [C.target_eq]
    refine ⟨norm_ne_zero_iff.mp ?_, ?_⟩
    · rw [hzn]
      exact ne_of_gt hzpos
    · rw [hzn]
      linarith [C.radius_pos]
  exact ⟨C.chart.symm z, C.chart.map_target hzt⟩

theorem punctureFill_connectedSpace {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    (C : PunctureFillData X) : ConnectedSpace (PunctureFill C) := by
  have hball : IsConnected (punctureFillDisc C) :=
    (convex_ball (0 : ℂ) C.radius).isConnected
      ⟨0, by simpa only [punctureFillDisc, Metric.mem_ball, dist_self] using C.radius_pos⟩
  have : ConnectedSpace (punctureFillDisc C) := isConnected_iff_connectedSpace.mp hball
  have hI : IsConnected (Set.range (punctureFillSome C)) := by
    simpa only [Set.image_univ] using isConnected_univ.image (punctureFillSome C)
      (punctureFillSome_continuous C).continuousOn
  have hJ : IsConnected (Set.range (punctureFillDiscMap C)) := by
    simpa only [Set.image_univ] using isConnected_univ.image (punctureFillDiscMap C)
      (punctureFillDiscMap_continuous C).continuousOn
  obtain ⟨x, hx⟩ := punctureFillData_source_nonempty C
  have ht := C.chart.map_source hx
  have hxnorm : ‖C.chart x‖ < C.radius := by rw [C.target_eq] at ht; exact ht.2
  let z : punctureFillDisc C := ⟨C.chart x, by
    simpa only [punctureFillDisc, Metric.mem_ball, dist_zero_right] using hxnorm⟩
  have hmeet : (Set.range (punctureFillSome C) ∩ Set.range (punctureFillDiscMap C)).Nonempty :=
    ⟨punctureFillSome C x, ⟨x, rfl⟩, z, (punctureFillDiscMap_eq_some C z x).mpr ⟨hx, rfl⟩⟩
  have hc := hI.union hmeet hJ
  rw [punctureFill_ranges_cover C] at hc
  exact connectedSpace_iff_univ.mpr hc

/-- The original space as an actual open partial homeomorphism into its filling. -/
def punctureFillOldEmbedding {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) : OpenPartialHomeomorph X (PunctureFill C) :=
  (punctureFillSome_isOpenEmbedding C).toOpenPartialHomeomorph (punctureFillSome C)

/-- The ordinary filled disc as an actual open partial homeomorphism into the filling. -/
def punctureFillDiscEmbedding {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) : OpenPartialHomeomorph (punctureFillDisc C) (PunctureFill C) := by
  letI : Nonempty (punctureFillDisc C) :=
    ⟨⟨0, by simpa only [punctureFillDisc, Metric.mem_ball, dist_self] using C.radius_pos⟩⟩
  exact (punctureFillDiscMap_isOpenEmbedding C).toOpenPartialHomeomorph (punctureFillDiscMap C)

/-- The literal ordinary disc inclusion, as an open complex coordinate map. -/
def punctureFillDiscCoordinate {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) : OpenPartialHomeomorph (punctureFillDisc C) ℂ := by
  letI : Nonempty (punctureFillDisc C) :=
    ⟨⟨0, by simpa only [punctureFillDisc, Metric.mem_ball, dist_self] using C.radius_pos⟩⟩
  exact Metric.isOpen_ball.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val

/-- The actual complex coordinate chart around the newly filled point. -/
def punctureFillChart {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) : OpenPartialHomeomorph (PunctureFill C) ℂ := by
  exact (punctureFillDiscEmbedding C).symm.trans (punctureFillDiscCoordinate C)

/-- Every original chart is extended over its original open image, using the old coordinates. -/
def punctureFillOldChart {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (e : OpenPartialHomeomorph X ℂ) :
    OpenPartialHomeomorph (PunctureFill C) ℂ :=
  (punctureFillOldEmbedding C).symm.trans e

theorem punctureFillOldEmbedding_apply {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (x : X) : punctureFillOldEmbedding C x = punctureFillSome C x := rfl

theorem punctureFillDiscEmbedding_apply {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) (z : punctureFillDisc C) :
    punctureFillDiscEmbedding C z = punctureFillDiscMap C z := rfl

theorem punctureFillDiscCoordinate_apply {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) (z : punctureFillDisc C) : punctureFillDiscCoordinate C z = z.val := rfl

theorem punctureFillOldEmbedding_left_inv {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (x : X) :
    (punctureFillOldEmbedding C).symm (punctureFillSome C x) = x :=
  (punctureFillSome_isOpenEmbedding C).toOpenPartialHomeomorph_left_inv

theorem punctureFillDiscEmbedding_left_inv {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) (z : punctureFillDisc C) :
    (punctureFillDiscEmbedding C).symm (punctureFillDiscMap C z) = z := by
  apply (punctureFillDiscEmbedding C).left_inv
  exact Set.mem_univ _

theorem punctureFillOldChart_apply_some {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (e : OpenPartialHomeomorph X ℂ) (x : X) :
    punctureFillOldChart C e (punctureFillSome C x) = e x := by
  change e ((punctureFillOldEmbedding C).symm (punctureFillSome C x)) = e x
  rw [punctureFillOldEmbedding_left_inv]

theorem punctureFillOldChart_symm_apply {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (e : OpenPartialHomeomorph X ℂ) (z : ℂ) :
    (punctureFillOldChart C e).symm z = punctureFillSome C (e.symm z) := rfl

theorem punctureFillChart_apply_discMap {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) (z : punctureFillDisc C) :
    punctureFillChart C (punctureFillDiscMap C z) = z.val := by
  change (punctureFillDiscCoordinate C)
    ((punctureFillDiscEmbedding C).symm (punctureFillDiscMap C z)) = z.val
  rw [punctureFillDiscEmbedding_left_inv, punctureFillDiscCoordinate_apply]

theorem punctureFillDiscCoordinate_source {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) : (punctureFillDiscCoordinate C).source = Set.univ := rfl

theorem punctureFillDiscCoordinate_target {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) : (punctureFillDiscCoordinate C).target = punctureFillDisc C := by
  have : Nonempty (punctureFillDisc C) :=
    ⟨⟨0, by simpa only [punctureFillDisc, Metric.mem_ball, dist_self] using C.radius_pos⟩⟩
  exact (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target
    (Subtype.val : punctureFillDisc C → ℂ) Metric.isOpen_ball.isOpenEmbedding_subtypeVal).trans
    Subtype.range_coe

theorem punctureFillDiscEmbedding_source {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) : (punctureFillDiscEmbedding C).source = Set.univ := rfl

theorem punctureFillDiscEmbedding_target {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) : (punctureFillDiscEmbedding C).target =
      Set.range (punctureFillDiscMap C) := by
  have : Nonempty (punctureFillDisc C) :=
    ⟨⟨0, by simpa only [punctureFillDisc, Metric.mem_ball, dist_self] using C.radius_pos⟩⟩
  exact Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target
    (punctureFillDiscMap C) (punctureFillDiscMap_isOpenEmbedding C)

theorem punctureFillChart_source {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) : (punctureFillChart C).source = Set.range (punctureFillDiscMap C) := by
  rw [punctureFillChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    punctureFillDiscCoordinate_source, preimage_univ, inter_univ, punctureFillDiscEmbedding_target]

theorem punctureFillChart_target {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) : (punctureFillChart C).target = punctureFillDisc C := by
  rw [punctureFillChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    punctureFillDiscEmbedding_source, preimage_univ, inter_univ, punctureFillDiscCoordinate_target]

theorem punctureFillChart_symm_apply {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) (z : punctureFillDisc C) :
    (punctureFillChart C).symm z.val = punctureFillDiscMap C z := by
  have hz : punctureFillDiscMap C z ∈ (punctureFillChart C).source := by
    rw [punctureFillChart_source]
    exact ⟨z, rfl⟩
  exact (congrArg (punctureFillChart C).symm
    (punctureFillChart_apply_discMap C z).symm).trans ((punctureFillChart C).left_inv hz)

theorem punctureFillOldEmbedding_source {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) : (punctureFillOldEmbedding C).source = Set.univ := rfl

theorem punctureFillOldEmbedding_target {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) : (punctureFillOldEmbedding C).target =
      Set.range (punctureFillSome C) :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target
    (punctureFillSome C) (punctureFillSome_isOpenEmbedding C)

theorem punctureFillOldChart_source {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (e : OpenPartialHomeomorph X ℂ) :
    (punctureFillOldChart C e).source = punctureFillSome C '' e.source := by
  rw [punctureFillOldChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    punctureFillOldEmbedding_target]
  ext p
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    simpa only [Set.mem_preimage, punctureFillOldEmbedding_left_inv] using hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    simpa only [Set.mem_preimage, punctureFillOldEmbedding_left_inv] using hx

theorem punctureFillOldChart_target {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (e : OpenPartialHomeomorph X ℂ) :
    (punctureFillOldChart C e).target = e.target := by
  rw [punctureFillOldChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    punctureFillOldEmbedding_source, preimage_univ, inter_univ]

theorem punctureFillChart_source_some_iff {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) (x : X) :
    punctureFillSome C x ∈ (punctureFillChart C).source ↔ x ∈ C.chart.source := by
  rw [punctureFillChart_source]
  constructor
  · rintro ⟨z, hz⟩
    exact ((punctureFillDiscMap_eq_some C z x).mp hz).1
  · intro hx
    have ht := C.chart.map_source hx
    rw [C.target_eq] at ht
    let z : punctureFillDisc C := ⟨C.chart x, by
      simpa only [punctureFillDisc, Metric.mem_ball, dist_zero_right] using ht.2⟩
    exact ⟨z, (punctureFillDiscMap_eq_some C z x).mpr ⟨hx, rfl⟩⟩

theorem punctureFillChart_apply_some {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) (x : X) (hx : x ∈ C.chart.source) :
    punctureFillChart C (punctureFillSome C x) = C.chart x := by
  have ht := C.chart.map_source hx
  rw [C.target_eq] at ht
  let z : punctureFillDisc C := ⟨C.chart x, by
    simpa only [punctureFillDisc, Metric.mem_ball, dist_zero_right] using ht.2⟩
  have he := (punctureFillDiscMap_eq_some C z x).mpr ⟨hx, rfl⟩
  exact (congrArg (punctureFillChart C) he.symm).trans (punctureFillChart_apply_discMap C z)

theorem punctureFillOldChart_source_some_iff {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (e : OpenPartialHomeomorph X ℂ) (x : X) :
    punctureFillSome C x ∈ (punctureFillOldChart C e).source ↔ x ∈ e.source := by
  rw [punctureFillOldChart_source]
  constructor
  · rintro ⟨y, hy, he⟩
    exact punctureFillSome_injective C he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem punctureFill_old_old_source {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (e f : OpenPartialHomeomorph X ℂ) :
    ((punctureFillOldChart C e).symm.trans (punctureFillOldChart C f)).source =
      (e.symm.trans f).source := by
  ext z
  change (z ∈ (punctureFillOldChart C e).target ∧
      (punctureFillOldChart C e).symm z ∈ (punctureFillOldChart C f).source) ↔ _
  rw [punctureFillOldChart_target, punctureFillOldChart_symm_apply,
    punctureFillOldChart_source_some_iff]
  rfl

theorem punctureFill_old_new_source {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (e : OpenPartialHomeomorph X ℂ) :
    ((punctureFillOldChart C e).symm.trans (punctureFillChart C)).source =
      (e.symm.trans C.chart).source := by
  ext z
  change (z ∈ (punctureFillOldChart C e).target ∧
      (punctureFillOldChart C e).symm z ∈ (punctureFillChart C).source) ↔ _
  rw [punctureFillOldChart_target, punctureFillOldChart_symm_apply,
    punctureFillChart_source_some_iff]
  rfl

theorem punctureFill_new_old_source {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (e : OpenPartialHomeomorph X ℂ) :
    ((punctureFillChart C).symm.trans (punctureFillOldChart C e)).source =
      (C.chart.symm.trans e).source := by
  ext z
  change (z ∈ (punctureFillChart C).target ∧
      (punctureFillChart C).symm z ∈ (punctureFillOldChart C e).source) ↔
    (z ∈ C.chart.target ∧ C.chart.symm z ∈ e.source)
  constructor
  · rintro ⟨hzt, hz⟩
    rw [punctureFillChart_target] at hzt
    let w : punctureFillDisc C := ⟨z, hzt⟩
    have hzs := punctureFillChart_symm_apply C w
    rw [punctureFillOldChart_source] at hz
    obtain ⟨x, hx, he⟩ := hz
    have hm := (punctureFillDiscMap_eq_some C w x).mp (hzs.symm.trans he.symm)
    have hmx : C.chart x = z := hm.2
    refine ⟨hmx ▸ C.chart.map_source hm.1, ?_⟩
    rw [← hmx, C.chart.left_inv hm.1]
    exact hx
  · rintro ⟨hzt, hz⟩
    have htr := hzt
    rw [C.target_eq] at htr
    have hzball : z ∈ punctureFillDisc C := by
      simpa only [punctureFillDisc, Metric.mem_ball, dist_zero_right] using htr.2
    let w : punctureFillDisc C := ⟨z, hzball⟩
    refine ⟨by rw [punctureFillChart_target]; exact hzball, ?_⟩
    have he := (punctureFillDiscMap_eq_some C w _).mpr
      ⟨C.chart.map_target hzt, C.chart.right_inv hzt⟩
    rw [punctureFillChart_symm_apply C w, he]
    exact (punctureFillOldChart_source_some_iff C e _).mpr hz

/-- Compatibility with the original atlas is stated for the actual punctured chart. -/
def PunctureFillData.AnalyticCompatible {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) (A : RiemannAtlas X) : Prop :=
  ∀ e ∈ A.charts,
    AnalyticOnNhd ℂ (e.symm.trans C.chart) (e.symm.trans C.chart).source ∧
      AnalyticOnNhd ℂ (C.chart.symm.trans e) (C.chart.symm.trans e).source

theorem punctureFill_old_old_analytic {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (A : RiemannAtlas X)
    (e f : OpenPartialHomeomorph X ℂ) (he : e ∈ A.charts) (hf : f ∈ A.charts) :
    AnalyticOnNhd ℂ ((punctureFillOldChart C e).symm.trans (punctureFillOldChart C f))
      ((punctureFillOldChart C e).symm.trans (punctureFillOldChart C f)).source := by
  have ha : AnalyticOnNhd ℂ (e.symm.trans f)
      ((punctureFillOldChart C e).symm.trans (punctureFillOldChart C f)).source := by
    rw [punctureFill_old_old_source]
    exact A.compatible e he f hf
  apply ha.congr ((punctureFillOldChart C e).symm.trans (punctureFillOldChart C f)).open_source
  intro z _
  change f (e.symm z) = punctureFillOldChart C f ((punctureFillOldChart C e).symm z)
  rw [punctureFillOldChart_symm_apply, punctureFillOldChart_apply_some]

theorem punctureFill_old_new_analytic {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (A : RiemannAtlas X) (hc : C.AnalyticCompatible A)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ A.charts) :
    AnalyticOnNhd ℂ ((punctureFillOldChart C e).symm.trans (punctureFillChart C))
      ((punctureFillOldChart C e).symm.trans (punctureFillChart C)).source := by
  have ha : AnalyticOnNhd ℂ (e.symm.trans C.chart)
      ((punctureFillOldChart C e).symm.trans (punctureFillChart C)).source := by
    rw [punctureFill_old_new_source]
    exact (hc e he).1
  apply ha.congr ((punctureFillOldChart C e).symm.trans (punctureFillChart C)).open_source
  intro z hz
  have hzbase := hz
  rw [punctureFill_old_new_source] at hzbase
  change z ∈ e.target ∧ e.symm z ∈ C.chart.source at hzbase
  change C.chart (e.symm z) = punctureFillChart C ((punctureFillOldChart C e).symm z)
  rw [punctureFillOldChart_symm_apply]
  exact (punctureFillChart_apply_some C (e.symm z) hzbase.2).symm

theorem punctureFill_new_old_analytic {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (A : RiemannAtlas X) (hc : C.AnalyticCompatible A)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ A.charts) :
    AnalyticOnNhd ℂ ((punctureFillChart C).symm.trans (punctureFillOldChart C e))
      ((punctureFillChart C).symm.trans (punctureFillOldChart C e)).source := by
  have ha : AnalyticOnNhd ℂ (C.chart.symm.trans e)
      ((punctureFillChart C).symm.trans (punctureFillOldChart C e)).source := by
    rw [punctureFill_new_old_source]
    exact (hc e he).2
  apply ha.congr ((punctureFillChart C).symm.trans (punctureFillOldChart C e)).open_source
  intro z hz
  have hzbase := hz
  rw [punctureFill_new_old_source] at hzbase
  change z ∈ C.chart.target ∧ C.chart.symm z ∈ e.source at hzbase
  have htr := hzbase.1
  rw [C.target_eq] at htr
  let w : punctureFillDisc C := ⟨z, by
    simpa only [punctureFillDisc, Metric.mem_ball, dist_zero_right] using htr.2⟩
  have heq := (punctureFillDiscMap_eq_some C w _).mpr
    ⟨C.chart.map_target hzbase.1, C.chart.right_inv hzbase.1⟩
  change e (C.chart.symm z) = punctureFillOldChart C e ((punctureFillChart C).symm z)
  rw [punctureFillChart_symm_apply C w, heq, punctureFillOldChart_apply_some]

/-- The old charts together with the genuine filled-disc coordinate form an analytic atlas. -/
def punctureFillRiemannAtlas {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (A : RiemannAtlas X) (hc : C.AnalyticCompatible A) :
    RiemannAtlas (PunctureFill C) where
  charts := (punctureFillOldChart C) '' A.charts ∪ {punctureFillChart C}
  cover p := by
    change Option X at p
    cases p with
    | none =>
      refine ⟨punctureFillChart C, Or.inr rfl, ?_⟩
      rw [punctureFillChart_source]
      refine ⟨⟨0, by simpa only [punctureFillDisc, Metric.mem_ball, dist_self] using C.radius_pos⟩, ?_⟩
      exact (punctureFillDiscMap_eq_infinity C _).mpr rfl
    | some x =>
      obtain ⟨e, he, hx⟩ := A.cover x
      exact ⟨punctureFillOldChart C e, Or.inl ⟨e, he, rfl⟩,
        (punctureFillOldChart_source_some_iff C e x).mpr hx⟩
  compatible e he f hf := by
    rcases he with ⟨a, ha, rfl⟩ | he
    · rcases hf with ⟨b, hb, rfl⟩ | hf
      · exact punctureFill_old_old_analytic C A a b ha hb
      · have hf' : f = punctureFillChart C := hf
        subst f
        exact punctureFill_old_new_analytic C A hc a ha
    · have he' : e = punctureFillChart C := he
      subst e
      rcases hf with ⟨b, hb, rfl⟩ | hf
      · exact punctureFill_new_old_analytic C A hc b hb
      · have hf' : f = punctureFillChart C := hf
        subst f
        exact openPartialHomeomorph_self_transition_analytic _

/-- Filling an analytic end gives a genuine connected Hausdorff Riemann surface. -/
def punctureFillRiemannSurface {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) (C : PunctureFillData X)
    (hc : C.AnalyticCompatible R.toRiemannAtlas) (he : C.Escapes) : RiemannSurface (PunctureFill C) := by
  letI : T2Space X := R.t2Space
  letI : ConnectedSpace X := R.connectedSpace
  exact { punctureFillRiemannAtlas C R.toRiemannAtlas hc with
    t2Space := punctureFill_t2Space C he
    connectedSpace := punctureFill_connectedSpace C }

/-- The original analytic surface is an analytic open subspace of the filling. -/
theorem punctureFillSome_analytic {X : Type*} [TopologicalSpace X] [Nonempty X]
    (C : PunctureFillData X) (A : RiemannAtlas X) (hc : C.AnalyticCompatible A) :
    RiemannAnalyticMap A (punctureFillRiemannAtlas C A hc) (punctureFillSome C) := by
  refine ⟨punctureFillSome_continuous C, ?_⟩
  intro e he f hf
  rcases hf with ⟨b, hb, rfl⟩ | hf
  · have hbase : riemannChartMapDomain e (punctureFillSome C) (punctureFillOldChart C b) =
        (e.symm.trans b).source := by
      ext z
      change (z ∈ e.target ∧ punctureFillSome C (e.symm z) ∈
        (punctureFillOldChart C b).source) ↔ _
      rw [punctureFillOldChart_source_some_iff]
      rfl
    have ha : AnalyticOnNhd ℂ (e.symm.trans b)
        (riemannChartMapDomain e (punctureFillSome C) (punctureFillOldChart C b)) := by
      rw [hbase]
      exact A.compatible e he b hb
    apply ha.congr (riemannChartMapDomain_isOpen _ _ _ (punctureFillSome_continuous C))
    intro z _
    change b (e.symm z) = punctureFillOldChart C b (punctureFillSome C (e.symm z))
    exact (punctureFillOldChart_apply_some C b _).symm
  · have hf' : f = punctureFillChart C := hf
    subst f
    have hbase : riemannChartMapDomain e (punctureFillSome C) (punctureFillChart C) =
        (e.symm.trans C.chart).source := by
      ext z
      change (z ∈ e.target ∧ punctureFillSome C (e.symm z) ∈
        (punctureFillChart C).source) ↔ _
      rw [punctureFillChart_source_some_iff]
      rfl
    have ha : AnalyticOnNhd ℂ (e.symm.trans C.chart)
        (riemannChartMapDomain e (punctureFillSome C) (punctureFillChart C)) := by
      rw [hbase]
      exact (hc e he).1
    apply ha.congr (riemannChartMapDomain_isOpen _ _ _ (punctureFillSome_continuous C))
    intro z hz
    change C.chart (e.symm z) = punctureFillChart C (punctureFillSome C (e.symm z))
    have hx : e.symm z ∈ C.chart.source := (punctureFillChart_source_some_iff C _).mp hz.2
    exact (punctureFillChart_apply_some C _ hx).symm

theorem punctureFillChart_infinity {X : Type*} [TopologicalSpace X]
    (C : PunctureFillData X) : punctureFillChart C (punctureFillInfinity C) = 0 := by
  let z : punctureFillDisc C :=
    ⟨0, by simpa only [punctureFillDisc, Metric.mem_ball, dist_self] using C.radius_pos⟩
  have he := (punctureFillDiscMap_eq_infinity C z).mpr rfl
  exact (congrArg (punctureFillChart C) he.symm).trans (punctureFillChart_apply_discMap C z)

open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The literal finite inclusion of the normalized punctured complex disc. -/
def stableCuspPuncturedDiscInclusion (h : ℝ) : stableCuspPuncturedDisc h → ℂ := fun z => z.val.val

theorem stableCuspPuncturedDiscInclusion_isOpenEmbedding (h : ℝ) :
    Topology.IsOpenEmbedding (stableCuspPuncturedDiscInclusion h) := by
  exact (show IsOpen ({z : ℂ | z ≠ 0}) from isClosed_singleton.isOpen_compl).isOpenEmbedding_subtypeVal.comp
    (stableCuspPuncturedDisc_isOpen h).isOpenEmbedding_subtypeVal

/-- The ordinary punctured-disc inclusion as a genuine full-source complex chart. -/
def stableCuspPuncturedDiscChart (h : ℝ) : OpenPartialHomeomorph (stableCuspPuncturedDisc h) ℂ := by
  letI : Nonempty (stableCuspPuncturedDisc h) := (stableCuspPuncturedDisc_isConnected h).nonempty.to_subtype
  exact (stableCuspPuncturedDiscInclusion_isOpenEmbedding h).toOpenPartialHomeomorph
    (stableCuspPuncturedDiscInclusion h)

theorem stableCuspPuncturedDiscChart_source (h : ℝ) :
    (stableCuspPuncturedDiscChart h).source = Set.univ := rfl

theorem stableCuspPuncturedDiscChart_apply (h : ℝ) (z : stableCuspPuncturedDisc h) :
    stableCuspPuncturedDiscChart h z = z.val.val := rfl

theorem stableCuspPuncturedDiscChart_target (h : ℝ) :
    (stableCuspPuncturedDiscChart h).target = {z : ℂ | z ≠ 0 ∧ ‖z‖ < stableCuspRadius h} := by
  have : Nonempty (stableCuspPuncturedDisc h) := (stableCuspPuncturedDisc_isConnected h).nonempty.to_subtype
  have ht := Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target
    (stableCuspPuncturedDiscInclusion h) (stableCuspPuncturedDiscInclusion_isOpenEmbedding h)
  refine ht.trans ?_
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.val.property, w.property⟩
  · rintro ⟨hz, hr⟩
    exact ⟨⟨⟨z, hz⟩, hr⟩, rfl⟩

/-- The open inclusion of the actual stable cusp image into the old full quotient. -/
def stableCuspImageEmbedding {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    OpenPartialHomeomorph S.quotientImage (MobiusDomainQuotient D) := by
  letI : Nonempty S.quotientImage := (S.quotientImage_isConnected hSc).nonempty.to_subtype
  exact (S.quotientImage_isOpen hSo).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val

/-- The actual period-one exponential coordinate on its original open full-quotient image. -/
def stableCuspImageChart {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    OpenPartialHomeomorph (MobiusDomainQuotient D) ℂ :=
  (stableCuspImageEmbedding S hSo hSc).symm.trans
    ((stableCuspImageHomeomorph S h hS hK hSo hSc).toOpenPartialHomeomorph.trans
      (stableCuspPuncturedDiscChart h))

theorem stableCuspImageEmbedding_source {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    (stableCuspImageEmbedding S hSo hSc).source = Set.univ := rfl

theorem stableCuspImageEmbedding_apply {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) (p : S.quotientImage) :
    stableCuspImageEmbedding S hSo hSc p = p.val := rfl

theorem stableCuspImageEmbedding_target {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    (stableCuspImageEmbedding S hSo hSc).target = S.quotientImage := by
  have : Nonempty S.quotientImage := (S.quotientImage_isConnected hSc).nonempty.to_subtype
  exact (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target
    (Subtype.val : S.quotientImage → MobiusDomainQuotient D)
    (S.quotientImage_isOpen hSo).isOpenEmbedding_subtypeVal).trans Subtype.range_coe

theorem stableCuspImageChart_source {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    (stableCuspImageChart S h hS hK hSo hSc).source = S.quotientImage := by
  rw [stableCuspImageChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    stableCuspPuncturedDiscChart_source, preimage_univ, inter_self,
    preimage_univ, inter_univ, OpenPartialHomeomorph.symm_source, stableCuspImageEmbedding_target]

theorem stableCuspImageChart_target {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    (stableCuspImageChart S h hS hK hSo hSc).target =
      {z : ℂ | z ≠ 0 ∧ ‖z‖ < stableCuspRadius h} := by
  rw [stableCuspImageChart, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.symm_target, stableCuspImageEmbedding_source, preimage_univ, inter_univ,
    OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
    preimage_univ, inter_univ, stableCuspPuncturedDiscChart_target]

theorem stableCuspImageChart_apply_image {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) (p : S.quotientImage) :
    stableCuspImageChart S h hS hK hSo hSc p.val =
      (stableCuspImageHomeomorph S h hS hK hSo hSc p).val.val := by
  have hp : p ∈ (stableCuspImageEmbedding S hSo hSc).source := by
    rw [stableCuspImageEmbedding_source]
    exact Set.mem_univ _
  have hi : (stableCuspImageEmbedding S hSo hSc).symm p.val = p :=
    (stableCuspImageEmbedding S hSo hSc).left_inv hp
  change ((stableCuspImageHomeomorph S h hS hK hSo hSc)
    ((stableCuspImageEmbedding S hSo hSc).symm p.val)).val.val = _
  rw [hi]

theorem stableCuspImageChart_symm_apply {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) (z : stableCuspPuncturedDisc h) :
    (stableCuspImageChart S h hS hK hSo hSc).symm z.val.val =
      ((stableCuspImageHomeomorph S h hS hK hSo hSc).symm z).val := by
  have hp : z ∈ (stableCuspPuncturedDiscChart h).source := by
    rw [stableCuspPuncturedDiscChart_source]
    exact Set.mem_univ _
  have hi : (stableCuspPuncturedDiscChart h).symm z.val.val = z :=
    (stableCuspPuncturedDiscChart h).left_inv hp
  change (stableCuspImageEmbedding S hSo hSc)
    ((stableCuspImageHomeomorph S h hS hK hSo hSc).symm
      ((stableCuspPuncturedDiscChart h).symm z.val.val)) = _
  rw [hi]
  rfl

/-- The normalized stable cusp supplies genuine punctured coordinate data on the old quotient. -/
def stableCuspFillData {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    PunctureFillData (MobiusDomainQuotient D) where
  chart := stableCuspImageChart S h hS hK hSo hSc
  radius := stableCuspRadius h
  radius_pos := stableCuspRadius_pos h
  target_eq := stableCuspImageChart_target S h hS hK hSo hSc

/-- The actual full-group compact-tail estimate discharges end escape for the canonical
exponential coordinate on the old quotient. No quotient separation is assumed. -/
theorem stableCuspFillData_escapes {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup) :
    (stableCuspFillData S h hS hK hSo hSc).Escapes := by
  intro x
  obtain ⟨z, rfl⟩ := mobiusDomainProjection_surjective D x
  obtain ⟨K, hKc, hzK, hKD⟩ := exists_compact_subset D.isOpen z.property
  let V : Set D.carrier := Subtype.val ⁻¹' interior K
  let U : Set (MobiusDomainQuotient D) := mobiusDomainProjection D '' V
  have hV : IsOpen V := isOpen_interior.preimage continuous_subtype_val
  have hU : IsOpen U := (mobiusDomainProjection_isOpenQuotientMap D).isOpenMap V hV
  have hQ : stableCuspSphere h ⊆ D.carrier := hS ▸ S.subset_domain
  obtain ⟨t, ht, htail⟩ := stableCusp_compact_tail_escape G D hD hT h hQ hfix K hKc hKD
  refine ⟨U, hU, ⟨z, hzK, rfl⟩, stableCuspRadius t, stableCuspRadius_pos t, ?_⟩
  intro w hwt hwn hwU
  change w ∈ (stableCuspImageChart S h hS hK hSo hSc).target at hwt
  rw [stableCuspImageChart_target] at hwt
  let wP : stableCuspPuncturedDisc h := ⟨⟨w, hwt.1⟩, hwt.2⟩
  change (stableCuspImageChart S h hS hK hSo hSc).symm w ∈ U at hwU
  have hs := stableCuspImageChart_symm_apply S h hS hK hSo hSc wP
  change (stableCuspImageChart S h hS hK hSo hSc).symm w =
    ((stableCuspImageHomeomorph S h hS hK hSo hSc).symm wP).val at hs
  rw [hs] at hwU
  obtain ⟨a, haK, haE⟩ := hwU
  obtain ⟨q, hq⟩ := (mobiusDiscRangeProjection_isOpenQuotientMap D S.carrier
    S.subset_domain hSo).surjective ((stableCuspImageHomeomorph S h hS hK hSo hSc).symm wP)
  have hqS : q.val ∈ stableCuspSphere h := hS ▸ q.property
  obtain ⟨v, hv, hqv⟩ := hqS
  let vH : stableCuspHalfPlane h := ⟨v, hv⟩
  have hExp := stableCuspImageHomeomorph_projection S h hS hK hSo hSc q vH hqv.symm
  have hE : stableCuspImageHomeomorph S h hS hK hSo hSc
      (mobiusDiscRangeProjection D S.carrier S.subset_domain q) = wP :=
    (congrArg (stableCuspImageHomeomorph S h hS hK hSo hSc) hq).trans
      (Homeomorph.apply_symm_apply _ _)
  have hnorm : ‖(complexPeriodExponential 1 v).val‖ < stableCuspRadius t := by
    have hn := congrArg (fun p : stableCuspPuncturedDisc h => ‖p.val.val‖) (hExp.symm.trans hE)
    exact hn.symm ▸ hwn
  have hvt : t < v.im := (stableCuspExponential_mem t v).mp hnorm
  let qD : D.carrier := ⟨q.val, S.subset_domain q.property⟩
  have hpa : mobiusDomainProjection D a = mobiusDomainProjection D qD :=
    haE.trans (congrArg Subtype.val hq).symm
  obtain ⟨g, hg⟩ := Quotient.exact hpa
  have hga : g.val.val q.val = a.val := congrArg Subtype.val hg
  exact Set.disjoint_left.mp (htail g.val g.property)
    ⟨q.val, ⟨v, hvt, hqv⟩, hga⟩ (interior_subset haK)

/-- A homeomorphism analytic in the genuinely lifted source and coordinate atlases gives
an actual analytic coordinate on the original space, in both directions. -/
theorem riemann_lifted_coordinate_compatible
    {X U V : Type*} [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace V]
    (A : RiemannAtlas X) (i : OpenPartialHomeomorph U X) (hi : i.source = Set.univ)
    (hil : IsLocalHomeomorph i) (v : OpenPartialHomeomorph V ℂ) (hv : v.source = Set.univ)
    (hvl : IsLocalHomeomorph v) (E : U ≃ₜ V)
    (hE : RiemannAnalyticMap (A.liftLocalHomeomorph i hil)
      (complexPlaneRiemannSurface.toRiemannAtlas.liftLocalHomeomorph v hvl) E) :
    ∀ e ∈ A.charts,
      AnalyticOnNhd ℂ (e.symm.trans (i.symm.trans (E.toOpenPartialHomeomorph.trans v)))
        (e.symm.trans (i.symm.trans (E.toOpenPartialHomeomorph.trans v))).source ∧
      AnalyticOnNhd ℂ ((i.symm.trans (E.toOpenPartialHomeomorph.trans v)).symm.trans e)
        ((i.symm.trans (E.toOpenPartialHomeomorph.trans v)).symm.trans e).source := by
  let q := i.symm.trans (E.toOpenPartialHomeomorph.trans v)
  have hqs : q.source = i.target := by
    simp only [q, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Homeomorph.toOpenPartialHomeomorph_source, hv, preimage_univ, inter_self, inter_univ]
  have hqt : q.target = v.target := by
    simp only [q, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target, hi,
      Homeomorph.toOpenPartialHomeomorph_target, preimage_univ, inter_univ]
  let b := v.trans (OpenPartialHomeomorph.refl ℂ)
  have hbs : b.source = Set.univ := by
    simp only [b, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.refl_source,
      hv, preimage_univ, inter_self]
  have hbt : b.target = v.target := by
    change Set.univ ∩ v.target = v.target
    exact univ_inter _
  have hb : b ∈ (complexPlaneRiemannSurface.toRiemannAtlas.liftLocalHomeomorph v hvl).charts :=
    ⟨v, rfl, OpenPartialHomeomorph.refl ℂ, rfl, rfl⟩
  have hEi := riemannAnalyticMap_homeomorph_symm E hE
  intro e he
  have ha : i.trans e ∈ (A.liftLocalHomeomorph i hil).charts := ⟨i, rfl, e, he, rfl⟩
  constructor
  · have hd : riemannChartMapDomain (i.trans e) E b = (e.symm.trans q).source := by
      rw [riemannChartMapDomain, hbs, preimage_univ, preimage_univ, inter_univ,
        OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, hqs]
    have hh := hE.2 (i.trans e) ha b hb
    rw [hd] at hh
    apply hh.congr (e.symm.trans q).open_source
    intro z _
    rfl
  · have hd : riemannChartMapDomain b E.symm (i.trans e) = (q.symm.trans e).source := by
      ext z
      change (z ∈ b.target ∧ E.symm (b.symm z) ∈ (i.trans e).source) ↔
        (z ∈ q.target ∧ q.symm z ∈ e.source)
      rw [hbt, hqt]
      change (z ∈ v.target ∧ E.symm (v.symm z) ∈ i.source ∧
        i (E.symm (v.symm z)) ∈ e.source) ↔
        (z ∈ v.target ∧ i (E.symm (v.symm z)) ∈ e.source)
      rw [hi]
      simp only [Set.mem_univ, true_and]
    have hh := hEi.2 b hb (i.trans e) ha
    rw [hd] at hh
    apply hh.congr (q.symm.trans e).open_source
    intro z _
    rfl

/-- The ordinary punctured-plane inclusion is analytic for its original global chart. -/
theorem puncturedPlane_inclusion_analytic :
    RiemannAnalyticMap puncturedPlaneRiemannSurface.toRiemannAtlas
      complexPlaneRiemannSurface.toRiemannAtlas (Subtype.val : {z : ℂ // z ≠ 0} → ℂ) := by
  apply (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.globalChart_iff puncturedPlaneChart
    puncturedPlaneChart_source
    (OpenPartialHomeomorph.refl ℂ) rfl Subtype.val).mpr
  refine ⟨continuous_subtype_val, ?_⟩
  have hd : riemannChartMapDomain puncturedPlaneChart Subtype.val (OpenPartialHomeomorph.refl ℂ) =
      puncturedPlaneChart.target := by
    simp only [riemannChartMapDomain, OpenPartialHomeomorph.refl_source, preimage_univ, inter_univ]
  rw [hd]
  apply (analyticOnNhd_id : AnalyticOnNhd ℂ id puncturedPlaneChart.target).congr puncturedPlaneChart.open_target
  intro z hz
  exact ((puncturedPlaneChart.right_inv hz) : (puncturedPlaneChart.symm z).val = z).symm

/-- The actual nested punctured-disc inclusion is analytic in the already established atlas. -/
theorem stableCuspPuncturedDiscInclusion_analytic (h : ℝ) :
    RiemannAnalyticMap (stableCuspPuncturedDiscRiemannSurface h).toRiemannAtlas
      complexPlaneRiemannSurface.toRiemannAtlas (stableCuspPuncturedDiscInclusion h) := by
  have hp := puncturedPlaneRiemannSurface.toRiemannAtlas.liftLocalHomeomorph_projection_analytic
    (Subtype.val : stableCuspPuncturedDisc h → {z : ℂ // z ≠ 0})
    (stableCuspPuncturedDisc_isOpen h).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  exact puncturedPlane_inclusion_analytic.comp hp

/-- The canonical exponential cusp chart is compatible with the genuine old quotient atlas. -/
theorem stableCuspFillData_analyticCompatible {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    (stableCuspFillData S h hS hK hSo hSc).AnalyticCompatible
      (mobiusQuotientRiemannSurface D hD).toRiemannAtlas := by
  let A := (mobiusQuotientRiemannSurface D hD).toRiemannAtlas
  let i := stableCuspImageEmbedding S hSo hSc
  let v := stableCuspPuncturedDiscChart h
  have hil : IsLocalHomeomorph i := by
    change IsLocalHomeomorph (Subtype.val : S.quotientImage → MobiusDomainQuotient D)
    exact (S.quotientImage_isOpen hSo).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hvl : IsLocalHomeomorph v := by
    change IsLocalHomeomorph (stableCuspPuncturedDiscInclusion h)
    exact (stableCuspPuncturedDiscInclusion_isOpenEmbedding h).isLocalHomeomorph
  have hp := complexPlaneRiemannSurface.toRiemannAtlas.liftLocalHomeomorph_projection_analytic v hvl
  have hcomp := (stableCuspPuncturedDiscInclusion_analytic h).comp
    (stableCuspImageHomeomorph_analytic S hD h hS hK hSo hSc)
  have hE := _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_localHomeomorph hp hvl
    (stableCuspImageHomeomorph S h hS hK hSo hSc).continuous hcomp
  exact riemann_lifted_coordinate_compatible A i (stableCuspImageEmbedding_source S hSo hSc) hil
    v (stableCuspPuncturedDiscChart_source h) hvl
    (stableCuspImageHomeomorph S h hS hK hSo hSc) hE

/-- The actual original quotient with its normalized parabolic cusp filled is a genuine
Riemann surface, extending its original complex structure. -/
def stableCuspFilledRiemannSurface {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup) :
    RiemannSurface (PunctureFill (stableCuspFillData S h hS hK hSo hSc)) :=
  punctureFillRiemannSurface (mobiusQuotientRiemannSurface D hD)
    (stableCuspFillData S h hS hK hSo hSc)
    (stableCuspFillData_analyticCompatible S hD h hS hK hSo hSc)
    (stableCuspFillData_escapes S hD hT h hS hK hSo hSc hfix)

/-- The old full-group quotient retains its original topology and analytic structure. -/
theorem stableCuspFilled_inclusion_analytic {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup) :
    RiemannAnalyticMap (mobiusQuotientRiemannSurface D hD).toRiemannAtlas
      (stableCuspFilledRiemannSurface S hD hT h hS hK hSo hSc hfix).toRiemannAtlas
      (punctureFillSome (stableCuspFillData S h hS hK hSo hSc)) := by
  have : ConnectedSpace (MobiusDomainQuotient D) :=
    (mobiusQuotientRiemannSurface D hD).connectedSpace
  exact punctureFillSome_analytic (stableCuspFillData S h hS hK hSo hSc)
    (mobiusQuotientRiemannSurface D hD).toRiemannAtlas
    (stableCuspFillData_analyticCompatible S hD h hS hK hSo hSc)

/-- A finite half-plane homeomorphism extends to the same added cusp point. -/
def stableCuspCompletionMap (h : ℝ) (e : stableCuspHalfPlane h ≃ₜ stableCuspHalfPlane h) :
    StableCuspCompletion h → StableCuspCompletion h := Option.map e

/-- Invariance of the actual filled exponential gives continuity in the genuine cusp topology. -/
theorem stableCuspCompletionMap_continuous (h : ℝ)
    (e : stableCuspHalfPlane h ≃ₜ stableCuspHalfPlane h)
    (he : ∀ p, stableCuspCompletionToDisc h (stableCuspCompletionMap h e p) = stableCuspCompletionToDisc h p) :
    Continuous (stableCuspCompletionMap h e) := by
  apply continuous_generateFrom_iff.mpr
  intro U hU
  rcases hU with ⟨V, hV, rfl⟩ | ⟨V, hV, rfl⟩
  · have hpre : (stableCuspCompletionMap h e) ⁻¹' ((stableCuspCompletionSome h) '' V) =
        (stableCuspCompletionSome h) '' (e ⁻¹' V) := by
      ext p
      cases p with
      | none =>
        change (∃ w ∈ V, (some w : Option (stableCuspHalfPlane h)) = none) ↔
          ∃ w ∈ e ⁻¹' V, (some w : Option (stableCuspHalfPlane h)) = none
        constructor <;> rintro ⟨w, _, heq⟩ <;> cases heq
      | some z =>
        change (∃ w ∈ V, some w = some (e z)) ↔ ∃ w ∈ e ⁻¹' V, some w = some z
        simp only [Option.some.injEq, exists_eq_right, mem_preimage]
    rw [hpre]
    exact (stableCuspCompletion_some_isOpenEmbedding h).isOpenMap _ (hV.preimage e.continuous)
  · have hpre : (stableCuspCompletionMap h e) ⁻¹' (stableCuspCompletionToDisc h ⁻¹' V) =
        stableCuspCompletionToDisc h ⁻¹' V := by
      ext p
      exact (congrArg (fun z => z ∈ V) (he p)).to_iff
    rw [hpre]
    exact hV.preimage (stableCuspCompletionToDisc_continuous h)

/-- A genuine exponential-preserving finite homeomorphism extends as a cusp homeomorphism. -/
def stableCuspCompletionHomeomorph (h : ℝ)
    (e : stableCuspHalfPlane h ≃ₜ stableCuspHalfPlane h)
    (he : ∀ p, stableCuspCompletionToDisc h (stableCuspCompletionMap h e p) = stableCuspCompletionToDisc h p) :
    StableCuspCompletion h ≃ₜ StableCuspCompletion h where
  toFun := stableCuspCompletionMap h e
  invFun := stableCuspCompletionMap h e.symm
  left_inv p := by
    cases p with
    | none => rfl
    | some z => exact congrArg some (e.symm_apply_apply z)
  right_inv p := by
    cases p with
    | none => rfl
    | some z => exact congrArg some (e.apply_symm_apply z)
  continuous_toFun := stableCuspCompletionMap_continuous h e he
  continuous_invFun := by
    apply stableCuspCompletionMap_continuous h e.symm
    intro p
    have hh := he (stableCuspCompletionMap h e.symm p)
    have hp : stableCuspCompletionMap h e (stableCuspCompletionMap h e.symm p) = p := by
      cases p with
      | none => rfl
      | some z => exact congrArg some (e.apply_symm_apply z)
    rw [hp] at hh
    exact hh.symm

/-- The actual integer translation on the original finite half-plane. -/
def stableCuspHalfPlaneIntegerTranslation (h : ℝ) (n : ℤ) :
    stableCuspHalfPlane h ≃ₜ stableCuspHalfPlane h where
  toFun z := ⟨z.val + (n : ℂ), by simpa [stableCuspHalfPlane, Complex.add_im] using z.property⟩
  invFun z := ⟨z.val - (n : ℂ), by simpa [stableCuspHalfPlane, Complex.sub_im] using z.property⟩
  left_inv z := Subtype.ext (add_sub_cancel_right z.val (n : ℂ))
  right_inv z := Subtype.ext (sub_add_cancel z.val (n : ℂ))
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

theorem stableCuspCompletionIntegerTranslation_exponential (h : ℝ) (n : ℤ) (p : StableCuspCompletion h) :
    stableCuspCompletionToDisc h
      (stableCuspCompletionMap h (stableCuspHalfPlaneIntegerTranslation h n) p) =
      stableCuspCompletionToDisc h p := by
  apply (stableCuspCompletion_orbitRel_iff h _ _).mp
  refine ⟨⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (n : ℂ), (stableTranslationGroup_mem
    _).mpr ⟨n, rfl⟩⟩, ?_⟩
  cases p with
  | none => exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty _
  | some z => exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe _ _

/-- The literal integer translation, extended over the genuine completed cusp. -/
def stableCuspCompletionIntegerTranslation (h : ℝ) (n : ℤ) :
    StableCuspCompletion h ≃ₜ StableCuspCompletion h :=
  stableCuspCompletionHomeomorph h (stableCuspHalfPlaneIntegerTranslation h n)
    (stableCuspCompletionIntegerTranslation_exponential h n)

theorem stableCuspCompletionIntegerTranslation_sphere (h : ℝ) (n : ℤ) (p : StableCuspCompletion h) :
    stableCuspCompletionSphere h (stableCuspCompletionIntegerTranslation h n p) =
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (n : ℂ)).val (stableCuspCompletionSphere h p) := by
  cases p with
  | none => exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty _).symm
  | some z => exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe _ _).symm

/-- The actual original invariant domain with the full orbit of its cusp adjoined. -/
def StableCuspAugmentedDomain {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (_S : MobiusStableSubset D) (_h : ℝ) (_hS : _S.carrier = stableCuspSphere _h) :=
  {p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex // p ∈ D.carrier ∨ ∃ g : G, g.val.val ∞ = p}

/-- The original domain is included by its original sphere points. -/
def stableCuspAugmentedOld {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) :
    D.carrier → StableCuspAugmentedDomain S h hS := fun z => ⟨z.val, Or.inl z.property⟩

/-- Each genuine translated completed cusp maps into the actual augmented domain. -/
def stableCuspAugmentedCusp {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) (g : G) :
    StableCuspCompletion h → StableCuspAugmentedDomain S h hS :=
  Option.rec ⟨g.val.val ∞, Or.inr ⟨g, rfl⟩⟩
    (fun z => ⟨g.val.val (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), Or.inl (D.invariant g
      _
      (S.subset_domain (by rw [hS]; exact ⟨z.val, z.property, rfl⟩)))⟩)

/-- The actual augmented-domain topology is glued from the old domain and all genuine
translated completed cusps, retaining their literal uniform-height end neighborhoods. -/
instance stableCuspAugmentedTopology {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D
  : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) :
    TopologicalSpace (StableCuspAugmentedDomain S h hS) :=
  TopologicalSpace.coinduced (stableCuspAugmentedOld S h hS) inferInstance ⊔
    ⨆ g : G, TopologicalSpace.coinduced (stableCuspAugmentedCusp S h hS g) inferInstance

theorem stableCuspAugmented_isOpen_iff {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (U : Set (StableCuspAugmentedDomain S h hS)) :
    IsOpen U ↔ IsOpen ((stableCuspAugmentedOld S h hS) ⁻¹' U) ∧
      ∀ g : G, IsOpen ((stableCuspAugmentedCusp S h hS g) ⁻¹' U) := by
  exact isOpen_sup.trans (and_congr Iff.rfl isOpen_iSup_iff)

/-- The actual quotient projection on old points, with every new cusp mapped to the filled point. -/
def stableCuspAugmentedProjection {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    StableCuspAugmentedDomain S h hS → PunctureFill (stableCuspFillData S h hS hK hSo hSc) := by
  classical
  exact fun p => if hp : p.val ∈ D.carrier then
    punctureFillSome (stableCuspFillData S h hS hK hSo hSc) (mobiusDomainProjection D ⟨p.val, hp⟩)
    else punctureFillInfinity (stableCuspFillData S h hS hK hSo hSc)

theorem stableCuspAugmentedProjection_old {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (z : D.carrier) :
    stableCuspAugmentedProjection S h hS hK hSo hSc (stableCuspAugmentedOld S h hS z) =
      punctureFillSome (stableCuspFillData S h hS hK hSo hSc) (mobiusDomainProjection D z) := by
  unfold stableCuspAugmentedProjection
  split_ifs with hz
  · rfl
  · exact (hz z.property).elim

/-- The literal finite exponential already agrees with the filled coordinate map. -/
theorem stableCuspFilledDiscMap_finite {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (z : stableCuspHalfPlane h) :
    punctureFillDiscMap (stableCuspFillData S h hS hK hSo hSc) (stableCuspFiniteToFilledDisc h z) =
      punctureFillSome (stableCuspFillData S h hS hK hSo hSc)
        (mobiusDomainProjection D ⟨(z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),
          S.subset_domain (by rw [hS]; exact ⟨z.val, z.property, rfl⟩)⟩) := by
  let q : S.carrier := ⟨(z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), by rw [hS]; exact ⟨z.val, z.property, rfl⟩⟩
  let p := mobiusDiscRangeProjection D S.carrier S.subset_domain q
  have hp := stableCuspImageChart_apply_image S h hS hK hSo hSc p
  have he := stableCuspImageHomeomorph_projection S h hS hK hSo hSc q z rfl
  apply (punctureFillDiscMap_eq_some (stableCuspFillData S h hS hK hSo hSc) _ _).mpr
  constructor
  · change p.val ∈ (stableCuspImageChart S h hS hK hSo hSc).source
    rw [stableCuspImageChart_source]
    exact p.property
  · exact hp.trans (congrArg (fun w : stableCuspPuncturedDisc h => w.val.val) he)

/-- Every genuine translated completed cusp has the same original filled exponential
quotient coordinate, including its actual new ideal point. -/
theorem stableCuspAugmentedProjection_cusp {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (g : G) (p : StableCuspCompletion h) :
    stableCuspAugmentedProjection S h hS hK hSo hSc (stableCuspAugmentedCusp S h hS g p) =
      punctureFillDiscMap (stableCuspFillData S h hS hK hSo hSc) (stableCuspCompletionToDisc h p) := by
  classical
  cases p with
  | none =>
    have hn := stableCusp_orbit_infty_not_mem G D hD hT g
    unfold stableCuspAugmentedProjection
    split_ifs with hp
    · exact (hn hp).elim
    · exact ((punctureFillDiscMap_eq_infinity (stableCuspFillData S h hS hK hSo hSc)
        (stableCuspCompletionToDisc h none)).mpr rfl).symm
  | some z =>
    have hzS : (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ S.carrier := by
      rw [hS]
      exact ⟨z.val, z.property, rfl⟩
    let zD : D.carrier := ⟨(z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), S.subset_domain hzS⟩
    have hgD := D.invariant g zD.val zD.property
    unfold stableCuspAugmentedProjection
    split_ifs with hp
    · have hπ := mobiusDomainProjection_smul D g zD
      exact (congrArg (punctureFillSome (stableCuspFillData S h hS hK hSo hSc)) hπ).trans
        (stableCuspFilledDiscMap_finite S h hS hK hSo hSc z).symm
    · exact (hp hgD).elim

/-- The genuine augmented projection is continuous for its actual glued domain topology. -/
theorem stableCuspAugmentedProjection_continuous {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    Continuous (stableCuspAugmentedProjection S h hS hK hSo hSc) := by
  apply continuous_def.mpr
  intro U hU
  apply (stableCuspAugmented_isOpen_iff S h hS _).mpr
  constructor
  · have he : stableCuspAugmentedProjection S h hS hK hSo hSc ∘ stableCuspAugmentedOld S h hS =
        punctureFillSome (stableCuspFillData S h hS hK hSo hSc) ∘ mobiusDomainProjection D :=
      funext (stableCuspAugmentedProjection_old S h hS hK hSo hSc)
    change IsOpen ((stableCuspAugmentedProjection S h hS hK hSo hSc ∘
      stableCuspAugmentedOld S h hS) ⁻¹' U)
    rw [he]
    exact hU.preimage ((punctureFillSome_continuous _).comp (mobiusDomainProjection_continuous D))
  · intro g
    have he : stableCuspAugmentedProjection S h hS hK hSo hSc ∘ stableCuspAugmentedCusp S h hS g =
        punctureFillDiscMap (stableCuspFillData S h hS hK hSo hSc) ∘ stableCuspCompletionToDisc h :=
      funext (stableCuspAugmentedProjection_cusp S hD hT h hS hK hSo hSc g)
    change IsOpen ((stableCuspAugmentedProjection S h hS hK hSo hSc ∘
      stableCuspAugmentedCusp S h hS g) ⁻¹' U)
    rw [he]
    exact hU.preimage ((punctureFillDiscMap_continuous _).comp (stableCuspCompletionToDisc_continuous h))

theorem stableCuspAugmentedProjection_surjective {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    Function.Surjective (stableCuspAugmentedProjection S h hS hK hSo hSc) := by
  intro p
  change Option (MobiusDomainQuotient D) at p
  cases p with
  | none =>
    refine ⟨stableCuspAugmentedCusp S h hS 1 (stableCuspCompletionInfinity h), ?_⟩
    exact (stableCuspAugmentedProjection_cusp S hD hT h hS hK hSo hSc 1 _).trans
      ((punctureFillDiscMap_eq_infinity (stableCuspFillData S h hS hK hSo hSc)
        (stableCuspCompletionToDisc h (stableCuspCompletionInfinity h))).mpr rfl)
  | some x =>
    obtain ⟨z, hz⟩ := mobiusDomainProjection_surjective D x
    refine ⟨stableCuspAugmentedOld S h hS z, ?_⟩
    exact (stableCuspAugmentedProjection_old S h hS hK hSo hSc z).trans
      (congrArg (punctureFillSome (stableCuspFillData S h hS hK hSo hSc)) hz)

/-- Openness is proved using all original domain points and all actual cusp lifts. -/
theorem stableCuspAugmentedProjection_isOpenMap {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    IsOpenMap (stableCuspAugmentedProjection S h hS hK hSo hSc) := by
  intro U hU
  have ho := (stableCuspAugmented_isOpen_iff S h hS U).mp hU
  have heq : stableCuspAugmentedProjection S h hS hK hSo hSc '' U =
      punctureFillSome (stableCuspFillData S h hS hK hSo hSc) ''
        (mobiusDomainProjection D '' ((stableCuspAugmentedOld S h hS) ⁻¹' U)) ∪
      ⋃ g : G, punctureFillDiscMap (stableCuspFillData S h hS hK hSo hSc) ''
        (stableCuspCompletionToDisc h '' ((stableCuspAugmentedCusp S h hS g) ⁻¹' U)) := by
    ext p
    constructor
    · rintro ⟨a, haU, rfl⟩
      by_cases haD : a.val ∈ D.carrier
      · left
        let z : D.carrier := ⟨a.val, haD⟩
        have hea : stableCuspAugmentedOld S h hS z = a := Subtype.ext rfl
        refine ⟨mobiusDomainProjection D z, ⟨z, ?_, rfl⟩, ?_⟩
        · change stableCuspAugmentedOld S h hS z ∈ U
          rw [hea]
          exact haU
        · exact (stableCuspAugmentedProjection_old S h hS hK hSo hSc z).symm.trans
            (congrArg (stableCuspAugmentedProjection S h hS hK hSo hSc) hea)
      · right
        obtain ⟨g, hg⟩ := a.property.resolve_left haD
        have hea : stableCuspAugmentedCusp S h hS g (stableCuspCompletionInfinity h) = a :=
          Subtype.ext hg
        apply Set.mem_iUnion.mpr
        refine ⟨g, stableCuspCompletionToDisc h (stableCuspCompletionInfinity h),
          ⟨stableCuspCompletionInfinity h, ?_, rfl⟩, ?_⟩
        · change stableCuspAugmentedCusp S h hS g (stableCuspCompletionInfinity h) ∈ U
          rw [hea]
          exact haU
        · exact (stableCuspAugmentedProjection_cusp S hD hT h hS hK hSo hSc g _).symm.trans
            (congrArg (stableCuspAugmentedProjection S h hS hK hSo hSc) hea)
    · rintro (⟨x, ⟨z, hz, rfl⟩, rfl⟩ | hp)
      · exact ⟨stableCuspAugmentedOld S h hS z, hz,
          stableCuspAugmentedProjection_old S h hS hK hSo hSc z⟩
      · obtain ⟨g, w, ⟨q, hq, rfl⟩, hp⟩ := Set.mem_iUnion.mp hp
        exact ⟨stableCuspAugmentedCusp S h hS g q, hq,
          (stableCuspAugmentedProjection_cusp S hD hT h hS hK hSo hSc g q).trans hp⟩
  rw [heq]
  apply IsOpen.union
  · exact punctureFillSome_isOpenMap _ _ ((mobiusDomainProjection_isOpenQuotientMap D).isOpenMap _ ho.1)
  · apply isOpen_iUnion
    intro g
    exact punctureFillDiscMap_isOpenMap _ _ (stableCuspCompletionToDisc_isOpenMap h _ (ho.2 g))

theorem stableCuspAugmentedProjection_of_mem {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (p : StableCuspAugmentedDomain S h hS) (hp : p.val ∈ D.carrier) :
    stableCuspAugmentedProjection S h hS hK hSo hSc p =
      punctureFillSome (stableCuspFillData S h hS hK hSo hSc)
        (mobiusDomainProjection D ⟨p.val, hp⟩) := by
  classical
  unfold stableCuspAugmentedProjection
  split_ifs
  rfl

theorem stableCuspAugmentedProjection_of_not_mem {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (p : StableCuspAugmentedDomain S h hS) (hp : p.val ∉ D.carrier) :
    stableCuspAugmentedProjection S h hS hK hSo hSc p =
      punctureFillInfinity (stableCuspFillData S h hS hK hSo hSc) := by
  classical
  unfold stableCuspAugmentedProjection
  split_ifs
  rfl

/-- Named sphere coordinates preserve the augmented domain's declared topology in quotients. -/
def stableCuspAugmentedSphere {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) :
    StableCuspAugmentedDomain S h hS → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := Subtype.val

/-- The fibers are exactly the original full Mobius-group orbits on the genuinely
augmented original sphere domain. -/
theorem stableCuspAugmentedProjection_orbitRel_iff {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (a b : StableCuspAugmentedDomain S h hS) :
    (MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap
        (stableCuspAugmentedSphere S h hS) a b ↔
      stableCuspAugmentedProjection S h hS hK hSo hSc a =
        stableCuspAugmentedProjection S h hS hK hSo hSc b := by
  classical
  constructor
  · rintro ⟨g, hg⟩
    have hga : g • b.val = a.val := hg
    have hiff : a.val ∈ D.carrier ↔ b.val ∈ D.carrier := by
      constructor
      · intro ha
        have hh := D.invariant g⁻¹ a.val ha
        rw [← hga, inv_smul_smul] at hh
        exact hh
      · intro hb
        exact hga ▸ D.invariant g b.val hb
    by_cases ha : a.val ∈ D.carrier
    · have hb := hiff.mp ha
      rw [stableCuspAugmentedProjection_of_mem S h hS hK hSo hSc a ha,
        stableCuspAugmentedProjection_of_mem S h hS hK hSo hSc b hb]
      apply congrArg (punctureFillSome _)
      exact Quotient.sound ⟨g, Subtype.ext hga⟩
    · have hb : b.val ∉ D.carrier := fun hb => ha (hiff.mpr hb)
      rw [stableCuspAugmentedProjection_of_not_mem S h hS hK hSo hSc a ha,
        stableCuspAugmentedProjection_of_not_mem S h hS hK hSo hSc b hb]
  · intro he
    by_cases ha : a.val ∈ D.carrier
    · by_cases hb : b.val ∈ D.carrier
      · rw [stableCuspAugmentedProjection_of_mem S h hS hK hSo hSc a ha,
          stableCuspAugmentedProjection_of_mem S h hS hK hSo hSc b hb] at he
        have hπ := punctureFillSome_injective (stableCuspFillData S h hS hK hSo hSc) he
        obtain ⟨g, hg⟩ := Quotient.exact hπ
        exact ⟨g, congrArg Subtype.val hg⟩
      · rw [stableCuspAugmentedProjection_of_mem S h hS hK hSo hSc a ha,
          stableCuspAugmentedProjection_of_not_mem S h hS hK hSo hSc b hb] at he
        change (some _ : Option (MobiusDomainQuotient D)) = none at he
        cases he
    · by_cases hb : b.val ∈ D.carrier
      · rw [stableCuspAugmentedProjection_of_not_mem S h hS hK hSo hSc a ha,
          stableCuspAugmentedProjection_of_mem S h hS hK hSo hSc b hb] at he
        change (none : Option (MobiusDomainQuotient D)) = some _ at he
        cases he
      · obtain ⟨g, hg⟩ := a.property.resolve_left ha
        obtain ⟨k, hk⟩ := b.property.resolve_left hb
        refine ⟨g * k⁻¹, ?_⟩
        change (g * k⁻¹) • b.val = a.val
        have hks : k • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = b.val := hk
        rw [← hks, mul_smul, inv_smul_smul]
        exact hg

/-- The original full-group orbit quotient, using the actual augmented-domain topology. -/
abbrev StableCuspAugmentedQuotient {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) :=
  Quotient ((MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap
    (stableCuspAugmentedSphere S h hS))

/-- The genuine full-group orbit quotient of the augmented domain has precisely the
filled old-quotient topology; its homeomorphism is induced by original representatives. -/
def stableCuspAugmentedQuotientHomeomorph {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    StableCuspAugmentedQuotient S h hS ≃ₜ PunctureFill (stableCuspFillData S h hS hK hSo hSc) := by
  let F : C(StableCuspAugmentedDomain S h hS, PunctureFill (stableCuspFillData S h hS hK hSo hSc)) :=
    ⟨stableCuspAugmentedProjection S h hS hK hSo hSc,
      stableCuspAugmentedProjection_continuous S hD hT h hS hK hSo hSc⟩
  have hF : IsOpenQuotientMap F :=
    ⟨stableCuspAugmentedProjection_surjective S hD hT h hS hK hSo hSc, F.continuous,
      stableCuspAugmentedProjection_isOpenMap S hD hT h hS hK hSo hSc⟩
  exact (Homeomorph.Quotient.congrRight
    (stableCuspAugmentedProjection_orbitRel_iff S h hS hK hSo hSc)).trans hF.isQuotientMap.homeomorph

theorem stableCuspAugmentedCusp_val {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (g : G) (p : StableCuspCompletion h) :
    (stableCuspAugmentedCusp S h hS g p).val = g.val.val (stableCuspCompletionSphere h p) := by
  cases p <;> rfl

theorem stableCuspAugmentedCusp_injective {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) (g : G) :
    Function.Injective (stableCuspAugmentedCusp S h hS g) := by
  intro p q he
  have hv := congrArg Subtype.val he
  rw [stableCuspAugmentedCusp_val, stableCuspAugmentedCusp_val] at hv
  exact stableCuspCompletionSphere_injective h (g.val.val.injective hv)

theorem stableCuspAugmentedCusp_continuous {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) (g : G) :
    Continuous (stableCuspAugmentedCusp S h hS g) := by
  apply continuous_def.mpr
  intro U hU
  exact ((stableCuspAugmented_isOpen_iff S h hS U).mp hU).2 g

/-- Distinct cusp-stabilizer cosets have disjoint genuine completed-cusp images. The
explicit repaired cusp-stabilizer condition is used only at the actual ideal points. -/
theorem stableCuspAugmentedCusp_disjoint {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup)
    (g k : G) (hn : (g⁻¹ * k).val ∉ stableTranslationGroup) :
    Disjoint (Set.range (stableCuspAugmentedCusp S h hS g))
      (Set.range (stableCuspAugmentedCusp S h hS k)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨p, rfl⟩ ⟨q, he⟩
  have hv := congrArg Subtype.val he
  rw [stableCuspAugmentedCusp_val, stableCuspAugmentedCusp_val] at hv
  cases p with
  | none =>
    cases q with
    | none =>
      change k • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = g • (∞ :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hv
      have hf : (g⁻¹ * k) • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ∞ := by
        rw [mul_smul, hv, inv_smul_smul]
      exact hn (hfix (g⁻¹ * k).val (g⁻¹ * k).property hf)
    | some w =>
      change k • (w.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = g • (∞ :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hv
      have hw : (w.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ D.carrier := S.subset_domain (by
        rw [hS]
        exact ⟨w.val, w.property, rfl⟩)
      have hk := D.invariant k (w.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hw
      rw [hv] at hk
      exact stableCusp_orbit_infty_not_mem G D hD hT g hk
  | some z =>
    cases q with
    | none =>
      change k • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = g • (z.val :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hv
      have hz : (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ D.carrier := S.subset_domain (by
        rw [hS]
        exact ⟨z.val, z.property, rfl⟩)
      have hg := D.invariant g (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hz
      rw [← hv] at hg
      exact stableCusp_orbit_infty_not_mem G D hD hT k hg
    | some w =>
      have hz : (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ S.carrier := by rw [hS]; exact ⟨z.val, z.property, rfl⟩
      have hw : (w.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ S.carrier := by rw [hS]; exact ⟨w.val, w.property, rfl⟩
      change k • (w.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = g • (z.val :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hv
      have hf : (g⁻¹ * k) • (w.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
        rw [mul_smul, hv, inv_smul_smul]
      have hnS : (g⁻¹ * k).val ∉ S.stabilizer := by rw [hK]; exact hn
      exact Set.disjoint_left.mp (S.separated _ (g⁻¹ * k).property hnS) ⟨_, hw, hf⟩ hz

/-- The genuine finite part of a translated cusp, in the original domain topology. -/
def stableCuspAugmentedFinite {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) (g : G) :
    stableCuspHalfPlane h → D.carrier := fun z =>
  ⟨g.val.val (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), D.invariant g _ (S.subset_domain (by
    rw [hS]
    exact ⟨z.val, z.property, rfl⟩))⟩

theorem stableCuspAugmentedFinite_isOpenMap {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) (g : G) :
    IsOpenMap (stableCuspAugmentedFinite S h hS g) := by
  have hH : IsOpen (stableCuspHalfPlane h) := isOpen_lt continuous_const Complex.continuous_im
  have hm : IsOpenMap (fun z : stableCuspHalfPlane h => g.val.val (z.val :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph g.val).isOpenMap.comp
      (OnePoint.isOpenEmbedding_coe.isOpenMap.comp hH.isOpenEmbedding_subtypeVal.isOpenMap)
  exact hm.codRestrict _

theorem stableCuspAugmentedCusp_preimage_old {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h) (g : G) (U : Set (StableCuspCompletion h)) :
    (stableCuspAugmentedOld S h hS) ⁻¹' ((stableCuspAugmentedCusp S h hS g) '' U) =
      (stableCuspAugmentedFinite S h hS g) '' ((stableCuspCompletionSome h) ⁻¹' U) := by
  ext z
  constructor
  · rintro ⟨p, hp, he⟩
    cases p with
    | none =>
      have heq : g.val.val ∞ = z.val := congrArg Subtype.val he
      exact (stableCusp_orbit_infty_not_mem G D hD hT g (heq.symm ▸ z.property)).elim
    | some w =>
      have hv := congrArg (stableCuspAugmentedSphere S h hS) he
      exact ⟨w, hp, Subtype.ext hv⟩
  · rintro ⟨w, hw, he⟩
    exact ⟨stableCuspCompletionSome h w, hw,
      (congrArg (stableCuspAugmentedOld S h hS) he)⟩

theorem stableCuspAugmentedCusp_integer_transition {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (g k : G) (n : ℤ)
    (hn : (g⁻¹ * k).val = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (n : ℂ)) :
    stableCuspAugmentedCusp S h hS k =
      stableCuspAugmentedCusp S h hS g ∘ stableCuspCompletionIntegerTranslation h n := by
  funext p
  apply Subtype.ext
  change (stableCuspAugmentedCusp S h hS k p).val =
    (stableCuspAugmentedCusp S h hS g (stableCuspCompletionIntegerTranslation h n p)).val
  rw [stableCuspAugmentedCusp_val, stableCuspAugmentedCusp_val,
    stableCuspCompletionIntegerTranslation_sphere, ← hn]
  change k • stableCuspCompletionSphere h p = g • ((g⁻¹ * k) • stableCuspCompletionSphere h p)
  rw [← mul_smul]
  simp

/--
Under the necessary cusp-stabilizer repair, every genuine translated completed cusp
embeds openly. Thus its height-tail neighborhoods are actual open neighborhoods, as in this formulation.
-/
theorem stableCuspAugmentedCusp_isOpenEmbedding {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup) (g : G) :
    Topology.IsOpenEmbedding (stableCuspAugmentedCusp S h hS g) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (stableCuspAugmentedCusp_continuous S h hS g) (stableCuspAugmentedCusp_injective S h hS g)
  intro U hU
  apply (stableCuspAugmented_isOpen_iff S h hS _).mpr
  constructor
  · rw [stableCuspAugmentedCusp_preimage_old S hD hT h hS g U]
    exact stableCuspAugmentedFinite_isOpenMap S h hS g _
      (hU.preimage (stableCuspCompletion_some_isOpenEmbedding h).continuous)
  · intro k
    by_cases hf : (g⁻¹ * k).val ∈ stableTranslationGroup
    · obtain ⟨n, hn⟩ := (stableTranslationGroup_mem _).mp hf
      rw [stableCuspAugmentedCusp_integer_transition S h hS g k n hn, Set.preimage_comp,
        Set.preimage_image_eq _ (stableCuspAugmentedCusp_injective S h hS g)]
      exact hU.preimage (stableCuspCompletionIntegerTranslation h n).continuous
    · have hd := stableCuspAugmentedCusp_disjoint S hD hT h hS hK hfix g k hf
      have heq : (stableCuspAugmentedCusp S h hS k) ⁻¹' ((stableCuspAugmentedCusp S h hS g) '' U) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨q, _, he⟩ := hp
        exact Set.disjoint_left.mp hd ⟨q, he⟩ ⟨p, rfl⟩
      rw [heq]
      exact isOpen_empty

/-- Genuine all-group height-tail neighborhoods at an actual added cusp. -/
def stableCuspAugmentedHeightTail {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) (g : G) (t : ℝ) :
    Set (StableCuspAugmentedDomain S h hS) :=
  {p | p.val = g.val.val ∞ ∨ ∃ z : ℂ, t < z.im ∧ g.val.val (z :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = p.val}

theorem stableCuspAugmentedHeightTail_eq_image {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (g : G) (t : ℝ) (ht : h < t) :
    stableCuspAugmentedHeightTail S h hS g t =
      stableCuspAugmentedCusp S h hS g '' stableCuspCompletionTail h t := by
  ext p
  constructor
  · rintro (hp | ⟨z, hz, he⟩)
    · exact ⟨stableCuspCompletionInfinity h, stableCuspCompletionTail_none h t, Subtype.ext hp.symm⟩
    · let w : stableCuspHalfPlane h := ⟨z, ht.trans hz⟩
      exact ⟨stableCuspCompletionSome h w, (stableCuspCompletionTail_some h t w).mpr hz, Subtype.ext he⟩
  · rintro ⟨q, hq, rfl⟩
    cases q with
    | none => exact Or.inl rfl
    | some z => exact Or.inr ⟨z.val, (stableCuspCompletionTail_some h t z).mp hq, rfl⟩

/-- The new-point neighborhood filter is exactly the original all-group uniform-height
cusp filter, with the necessary cusp-stabilizer repair made explicit. -/
theorem stableCuspAugmented_mem_nhds_iff {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup) (g : G)
    (U : Set (StableCuspAugmentedDomain S h hS)) :
    U ∈ 𝓝 (stableCuspAugmentedCusp S h hS g (stableCuspCompletionInfinity h)) ↔
      ∃ t : ℝ, h < t ∧ stableCuspAugmentedHeightTail S h hS g t ⊆ U := by
  have hj := stableCuspAugmentedCusp_isOpenEmbedding S hD hT h hS hK hfix g
  rw [← hj.map_nhds_eq (stableCuspCompletionInfinity h)]
  change (stableCuspAugmentedCusp S h hS g) ⁻¹' U ∈ 𝓝 (stableCuspCompletionInfinity h) ↔ _
  rw [stableCuspCompletion_mem_nhds_iff]
  constructor
  · rintro ⟨t, ht, hsub⟩
    refine ⟨t, ht, ?_⟩
    rw [stableCuspAugmentedHeightTail_eq_image S h hS g t ht]
    exact Set.image_subset_iff.mpr hsub
  · rintro ⟨t, ht, hsub⟩
    rw [stableCuspAugmentedHeightTail_eq_image S h hS g t ht] at hsub
    exact ⟨t, ht, Set.image_subset_iff.mp hsub⟩

theorem stableCuspAugmentedOld_injective {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) :
    Function.Injective (stableCuspAugmentedOld S h hS) := by
  intro a b he
  exact Subtype.ext (congrArg (stableCuspAugmentedSphere S h hS) he)

theorem stableCuspAugmentedOld_continuous {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) :
    Continuous (stableCuspAugmentedOld S h hS) := by
  apply continuous_def.mpr
  intro U hU
  exact ((stableCuspAugmented_isOpen_iff S h hS U).mp hU).1

/-- The original invariant domain retains exactly its original topology as an open subspace. -/
theorem stableCuspAugmentedOld_isOpenEmbedding {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h) :
    Topology.IsOpenEmbedding (stableCuspAugmentedOld S h hS) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (stableCuspAugmentedOld_continuous S h hS) (stableCuspAugmentedOld_injective S h hS)
  intro V hV
  apply (stableCuspAugmented_isOpen_iff S h hS _).mpr
  constructor
  · simpa only [Set.preimage_image_eq _ (stableCuspAugmentedOld_injective S h hS)] using hV
  · intro g
    let f := stableCuspAugmentedFinite S h hS g
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact (_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary g.val).comp
        (OnePoint.isOpenEmbedding_coe.continuous.comp continuous_subtype_val)
    have heq : (stableCuspAugmentedCusp S h hS g) ⁻¹' ((stableCuspAugmentedOld S h hS) '' V) =
        (stableCuspCompletionSome h) '' (f ⁻¹' V) := by
      ext p
      cases p with
      | none =>
        constructor
        · rintro ⟨z, hz, he⟩
          have heq : z.val = g.val.val ∞ := congrArg (stableCuspAugmentedSphere S h hS) he
          exact (stableCusp_orbit_infty_not_mem G D hD hT g (heq ▸ z.property)).elim
        · rintro ⟨z, _, he⟩
          cases he
      | some z =>
        constructor
        · rintro ⟨w, hw, he⟩
          have hv := congrArg (stableCuspAugmentedSphere S h hS) he
          have heq : w = f z := Subtype.ext hv
          refine ⟨z, ?_, rfl⟩
          change f z ∈ V
          exact heq ▸ hw
        · rintro ⟨w, hw, he⟩
          have hwz : w = z := Option.some_injective _ he
          subst w
          exact ⟨f z, hw, rfl⟩
    rw [heq]
    exact (stableCuspCompletion_some_isOpenEmbedding h).isOpenMap _ (hV.preimage hf)

/-- The actual full-group quotient of the actual augmented domain is a Riemann surface
whose complex structure fills the canonical old-quotient puncture. -/
def stableCuspAugmentedQuotientRiemannSurface {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup) :
    RiemannSurface (StableCuspAugmentedQuotient S h hS) := by
  let R := stableCuspFilledRiemannSurface S hD hT h hS hK hSo hSc hfix
  let E := stableCuspAugmentedQuotientHomeomorph S hD hT h hS hK hSo hSc
  letI : T2Space (PunctureFill (stableCuspFillData S h hS hK hSo hSc)) := R.t2Space
  letI : ConnectedSpace (PunctureFill (stableCuspFillData S h hS hK hSo hSc)) := R.connectedSpace
  exact { R.toRiemannAtlas.liftLocalHomeomorph E E.isOpenEmbedding.isLocalHomeomorph with
    t2Space := E.isEmbedding.t2Space
    connectedSpace := E.symm.surjective.connectedSpace E.symm.continuous }

theorem stableCuspAugmentedQuotientHomeomorph_apply_mk {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (p : StableCuspAugmentedDomain S h hS) :
    stableCuspAugmentedQuotientHomeomorph S hD hT h hS hK hSo hSc (Quotient.mk _ p) =
      stableCuspAugmentedProjection S h hS hK hSo hSc p := rfl

/-- The actual original quotient inclusion into the filled actual orbit quotient. -/
def stableCuspAugmentedQuotientOld {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    MobiusDomainQuotient D → StableCuspAugmentedQuotient S h hS :=
  (stableCuspAugmentedQuotientHomeomorph S hD hT h hS hK hSo hSc).symm ∘
    punctureFillSome (stableCuspFillData S h hS hK hSo hSc)

theorem stableCuspAugmentedQuotientOld_projection {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (z : D.carrier) :
    stableCuspAugmentedQuotientOld S hD hT h hS hK hSo hSc (mobiusDomainProjection D z) =
      Quotient.mk _ (stableCuspAugmentedOld S h hS z) := by
  apply (stableCuspAugmentedQuotientHomeomorph S hD hT h hS hK hSo hSc).injective
  rw [stableCuspAugmentedQuotientOld, Function.comp_apply, Homeomorph.apply_symm_apply,
    stableCuspAugmentedQuotientHomeomorph_apply_mk, stableCuspAugmentedProjection_old]

theorem stableCuspAugmentedQuotientOld_isOpenEmbedding {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    Topology.IsOpenEmbedding (stableCuspAugmentedQuotientOld S hD hT h hS hK hSo hSc) :=
  (stableCuspAugmentedQuotientHomeomorph S hD hT h hS hK hSo hSc).symm.isOpenEmbedding.comp
    (punctureFillSome_isOpenEmbedding _)

theorem stableCuspAugmentedQuotientOld_analytic {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (hK : S.stabilizer = stableTranslationGroup) (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup) :
    RiemannAnalyticMap (mobiusQuotientRiemannSurface D hD).toRiemannAtlas
      (stableCuspAugmentedQuotientRiemannSurface S hD hT h hS hK hSo hSc hfix).toRiemannAtlas
      (stableCuspAugmentedQuotientOld S hD hT h hS hK hSo hSc) := by
  let E := stableCuspAugmentedQuotientHomeomorph S hD hT h hS hK hSo hSc
  have hp := (stableCuspFilledRiemannSurface S hD hT h hS hK hSo hSc
    hfix).toRiemannAtlas.liftLocalHomeomorph_projection_analytic
    E E.isOpenEmbedding.isLocalHomeomorph
  have ha : RiemannAnalyticMap (mobiusQuotientRiemannSurface D hD).toRiemannAtlas
      (stableCuspFilledRiemannSurface S hD hT h hS hK hSo hSc hfix).toRiemannAtlas
      (E ∘ stableCuspAugmentedQuotientOld S hD hT h hS hK hSo hSc) := by
    have heq : E ∘ stableCuspAugmentedQuotientOld S hD hT h hS hK hSo hSc =
        punctureFillSome (stableCuspFillData S h hS hK hSo hSc) := by
      funext x
      exact E.apply_symm_apply _
    rw [heq]
    exact stableCuspFilled_inclusion_analytic S hD hT h hS hK hSo hSc hfix
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_localHomeomorph hp E.isOpenEmbedding.isLocalHomeomorph
    (stableCuspAugmentedQuotientOld_isOpenEmbedding S hD hT h hS hK hSo hSc).continuous ha

/-- The genuine completed-cusp topology is finer than the actual sphere topology. -/
theorem stableCuspCompletionSphere_continuous (h : ℝ) : Continuous (stableCuspCompletionSphere h) := by
  apply continuous_def.mpr
  intro U hU
  let V : Set (stableCuspHalfPlane h) := {z | (z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈
    U}
  have hV : IsOpen V := hU.preimage (OnePoint.isOpenEmbedding_coe.continuous.comp continuous_subtype_val)
  have hfin : IsOpen ((stableCuspCompletionSome h) '' V) :=
    (stableCuspCompletion_some_isOpenEmbedding h).isOpenMap V hV
  by_cases hinfty : (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ U
  · have hK := ((OnePoint.isOpen_iff_of_mem' hinfty).mp hU).1
    obtain ⟨R, _hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
    have htail : stableCuspCompletionTail h (R + 1) ⊆ stableCuspCompletionSphere h ⁻¹' U := by
      intro p hp
      cases p with
      | none => exact hinfty
      | some z =>
        have hz := (stableCuspCompletionTail_some h (R + 1) z).mp hp
        by_contra hn
        have hb : ‖z.val‖ ≤ R := hR z.val hn
        have him : z.val.im ≤ ‖z.val‖ := (le_abs_self _).trans (Complex.abs_im_le_norm _)
        linarith
    have heq : stableCuspCompletionSphere h ⁻¹' U =
        (stableCuspCompletionSome h) '' V ∪ stableCuspCompletionTail h (R + 1) := by
      apply Set.Subset.antisymm
      · intro p hp
        cases p with
        | none => exact Or.inr (stableCuspCompletionTail_none h (R + 1))
        | some z => exact Or.inl ⟨z, hp, rfl⟩
      · rintro p (⟨z, hz, rfl⟩ | hp)
        · exact hz
        · exact htail hp
    rw [heq]
    exact hfin.union (stableCuspCompletionTail_isOpen h (R + 1))
  · have heq : stableCuspCompletionSphere h ⁻¹' U = (stableCuspCompletionSome h) '' V := by
      apply Set.Subset.antisymm
      · intro p hp
        cases p with
        | none => exact (hinfty hp).elim
        | some z => exact ⟨z, hp, rfl⟩
      · rintro _ ⟨z, hz, rfl⟩
        exact hz
    rw [heq]
    exact hfin

theorem stableCuspAugmentedSphere_continuous {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) :
    Continuous (stableCuspAugmentedSphere S h hS) := by
  apply continuous_def.mpr
  intro U hU
  apply (stableCuspAugmented_isOpen_iff S h hS _).mpr
  constructor
  · exact hU.preimage continuous_subtype_val
  · intro g
    have he : stableCuspAugmentedSphere S h hS ∘ stableCuspAugmentedCusp S h hS g =
        g.val.val ∘ stableCuspCompletionSphere h := funext (stableCuspAugmentedCusp_val S h hS g)
    change IsOpen ((stableCuspAugmentedSphere S h hS ∘ stableCuspAugmentedCusp S h hS g) ⁻¹' U)
    rw [he]
    exact hU.preimage ((_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary g.val).comp
      (stableCuspCompletionSphere_continuous h))

theorem stableCuspAugmented_t2Space {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) :
    T2Space (StableCuspAugmentedDomain S h hS) := by
  constructor
  intro p q hpq
  have hne : stableCuspAugmentedSphere S h hS p ≠ stableCuspAugmentedSphere S h hS q :=
    fun he => hpq (Subtype.ext he)
  obtain ⟨U, V, hU, hV, hp, hq, hd⟩ := t2_separation hne
  exact ⟨(stableCuspAugmentedSphere S h hS) ⁻¹' U, (stableCuspAugmentedSphere S h hS) ⁻¹' V,
    hU.preimage (stableCuspAugmentedSphere_continuous S h hS),
    hV.preimage (stableCuspAugmentedSphere_continuous S h hS), hp, hq, hd.preimage _⟩

/-- A compact neighborhood pulls back through an open embedding into a Hausdorff space.
Only the given neighborhood is compact; no global local compactness is assumed. -/
theorem isOpenEmbedding_compact_nhds_pullback {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B]
    (j : A → B) (hj : Topology.IsOpenEmbedding j) (a : A)
    (K : Set B) (hK : IsCompact K) (haK : K ∈ 𝓝 (j a)) :
    ∃ L : Set A, IsCompact L ∧ L ∈ 𝓝 a := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let W : Set B := interior K
  let i : W → K := fun z => ⟨z.val, interior_subset z.property⟩
  have hi : Topology.IsOpenEmbedding i := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact continuous_subtype_val.subtype_mk _
    · intro x y he
      exact Subtype.ext (congrArg (fun z : K => z.val) he)
    · exact isOpen_interior.isOpenEmbedding_subtypeVal.isOpenMap.codRestrict _
  have : LocallyCompactSpace W := hi.locallyCompactSpace
  let P : Set A := j ⁻¹' W
  have hP : IsOpen P := isOpen_interior.preimage hj.continuous
  have hf : Topology.IsOpenEmbedding (fun z : P => j z.val) :=
    hj.comp hP.isOpenEmbedding_subtypeVal
  let f : P → W := fun z => ⟨j z.val, z.property⟩
  have hff : Topology.IsOpenEmbedding f := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact hf.continuous.subtype_mk _
    · intro x y he
      exact hf.injective (congrArg (fun z : W => z.val) he)
    · exact hf.isOpenMap.codRestrict _
  have : LocallyCompactSpace P := hff.locallyCompactSpace
  let aP : P := ⟨a, mem_interior_iff_mem_nhds.mpr haK⟩
  obtain ⟨L, hL, haL⟩ := exists_compact_mem_nhds aP
  exact ⟨Subtype.val '' L, hL.image continuous_subtype_val,
    hP.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds haL⟩

/-- Every actual new cusp point in the actual augmented domain has no compact neighborhood. -/
theorem stableCuspAugmented_no_compact_nhds {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup) (g : G) :
    ¬∃ K : Set (StableCuspAugmentedDomain S h hS), IsCompact K ∧
      K ∈ 𝓝 (stableCuspAugmentedCusp S h hS g (stableCuspCompletionInfinity h)) := by
  have : T2Space (StableCuspAugmentedDomain S h hS) := stableCuspAugmented_t2Space S h hS
  rintro ⟨K, hKc, hKn⟩
  obtain ⟨L, hLc, hLn⟩ := isOpenEmbedding_compact_nhds_pullback
    (stableCuspAugmentedCusp S h hS g)
    (stableCuspAugmentedCusp_isOpenEmbedding S hD hT h hS hK hfix g)
    (stableCuspCompletionInfinity h) K hKc hKn
  exact stableCuspCompletion_no_compact_nhds h ⟨L, hLc, hLn⟩

theorem stableCuspAugmented_not_locallyCompact {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup) :
    ¬LocallyCompactSpace (StableCuspAugmentedDomain S h hS) := by
  intro hloc
  have : LocallyCompactSpace (StableCuspAugmentedDomain S h hS) := hloc
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds
    (stableCuspAugmentedCusp S h hS (1 : G) (stableCuspCompletionInfinity h))
  exact stableCuspAugmented_no_compact_nhds S hD hT h hS hK hfix 1 ⟨K, hKc, hKn⟩

theorem stableCuspAugmented_invariant {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D
  : MobiusInvariantDomain G}
    (g : G) (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hp : p ∈ D.carrier ∨ ∃ k : G, k.val.val ∞ = p) :
    g • p ∈ D.carrier ∨ ∃ k : G, k.val.val ∞ = g • p := by
  rcases hp with hp | ⟨k, rfl⟩
  · exact Or.inl (D.invariant g p hp)
  · exact Or.inr ⟨g * k, mul_smul g k (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)⟩

/-- The original actual Mobius subgroup acts on the actual augmented domain. -/
instance stableCuspAugmentedAction {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) :
    MulAction G (StableCuspAugmentedDomain S h hS) where
  smul g p := ⟨g • p.val, stableCuspAugmented_invariant g p.val p.property⟩
  one_smul p := Subtype.ext (one_smul G p.val)
  mul_smul g k p := Subtype.ext (mul_smul g k p.val)

theorem stableCuspAugmented_smul_old {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D
  : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) (g : G) (z : D.carrier) :
    g • stableCuspAugmentedOld S h hS z = stableCuspAugmentedOld S h hS (g • z) := rfl

theorem stableCuspAugmented_smul_cusp {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D
  : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (g k : G) (p : StableCuspCompletion h) :
    g • stableCuspAugmentedCusp S h hS k p = stableCuspAugmentedCusp S h hS (g * k) p := by
  apply Subtype.ext
  change g • (stableCuspAugmentedCusp S h hS k p).val =
    (stableCuspAugmentedCusp S h hS (g * k) p).val
  rw [stableCuspAugmentedCusp_val, stableCuspAugmentedCusp_val]
  exact (mul_smul g k (stableCuspCompletionSphere h p)).symm

instance stableCuspAugmentedContinuousConstSMul {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) :
    ContinuousConstSMul G (StableCuspAugmentedDomain S h hS) where
  continuous_const_smul g := by
    apply continuous_def.mpr
    intro U hU
    have ho := (stableCuspAugmented_isOpen_iff S h hS U).mp hU
    apply (stableCuspAugmented_isOpen_iff S h hS _).mpr
    constructor
    · have he : (fun p => g • p) ∘ stableCuspAugmentedOld S h hS =
          stableCuspAugmentedOld S h hS ∘ (fun z : D.carrier => g • z) :=
        funext (stableCuspAugmented_smul_old S h hS g)
      change IsOpen (((fun p => g • p) ∘ stableCuspAugmentedOld S h hS) ⁻¹' U)
      rw [he]
      exact ho.1.preimage (continuous_const_smul g)
    · intro k
      have he : (fun p => g • p) ∘ stableCuspAugmentedCusp S h hS k =
          stableCuspAugmentedCusp S h hS (g * k) :=
        funext (stableCuspAugmented_smul_cusp S h hS g k)
      change IsOpen (((fun p => g • p) ∘ stableCuspAugmentedCusp S h hS k) ⁻¹' U)
      rw [he]
      exact ho.2 (g * k)

/-- The restricted sphere orbit relation is exactly the orbit relation of the actual
extended group action, rather than an auxiliary relation. -/
theorem stableCuspAugmented_orbitRel_iff {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h)
    (p q : StableCuspAugmentedDomain S h hS) :
    MulAction.orbitRel G (StableCuspAugmentedDomain S h hS) p q ↔
      (MulAction.orbitRel G _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap (stableCuspAugmentedSphere S h hS) p q := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg (stableCuspAugmentedSphere S h hS) hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩

/-- The quotient is equivalently the native orbit quotient of the genuinely extended action. -/
def stableCuspAugmentedNativeQuotientHomeomorph {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D) (h : ℝ) (hS : S.carrier = stableCuspSphere h) :
    Quotient (MulAction.orbitRel G (StableCuspAugmentedDomain S h hS)) ≃ₜ StableCuspAugmentedQuotient S h hS :=
  Homeomorph.Quotient.congrRight (stableCuspAugmented_orbitRel_iff S h hS)

/-- The actual filled coordinate chart on the actual augmented full-group quotient. -/
def stableCuspAugmentedNewChart {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D :
  MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    OpenPartialHomeomorph (StableCuspAugmentedQuotient S h hS) ℂ :=
  (stableCuspAugmentedQuotientHomeomorph S hD hT h hS hK hSo hSc).toOpenPartialHomeomorph.trans
    (punctureFillChart (stableCuspFillData S h hS hK hSo hSc))

theorem stableCuspAugmentedNewChart_mem {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup) :
    stableCuspAugmentedNewChart S hD hT h hS hK hSo hSc ∈
      (stableCuspAugmentedQuotientRiemannSurface S hD hT h hS hK hSo hSc hfix).charts := by
  exact ⟨(stableCuspAugmentedQuotientHomeomorph S hD hT h hS hK hSo hSc).toOpenPartialHomeomorph,
    rfl, punctureFillChart (stableCuspFillData S h hS hK hSo hSc), Or.inr rfl, rfl⟩

theorem stableCuspAugmentedNewChart_target {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) :
    (stableCuspAugmentedNewChart S hD hT h hS hK hSo hSc).target = Metric.ball 0 (stableCuspRadius h) := by
  rw [stableCuspAugmentedNewChart, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, preimage_univ, inter_univ, punctureFillChart_target]
  rfl

theorem stableCuspAugmentedNewChart_cusp {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : MobiusInvariantDomain G}
    (S : MobiusStableSubset D) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) (g : G) :
    stableCuspAugmentedNewChart S hD hT h hS hK hSo hSc
      (Quotient.mk _ (stableCuspAugmentedCusp S h hS g (stableCuspCompletionInfinity h))) = 0 := by
  change punctureFillChart (stableCuspFillData S h hS hK hSo hSc)
    (stableCuspAugmentedQuotientHomeomorph S hD hT h hS hK hSo hSc _) = 0
  rw [stableCuspAugmentedQuotientHomeomorph_apply_mk, stableCuspAugmentedProjection_cusp S hD hT]
  have he := (punctureFillDiscMap_eq_infinity (stableCuspFillData S h hS hK hSo hSc)
    (stableCuspCompletionToDisc h (stableCuspCompletionInfinity h))).mpr rfl
  rw [he, punctureFillChart_infinity]

theorem stableCuspAugmentedNewChart_exponential {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) (z : stableCuspHalfPlane h) :
    stableCuspAugmentedNewChart S hD hT h hS hK hSo hSc
      (Quotient.mk _ (stableCuspAugmentedOld S h hS ⟨(z.val :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),
        S.subset_domain (by rw [hS]; exact ⟨z.val, z.property, rfl⟩)⟩)) =
      (complexPeriodExponential 1 z.val).val := by
  change punctureFillChart (stableCuspFillData S h hS hK hSo hSc)
    (stableCuspAugmentedQuotientHomeomorph S hD hT h hS hK hSo hSc _) = _
  rw [stableCuspAugmentedQuotientHomeomorph_apply_mk, stableCuspAugmentedProjection_old]
  have he := stableCuspFilledDiscMap_finite S h hS hK hSo hSc z
  rw [← he]
  exact punctureFillChart_apply_discMap (stableCuspFillData S h hS hK hSo hSc)
    (stableCuspFiniteToFilledDisc h z)

theorem stableCuspAugmentedNewChart_cusp_source {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G)
    (h : ℝ) (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hSo : IsOpen S.carrier) (hSc : IsConnected S.carrier) (g : G) :
    Quotient.mk _ (stableCuspAugmentedCusp S h hS g (stableCuspCompletionInfinity h)) ∈
      (stableCuspAugmentedNewChart S hD hT h hS hK hSo hSc).source := by
  change _ ∈ (stableCuspAugmentedQuotientHomeomorph S hD hT h hS hK hSo hSc).toOpenPartialHomeomorph.source ∧ _
  constructor
  · exact Set.mem_univ _
  · change stableCuspAugmentedQuotientHomeomorph S hD hT h hS hK hSo hSc _ ∈
      (punctureFillChart (stableCuspFillData S h hS hK hSo hSc)).source
    rw [stableCuspAugmentedQuotientHomeomorph_apply_mk, stableCuspAugmentedProjection_cusp S hD hT,
      punctureFillChart_source]
    exact ⟨stableCuspCompletionToDisc h (stableCuspCompletionInfinity h), rfl⟩

/--
In arbitrary actual full-group context, after the genuine geometric
normalization. Openness, connectedness and group membership are derived, rather than
added to its source hypotheses. The necessary cusp-stabilizer correction is explicit.
-/
theorem normalized_cusp_conformal_filling_exists {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : MobiusInvariantDomain G} (S : MobiusStableSubset D)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G D.carrier) (h : ℝ)
    (hS : S.carrier = stableCuspSphere h) (hK : S.stabilizer = stableTranslationGroup)
    (hfix : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ S.stabilizer) :
    ∃ hSo : IsOpen S.carrier, ∃ hSc : IsConnected S.carrier, ∃ hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G,
    ∃ hfixT : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup,
    let R := stableCuspAugmentedQuotientRiemannSurface S hD hT h hS hK hSo hSc hfixT
    let J := stableCuspAugmentedQuotientOld S hD hT h hS hK hSo hSc
    let e := stableCuspAugmentedNewChart S hD hT h hS hK hSo hSc
    RiemannAnalyticMap (mobiusQuotientRiemannSurface D hD).toRiemannAtlas R.toRiemannAtlas J ∧
      Topology.IsOpenEmbedding J ∧ e ∈ R.charts ∧ e.target = Metric.ball 0 (stableCuspRadius h) ∧
      ∀ g : G,
        (Quotient.mk _ (stableCuspAugmentedCusp S h hS g (stableCuspCompletionInfinity h)) ∈ e.source ∧
          e (Quotient.mk _ (stableCuspAugmentedCusp S h hS g (stableCuspCompletionInfinity h))) = 0) ∧
        (¬∃ K : Set (StableCuspAugmentedDomain S h hS), IsCompact K ∧
          K ∈ 𝓝 (stableCuspAugmentedCusp S h hS g (stableCuspCompletionInfinity h))) ∧
        ∀ U : Set (StableCuspAugmentedDomain S h hS),
          U ∈ 𝓝 (stableCuspAugmentedCusp S h hS g (stableCuspCompletionInfinity h)) ↔
            ∃ t : ℝ, h < t ∧ stableCuspAugmentedHeightTail S h hS g t ⊆ U := by
  have hSo : IsOpen S.carrier := by rw [hS]; exact stableCuspSphere_isOpen h
  have hSc : IsConnected S.carrier := by rw [hS]; exact stableCuspSphere_isConnected h
  have hTg : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ stableTranslationGroup :=
    (stableTranslationGroup_mem _).mpr ⟨1, by norm_num⟩
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ G := S.stabilizer_le (hK.symm ▸
    hTg)
  have hfixT : ∀ f ∈ G, f.val ∞ = ∞ → f ∈ stableTranslationGroup :=
    fun f hf hfi => hK ▸ hfix f hf hfi
  refine ⟨hSo, hSc, hT, hfixT,
    stableCuspAugmentedQuotientOld_analytic S hD hT h hS hK hSo hSc hfixT,
    stableCuspAugmentedQuotientOld_isOpenEmbedding S hD hT h hS hK hSo hSc,
    stableCuspAugmentedNewChart_mem S hD hT h hS hK hSo hSc hfixT,
    stableCuspAugmentedNewChart_target S hD hT h hS hK hSo hSc, ?_⟩
  intro g
  exact ⟨⟨stableCuspAugmentedNewChart_cusp_source S hD hT h hS hK hSo hSc g,
    stableCuspAugmentedNewChart_cusp S hD hT h hS hK hSo hSc g⟩,
    stableCuspAugmented_no_compact_nhds S hD hT h hS hK hfixT g,
    stableCuspAugmented_mem_nhds_iff S hD hT h hS hK hfixT g⟩

end LowDimensionalTopology.Geometry.Surfaces
