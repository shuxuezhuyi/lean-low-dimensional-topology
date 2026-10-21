/- Actual canonical Nielsen-distance maximum principle, 2026-10-20. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.IdealHull.NielsenHalfPlaneDistance
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.QuotientSignature
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.NativeHalfPlaneComponents
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane OnePoint MatrixGroups Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Genuine native isometries transport the distance-to-set local maximum
condition, with the actual whole image of the same set. -/
theorem nielsen_infDist_not_isLocalMax_of_isometry_image
    (e : ℍ ≃ᵢ ℍ) (C : Set ℍ) (x : ℍ)
    (h : ¬ IsLocalMax (fun z : ℍ => Metric.infDist z (e '' C)) (e x)) :
    ¬ IsLocalMax (fun z : ℍ => Metric.infDist z C) x := by
  intro hm
  have hm' : IsLocalMax (fun z : ℍ => Metric.infDist (e.symm z) C) (e x) := by
    have ht : IsLocalMax (fun z : ℍ => Metric.infDist z C) (e.symm (e x)) := by
      simpa only [e.symm_apply_apply] using hm
    exact ht.comp_continuous e.symm.continuous.continuousAt
  have heq : (fun z : ℍ => Metric.infDist (e.symm z) C) =
      (fun z : ℍ => Metric.infDist z (e '' C)) := by
    funext z
    simpa only [e.apply_symm_apply] using (Metric.infDist_image e.isometry (x := e.symm z) (t := C)).symm
  exact h (heq ▸ hm')

/-- The actual positive half-turn preserves the complete native imaginary axis. -/
theorem nielsen_axisSwap_native_axis :
    Hyperbolic.hSLIsometry (Hyperbolic.axisHalfTurnSL 1 (by norm_num)) '' (Hyperbolic.HalfPlaneLine.vertical 0).carrier =
      (Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
  apply Mobius.halfPlaneBoundaryPoint_injective.image_injective
  calc
    Mobius.halfPlaneBoundaryPoint '' (Hyperbolic.hSLIsometry (Hyperbolic.axisHalfTurnSL 1 (by norm_num)) ''
        (Hyperbolic.HalfPlaneLine.vertical 0).carrier) =
        (Hyperbolic.realSLMobius (Hyperbolic.axisHalfTurnSL 1 (by norm_num))).val ''
          (Mobius.halfPlaneBoundaryPoint '' (Hyperbolic.HalfPlaneLine.vertical 0).carrier) := by
      rw [image_image, image_image]
      apply image_congr
      intro z _hz
      exact (Hyperbolic.realSLMobius_action _ z).symm
    _ = Mobius.halfPlaneBoundaryPoint '' (Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
      change (Hyperbolic.realSLMobius (Hyperbolic.axisHalfTurnSL 1 (by norm_num))).val ''
        (Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.HalfPlaneLine.vertical 0).carrier) =
        Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.HalfPlaneLine.vertical 0).carrier
      rw [nielsenImaginaryAxis_native_image, nielsenAxisSwap_axis]

/-- Every genuine line has an actual native SL frame with a specified point
strictly on the retained left side. No desired support or side is assumed. -/
theorem nielsen_line_left_normalizer
    (L : Hyperbolic.HalfPlaneLine)
    (w : ℍ)
    (hw : w ∉ L.carrier) :
    ∃ e : ℍ ≃ᵢ ℍ, e '' L.carrier = (Hyperbolic.HalfPlaneLine.vertical 0).carrier ∧ (e w).re < 0 := by
  obtain ⟨q, hq⟩ := L.exists_SL_normalizer
  let e := Hyperbolic.hSLIsometry q
  have hline : e '' L.carrier = (Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
    rw [← hq, Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  have hne : (e w).re ≠ 0 := by
    intro he
    apply hw
    have hh : e w ∈ e '' L.carrier := hline.symm ▸ he
    exact e.injective.mem_set_image.mp hh
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact ⟨e, hline, hneg⟩
  · let a := Hyperbolic.hSLIsometry (Hyperbolic.axisHalfTurnSL 1 (by norm_num))
    refine ⟨e.trans a, ?_, ?_⟩
    · change (fun z : ℍ => a (e z)) '' L.carrier = _
      rw [← image_image, hline]
      exact nielsen_axisSwap_native_axis
    · change (Hyperbolic.axisHalfTurnSL 1 (by norm_num) • e w : ℍ).re < 0
      rw [nielsenAxisSwap_re]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos hpos) (Complex.normSq_pos.mpr (e w).ne_zero)

/-- The actual maximal-gap arc intersection has no distance local maximum
outside its closed core. Every gap line is genuinely part of that core's
frontier, rather than a supplied nearest-point assumption. -/
theorem nielsenRealArcRegion_infDist_not_isLocalMax (A : Set ℝ)
    (ho : IsOpen (Hyperbolic.nielsenRealArcRegion A))
    (hn : (Hyperbolic.nielsenRealArcRegion A).Nonempty)
    (x : ℍ) (hx : x ∉ closure (Hyperbolic.nielsenRealArcRegion A)) :
    ¬ IsLocalMax (fun z : ℍ => Metric.infDist z (closure (Hyperbolic.nielsenRealArcRegion A))) x := by
  let C := closure (Hyperbolic.nielsenRealArcRegion A)
  have hxN : x ∉ Hyperbolic.nielsenRealArcRegion A := fun h => hx (subset_closure h)
  change ¬ ∀ G : Hyperbolic.NielsenHalfPlaneGap, G.carrier ∈ Auxiliary.Topology.nielsenRealGapFamily A → x ∈ G.keptSide at hxN
  push Not at hxN
  obtain ⟨G, hG, hxG⟩ := hxN
  obtain ⟨w, hw⟩ := hn
  have hwG : w ∈ G.keptSide := hw G hG
  have hwL : w ∉ G.line.carrier := fun h => disjoint_left.mp G.keptSide_disjoint_line hwG h
  obtain ⟨e, hline, hwleft⟩ := nielsen_line_left_normalizer G.line w hwL
  have hside : e '' G.keptSide = {z : ℍ | z.re < 0} := by
    rw [G.keptSide_eq_openHalfPlane w hwG, Hyperbolic.native_image_open_halfPlane e G.line
      (Hyperbolic.HalfPlaneLine.vertical 0) hline w hwL, Hyperbolic.hReCutLt_eq_openHalfPlane 0 (e w) hwleft]
    rfl
  have hCleft : e '' C ⊆ {z : ℍ | z.re ≤ 0} := by
    have hsub : Hyperbolic.nielsenRealArcRegion A ⊆ {z : ℍ | (e z).re ≤ 0} := by
      intro z hz
      have hh : e z ∈ e '' G.keptSide := mem_image_of_mem e (hz G hG)
      rw [hside] at hh
      exact (show (e z).re < 0 from hh).le
    have hc : C ⊆ {z : ℍ | (e z).re ≤ 0} := closure_minimal hsub
      (isClosed_le (UpperHalfPlane.continuous_re.comp e.continuous) continuous_const)
    rintro _ ⟨z, hz, rfl⟩
    exact hc hz
  have haxis : (Hyperbolic.HalfPlaneLine.vertical 0).carrier ⊆ e '' C := by
    rw [← hline]
    exact image_mono ((nielsenGap_line_subset_frontier A ho ⟨w, hw⟩ G hG).trans frontier_subset_closure)
  have hxleft : ¬ (e x).re < 0 := by
    intro hh
    have hm : e x ∈ e '' G.keptSide := hside.symm ▸ hh
    exact hxG (e.injective.mem_set_image.mp hm)
  have hxne : (e x).re ≠ 0 := by
    intro he
    have hm : e x ∈ e '' C := haxis he
    exact hx (e.injective.mem_set_image.mp hm)
  have hxright : 0 < (e x).re := lt_of_le_of_ne (le_of_not_gt hxleft) (Ne.symm hxne)
  apply nielsen_infDist_not_isLocalMax_of_isometry_image e C x
  exact Hyperbolic.nielsen_infDist_not_isLocalMax_of_right (e '' C) haxis hCleft (e x) hxright

/-- The source-defined canonical Nielsen region in the original native
half-plane has no distance local maximum anywhere outside its closure. -/
theorem halfPlaneNielsen_infDist_not_isLocalMax
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (x : ℍ) (hx : x ∉ closure (Mobius.halfPlaneBoundaryPoint ⁻¹' P.asFuchsianDisc.nielsenRegion hNE)) :
    ¬ IsLocalMax (fun z : ℍ => Metric.infDist z
      (closure (Mobius.halfPlaneBoundaryPoint ⁻¹' P.asFuchsianDisc.nielsenRegion hNE))) x := by
  let D := P.asFuchsianDisc
  let q := D.nielsenArcNormalizer hNE
  have hq : q.val '' Hyperbolic.openHalfPlaneSet = Hyperbolic.openHalfPlaneSet := D.nielsenArcNormalizer_image hNE
  obtain ⟨B, hB⟩ := mobius_preserves_halfPlane_exists_SL q hq
  let e := Hyperbolic.hSLIsometry B
  let N := Mobius.halfPlaneBoundaryPoint ⁻¹' D.nielsenRegion hNE
  let Λ := DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate q H)
  let A := Hyperbolic.nielsenHalfPlaneRealSet Λ
  have hArc : Hyperbolic.nielsenHalfPlaneArcRegion Λ = Hyperbolic.nielsenRealArcRegion A :=
    Hyperbolic.nielsenHalfPlaneArcRegion_eq_realArcRegion Λ (D.nielsenArcNormalizer_limit hNE)
  have he (z : ℍ) : Mobius.halfPlaneBoundaryPoint (e z) = q.val (Mobius.halfPlaneBoundaryPoint z) := by
    rw [← hB]
    exact (Hyperbolic.realSLMobius_action B z).symm
  have hNform : D.nielsenRegion hNE = nielsenModelSet q (Hyperbolic.nielsenRealArcRegion A) := by
    change nielsenModelSet q (Hyperbolic.nielsenHalfPlaneArcRegion Λ) = _
    rw [hArc]
  have himage : e '' N = Hyperbolic.nielsenRealArcRegion A := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      apply (nielsen_modelSet_point_mem q (Hyperbolic.nielsenRealArcRegion A) (e w)).mp
      change q.val.symm (Mobius.halfPlaneBoundaryPoint (e w)) ∈ _
      rw [he, q.val.symm_apply_apply]
      exact hNform ▸ hw
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      change Mobius.halfPlaneBoundaryPoint (e.symm z) ∈ D.nielsenRegion hNE
      rw [hNform]
      have hh := (nielsen_modelSet_point_mem q (Hyperbolic.nielsenRealArcRegion A) z).mpr hz
      change q.val.symm (Mobius.halfPlaneBoundaryPoint z) ∈ _ at hh
      have hback : q.val.symm (Mobius.halfPlaneBoundaryPoint z) = Mobius.halfPlaneBoundaryPoint (e.symm z) := by
        apply q.val.injective
        rw [q.val.apply_symm_apply, ← he, e.apply_symm_apply]
      rwa [hback] at hh
  have hoN : IsOpen N := ((D.nielsenRegion_properties hNE).2.2.1).preimage
    Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.continuous
  have hnN : N.Nonempty := by
    obtain ⟨p, hp⟩ := (D.nielsenRegion_properties hNE).2.1
    have hpD : p ∈ Hyperbolic.openHalfPlaneSet := (D.nielsenRegion_properties hNE).1 hp
    obtain ⟨z, rfl⟩ := Hyperbolic.halfPlaneBoundaryPoint_range.symm ▸ hpD
    exact ⟨z, hp⟩
  have ho : IsOpen (Hyperbolic.nielsenRealArcRegion A) := himage ▸ e.toHomeomorph.isOpenMap N hoN
  have hn : (Hyperbolic.nielsenRealArcRegion A).Nonempty := himage ▸ hnN.image e
  have hclosed : e '' closure N = closure (Hyperbolic.nielsenRealArcRegion A) := by
    change e.toHomeomorph '' closure N = _
    rw [e.toHomeomorph.image_closure]
    exact congrArg closure himage
  have hx' : e x ∉ closure (Hyperbolic.nielsenRealArcRegion A) := by
    rw [← hclosed]
    exact fun hh => hx (e.injective.mem_set_image.mp hh)
  apply nielsen_infDist_not_isLocalMax_of_isometry_image e (closure N) x
  rw [hclosed]
  exact nielsenRealArcRegion_infDist_not_isLocalMax A ho hn (e x) hx'

end LowDimensionalTopology.Geometry.Fuchsian
