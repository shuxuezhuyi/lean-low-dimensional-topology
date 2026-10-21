module
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.PlaneSeparation
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.AngularMeasure
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSidePairing
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonCycles
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Tactic

/-!
# Actual angular measure and the original polygon cycle angle sum
-/

@[expose] public section
noncomputable section
open Set Topology MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Pointwise OnePoint Complex.UnitDisc ENNReal ComplexConjugate Classical
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

abbrev polygonDirectionPositiveCompact := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionPositiveCompact

abbrev polygonDirectionMeasure := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure

instance polygonDirectionMeasure_isHaar : IsHaarMeasure polygonDirectionMeasure := _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure_isHaar

abbrev polygonDirectionMeasure_univ := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure_univ

instance polygonDirectionMeasure_isProbability : IsProbabilityMeasure polygonDirectionMeasure := _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure_isProbability

instance polygonDirectionMeasure_nullSingleton : NullSingletonClass polygonDirectionMeasure := _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure_nullSingleton

abbrev discRadialPoint := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint

abbrev continuous_discRadialPoint := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_discRadialPoint

abbrev discRadialDirections := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections

abbrev discOriginNormalizer := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer

abbrev discOriginNormalizer_apply_self := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self

abbrev discOriginNormalizer_isometry := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry

abbrev discRadialPoint_norm := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint_norm

abbrev kleinCoordinate_discRadialPoint := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_discRadialPoint

abbrev discRadialPoint_mem_of_le := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialPoint_mem_of_le

abbrev discRadialTestRadius := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialTestRadius

abbrev exists_discRadialTestRadius_le := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_discRadialTestRadius_le

abbrev discRadialDirections_eq_iUnion := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_eq_iUnion

abbrev measurableSet_discRadialDirections := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.measurableSet_discRadialDirections

abbrev finite_circle_orthogonal := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.finite_circle_orthogonal

abbrev discRadialDirections_mono := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_mono

abbrev discRadialDirections_inter := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_inter

abbrev finite_discRadialDirections_of_line := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.finite_discRadialDirections_of_line

abbrev polygonDirectionMeasure_line_zero := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure_line_zero

abbrev tendsto_discRadialTestPoint := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.tendsto_discRadialTestPoint

abbrev discRadialDirections_incident_cover := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_incident_cover

/-- Compatibility alias for the shared genuine planar separation theorem. -/
abbrev finite_discRadialDirections_common_closures := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.finite_discRadialDirections_common_closures

/-- The actual original-disc coordinate with the original basepoint moved to the origin. -/
def polygonPointCoordinate
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (x : P.domain.carrier) : P.domain.carrier ≃ₜ Complex.UnitDisc :=
  P.finiteCoordinate.trans (discOriginNormalizer (P.finiteCoordinate x))

theorem polygonPointCoordinate_self {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) : polygonPointCoordinate P x x = 0 :=
  discOriginNormalizer_apply_self _

/-- The genuine local directions of an original closed polygon copy at the specified point. -/
def fuchsianTileDirections
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (x : P.domain.carrier) (g : H) : Set Circle :=
  discRadialDirections (polygonPointCoordinate P x '' fuchsianDomainTile P D g)

theorem IsConvexFuchsianPolygon.pointCoordinate_smul_convex
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) (g : H) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (polygonPointCoordinate P x '' (g • D)) := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex ((fun z => discOriginNormalizer (P.finiteCoordinate x) (P.finiteCoordinate z)) '' (g • D))
  rw [← image_image]
  exact (hD.smul_convex g).isometry_image (discOriginNormalizer_isometry _)

theorem polygonPointCoordinate_image_tile
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (x : P.domain.carrier) (g : H) :
    polygonPointCoordinate P x '' fuchsianDomainTile P D g =
      closure (polygonPointCoordinate P x '' (g • D)) := by
  change polygonPointCoordinate P x '' (g • closure D) = _
  have he : g • closure D = closure (g • D) := (Homeomorph.smul g).image_closure D
  rw [he, (polygonPointCoordinate P x).image_closure]

theorem polygonPointCoordinate_zero_mem_tile
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (x : P.domain.carrier) (g : H) :
    (0 : Complex.UnitDisc) ∈ polygonPointCoordinate P x '' fuchsianDomainTile P D g ↔
      x ∈ fuchsianDomainTile P D g := by
  rw [← polygonPointCoordinate_self P x, (polygonPointCoordinate P x).injective.mem_set_image]

theorem IsConvexFuchsianPolygon.tileDirections_measurable
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) {g : H} (hg : x ∈ fuchsianDomainTile P D g) :
    MeasurableSet (fuchsianTileDirections P D x g) := by
  unfold fuchsianTileDirections
  rw [polygonPointCoordinate_image_tile]
  apply measurableSet_discRadialDirections (hD.pointCoordinate_smul_convex x g).closure isClosed_closure
  rw [← polygonPointCoordinate_image_tile, polygonPointCoordinate_zero_mem_tile]
  exact hg

theorem IsConvexFuchsianPolygon.tileDirections_pairwise_null
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) {g h : H} (hg : x ∈ fuchsianDomainTile P D g)
    (hh : x ∈ fuchsianDomainTile P D h) (hgh : g ≠ h) :
    polygonDirectionMeasure (fuchsianTileDirections P D x g ∩ fuchsianTileDirections P D x h) = 0 := by
  have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hDn := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hdis : Disjoint (g • D) (h • D) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨u, hu, hgu⟩ ⟨v, hv, hhv⟩
    change g • u = y at hgu
    change h • v = y at hhv
    have he : u = (g⁻¹ * h) • v := by rw [mul_smul, hhv, ← hgu, inv_smul_smul]
    have hne : g⁻¹ * h ≠ 1 := by intro he; exact hgh (inv_mul_eq_one.mp he)
    exact Set.disjoint_left.mp (hD.locallyFinite.fundamental.disjoint_image hne) ⟨v, hv, he.symm⟩ hu
  unfold fuchsianTileDirections
  rw [polygonPointCoordinate_image_tile, polygonPointCoordinate_image_tile]
  apply (finite_discRadialDirections_common_closures
    (hD.pointCoordinate_smul_convex x g)
    ((polygonPointCoordinate P x).isOpenMap _ ((Homeomorph.smul g).isOpenMap D hDo))
    ((hDn.image (fun y => g • y)).image (polygonPointCoordinate P x))
    (hD.pointCoordinate_smul_convex x h)
    ((polygonPointCoordinate P x).isOpenMap _ ((Homeomorph.smul h).isOpenMap D hDo))
    ((hDn.image (fun y => h • y)).image (polygonPointCoordinate P x))
    (hdis.image (polygonPointCoordinate P x).injective.injOn (subset_univ _) (subset_univ _))
    ?_ ?_).measure_zero _
  · rw [← polygonPointCoordinate_image_tile, polygonPointCoordinate_zero_mem_tile]; exact hg
  · rw [← polygonPointCoordinate_image_tile, polygonPointCoordinate_zero_mem_tile]; exact hh

/-- The genuine finite neighborhood star covers the whole angular circle at the original point. -/
theorem IsLocallyFiniteFuchsianDomain.tileDirections_cover
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsLocallyFiniteFuchsianDomain P D)
    (x : P.domain.carrier) :
    (⋃ g ∈ {g : H | x ∈ fuchsianDomainTile P D g}, fuchsianTileDirections P D x g) = univ := by
  let F := polygonPointCoordinate P x
  have he : (fun g : H => F '' fuchsianDomainTile P D g) =
      (fun g : H => F.symm ⁻¹' fuchsianDomainTile P D g) := by
    funext g
    exact F.toEquiv.image_eq_preimage_symm _
  have hl : LocallyFinite (fun g : H => F '' fuchsianDomainTile P D g) := by
    rw [he]
    exact hD.locallyFinite.preimage_continuous F.symm.continuous
  have hc : ∀ g : H, IsClosed (F '' fuchsianDomainTile P D g) :=
    fun g => F.isClosedMap _ (fuchsianDomainTile_closed P D g)
  have hcov : (⋃ g : H, F '' fuchsianDomainTile P D g) = univ := by
    have hf : (⋃ g : H, fuchsianDomainTile P D g) = univ := hD.fundamental.closure_cover
    rw [← image_iUnion, hf, image_univ, F.surjective.range_eq]
  have hd := discRadialDirections_incident_cover (fun g : H => F '' fuchsianDomainTile P D g) hl hc hcov
  simpa only [F, polygonPointCoordinate_zero_mem_tile, fuchsianTileDirections] using hd

/-- The actual closed polygon copies partition the full angular measure at every original point. -/
theorem IsConvexFuchsianPolygon.tileDirections_measure_sum
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) :
    ∑ g ∈ (hD.locallyFinite.incident_finite x).toFinset,
      polygonDirectionMeasure (fuchsianTileDirections P D x g) = 1 := by
  have hm := measure_biUnion_finset₀ (μ := polygonDirectionMeasure)
    (s := (hD.locallyFinite.incident_finite x).toFinset)
    (f := fuchsianTileDirections P D x)
    (fun g hg h hh hgh => hD.tileDirections_pairwise_null x
      (by simpa using hg) (by simpa using hh) hgh)
    (fun g hg => (hD.tileDirections_measurable x (by simpa using hg)).nullMeasurableSet)
  have hu : (⋃ g ∈ (hD.locallyFinite.incident_finite x).toFinset,
      fuchsianTileDirections P D x g) = univ := by
    simpa only [Set.Finite.mem_toFinset] using hD.locallyFinite.tileDirections_cover x
  rw [hu, polygonDirectionMeasure_univ] at hm
  exact hm.symm

abbrev disc_zero_isometry_formula := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_zero_isometry_formula

abbrev discRadialDirections_image_of_commute := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_image_of_commute

abbrev polygonDirectionMeasure_image_homeomorph := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure_image_homeomorph

abbrev polygonDirectionMeasure_radial_isometry := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure_radial_isometry

abbrev discOriginNormalizer_symm_isometry := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_symm_isometry

abbrev discSubtendedAngularFraction := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction

abbrev discSubtendedAngle := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle

abbrev discSubtendedAngularFraction_isometry := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction_isometry

abbrev discSubtendedAngle_isometry := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_isometry

/-- The original side-copy multiplicity above one actual cycle point is exactly the point stabilizer. -/
def fuchsianIncidentFiberEquivStabilizer {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (x y : P.domain.carrier)
    (hy : y ∈ fuchsianPolygonCycle P D x) :
    {g : H // x ∈ fuchsianDomainTile P D g ∧ g⁻¹ • x = y} ≃ MulAction.stabilizer H x := by
  let k := (MulAction.mem_orbit_iff.mp hy.2).choose
  have hk : k • x = y := (MulAction.mem_orbit_iff.mp hy.2).choose_spec
  refine {
    toFun := fun g => ⟨g.val * k, MulAction.mem_stabilizer_iff.mpr ?_⟩
    invFun := fun s => ⟨s.val * k⁻¹, ?_, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [mul_smul, hk]
    exact (congrArg (fun q => g.val • q) g.property.2.symm).trans (smul_inv_smul g.val x)
  · refine ⟨y, hy.1, ?_⟩
    change (s.val * k⁻¹) • y = x
    rw [mul_smul, ← hk, inv_smul_smul]
    exact MulAction.mem_stabilizer_iff.mp s.property
  · rw [mul_inv_rev, inv_inv, mul_smul]
    have hs : s.val⁻¹ • x = x := MulAction.mem_stabilizer_iff.mp s⁻¹.property
    rw [hs, hk]
  · intro g
    apply Subtype.ext
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  · intro s
    apply Subtype.ext
    simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- The actual closed original polygon's angular fraction at an original point. -/
def fuchsianPolygonAngularFraction
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (x : P.domain.carrier) : ℝ≥0∞ :=
  discSubtendedAngularFraction (P.finiteCoordinate '' closure D) (P.finiteCoordinate x)

/-- The actual original polygon angle in radians, without prescribed angle data. -/
def fuchsianPolygonAngle
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (x : P.domain.carrier) : ℝ :=
  2 * Real.pi * (fuchsianPolygonAngularFraction P D x).toReal

theorem fuchsianTileDirections_measure_eq
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (x : P.domain.carrier) (g : H) :
    polygonDirectionMeasure (fuchsianTileDirections P D x g) =
      fuchsianPolygonAngularFraction P D (g⁻¹ • x) := by
  have hm := discSubtendedAngularFraction_isometry (P.discAction g) (P.discAction_isometry g)
    (P.finiteCoordinate '' closure D) (P.finiteCoordinate (g⁻¹ • x))
  have hx : P.discAction g (P.finiteCoordinate (g⁻¹ • x)) = P.finiteCoordinate x := by
    change P.finiteCoordinate (g • P.finiteCoordinate.symm (P.finiteCoordinate (g⁻¹ • x))) = _
    rw [P.finiteCoordinate.symm_apply_apply, smul_inv_smul]
  rw [hx, ← P.discAction_image] at hm
  unfold fuchsianTileDirections
  have he : polygonPointCoordinate P x '' fuchsianDomainTile P D g =
      discOriginNormalizer (P.finiteCoordinate x) '' (P.finiteCoordinate '' (g • closure D)) := by
    rw [image_image]
    rfl
  rw [he]
  exact hm

theorem IsLocallyFiniteFuchsianDomain.incident_fiber_card
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsLocallyFiniteFuchsianDomain P D)
    (x y : P.domain.carrier) (hy : y ∈ fuchsianPolygonCycle P D x) :
    ((hD.incident_finite x).toFinset.filter (fun g : H => g⁻¹ • x = y)).card = fuchsianPointOrder P x := by
  classical
  let t := (hD.incident_finite x).toFinset.filter (fun g : H => g⁻¹ • x = y)
  let e : t ≃ {g : H // x ∈ fuchsianDomainTile P D g ∧ g⁻¹ • x = y} :=
    Equiv.subtypeEquivProp (by ext g; simp [t])
  have hc := Nat.card_congr (e.trans (fuchsianIncidentFiberEquivStabilizer P D x y hy))
  simpa only [t, fuchsianPointOrder, Nat.card_eq_fintype_card, Fintype.card_coe] using hc

/-- The actual incidence sum counts each original cycle point exactly its stabilizer order times. -/
theorem IsLocallyFiniteFuchsianDomain.incident_weight_sum
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsLocallyFiniteFuchsianDomain P D)
    (x : P.domain.carrier) (w : P.domain.carrier → ℝ≥0∞) :
    ∑ g ∈ (hD.incident_finite x).toFinset, w (g⁻¹ • x) =
      (fuchsianPointOrder P x : ℝ≥0∞) * ∑ y ∈ (hD.cycle_finite x).toFinset, w y := by
  classical
  have hf (g : H) (hg : g ∈ (hD.incident_finite x).toFinset) :
      g⁻¹ • x ∈ (hD.cycle_finite x).toFinset := by
    simp only [Set.Finite.mem_toFinset] at hg ⊢
    change g⁻¹ • x ∈ closure D ∧ g⁻¹ • x ∈ MulAction.orbit H x
    constructor
    · obtain ⟨y, hy, he⟩ := hg
      change g • y = x at he
      simpa only [← he, inv_smul_smul] using hy
    · exact MulAction.mem_orbit_iff.mpr ⟨g⁻¹, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hf]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  calc
    (∑ g ∈ (hD.incident_finite x).toFinset with g⁻¹ • x = y, w (g⁻¹ • x)) =
        ∑ _g ∈ (hD.incident_finite x).toFinset with _g⁻¹ • x = y, w y := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [(Finset.mem_filter.mp hg).2]
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hD.incident_fiber_card x y (by simpa using hy)]

/-- The original cycle's actual angular fractions add to the reciprocal of its stabilizer order. -/
theorem IsConvexFuchsianPolygon.cycleAngularFraction_sum
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) :
    (fuchsianPointOrder P x : ℝ≥0∞) *
      ∑ y ∈ (hD.locallyFinite.cycle_finite x).toFinset, fuchsianPolygonAngularFraction P D y = 1 := by
  rw [← hD.locallyFinite.incident_weight_sum x]
  convert hD.tileDirections_measure_sum x using 1
  apply Finset.sum_congr rfl
  intro g _hg
  exact (fuchsianTileDirections_measure_eq P D x g).symm

theorem fuchsianPolygonAngularFraction_ne_top
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (x : P.domain.carrier) :
    fuchsianPolygonAngularFraction P D x ≠ (⊤ : ℝ≥0∞) := measure_ne_top _ _

/-- In literal finite-cycle form, with actual native polygon angles in radians. -/
theorem sum_cycle_angles_eq_two_pi_div_pointOrder
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) :
    ∑ y ∈ (hD.locallyFinite.cycle_finite x).toFinset, fuchsianPolygonAngle P D y =
      2 * Real.pi / fuchsianPointOrder P x := by
  have hm := congrArg ENNReal.toReal (hD.cycleAngularFraction_sum x)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one,
    ENNReal.toReal_sum (fun y _hy => fuchsianPolygonAngularFraction_ne_top P D y)] at hm
  have hn : (fuchsianPointOrder P x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (P.pointOrder_pos x).ne'
  simp only [fuchsianPolygonAngle, ← Finset.mul_sum]
  apply (eq_div_iff hn).mpr
  calc
    (2 * Real.pi * ∑ y ∈ (hD.locallyFinite.cycle_finite x).toFinset,
        (fuchsianPolygonAngularFraction P D y).toReal) * (fuchsianPointOrder P x : ℝ) =
      2 * Real.pi * ((fuchsianPointOrder P x : ℝ) * ∑ y ∈ (hD.locallyFinite.cycle_finite x).toFinset,
        (fuchsianPolygonAngularFraction P D y).toReal) := by ring
    _ = 2 * Real.pi := by rw [hm, mul_one]

abbrev discRadialDirections_of_mem_nhds := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_of_mem_nhds

abbrev discSubtendedAngularFraction_of_interior := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction_of_interior

abbrev discSubtendedAngle_of_interior := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_of_interior

abbrev discRadialDirections_inter_nhds := @_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_inter_nhds

/-- The literal sum of actual interior angles over the original finite cycle. -/
def fuchsianPolygonCycleAngle
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D C : Set P.domain.carrier) (hC : C.Finite) : ℝ :=
  ∑ y ∈ hC.toFinset, fuchsianPolygonAngle P D y

/-- For the genuine finite-cycle angle, retaining the original polygon and action. -/
theorem cycleAngle_eq_two_pi_div_pointOrder
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) :
    fuchsianPolygonCycleAngle P D (fuchsianPolygonCycle P D x) (hD.locallyFinite.cycle_finite x) =
      2 * Real.pi / fuchsianPointOrder P x := sum_cycle_angles_eq_two_pi_div_pointOrder hD x

end LowDimensionalTopology.Geometry.Fuchsian
