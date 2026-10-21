module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleDilationPrimitiveRoot
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.ParabolicSideNormalizers
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped OnePoint Pointwise UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance simpleAxisNormalizerSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance simpleAxisNormalizerSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- A genuine original hyperbolic element has a whole-model half-plane dilation normalizer, with a nonzero signed logarithmic multiplier. -/
theorem UnitDiscFuchsianGroup.hyperbolic_halfPlane_normalizer {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f) (hfG : f ∈ G) :
    ∃ q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      ∃ l : ℝ, l ≠ 0 ∧ q*f*q⁻¹ = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l := by
  let p := _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
  let f0 := p*f*p⁻¹
  have hpres : f0.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    rw [←cayleyInverse_unitDisc_image]
    change (p*f*p⁻¹).val '' (p.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) = p.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image,P.image_eq ⟨f,hfG⟩]
  have hf0 : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f0 := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward f p hf
  obtain ⟨A,hA⟩ := mobius_preserves_halfPlane_exists_SL f0 hpres
  have hAh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by rw [hA];exact hf0
  obtain ⟨s,k,hk,hk1,hn,_hact⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_normalizer A hAh.1.1
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hAh.1.1).mp hAh)
  let r := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius s
  have hr : r.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := realSLMobius_image_openHalfPlane s
  have hl : Real.log k ≠ 0 := by
    intro he
    have hke : k = 1 := by
      calc
        k = Real.exp (Real.log k) := (Real.exp_log hk).symm
        _ = 1 := by rw [he,Real.exp_zero]
    exact hk1 hke
  refine ⟨r*p,?_,Real.log k,hl,?_⟩
  · change (fun z => r.val (p.val z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _
    rw [←image_image,cayleyInverse_unitDisc_image,hr]
  · have he : (r*p)*f*(r*p)⁻¹ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (s*A*s⁻¹) := by
      rw [map_mul,map_mul,map_inv,hA]
      dsimp [f0,r]
      group
    rw [he,hn]
    change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling _ = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling _
    apply congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
    apply Units.ext
    simp only [Units.val_mk0,Real.exp_log hk]

/-- Every nontrivial signed real dilation has the same genuine three-dimensional geodesic axis. -/
theorem stableAxisDilation_geodesicAxis_of_ne_zero (l : ℝ) (hl : l ≠ 0) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusVerticalGeodesic := by
  let a : ℂˣ := Units.mk0 ((Real.exp l:ℝ):ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero l))
  have ha : (a:ℂ) ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    change Real.exp l = 1 at hre
    exact hl (Real.exp_injective (hre.trans Real.exp_zero.symm))
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a) = _
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxis_scaling_eq_standard a
    ha,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis_standard a ha]

/-- The source full-axis construction is insensitive to which direction the original simple element travels along its axis. -/
theorem HalfPlaneFuchsianGroup.simple_signed_dilation_intersection_polygon
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (l : ℝ) (hl : l ≠ 0) (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) :
    letI := P.nativeAction
    ∃ t : ℝ, 0 < t ∧ ∃ D : Set ℍ,
      (D = dilationAxisAnnulus t ∨ D = dihedralAxisRightAnnulus t) ∧
      IsConvexFuchsianPolygon P.cayleyData
        (P.cayleyCoordinate '' (D ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier)) := by
  let nativeSignedDilationPolygonAction := P.nativeAction
  rcases lt_or_gt_of_ne hl with hneg | hpos
  · have hmem : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation (-l) ∈ H := by
      rw [_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_neg]
      exact H.inv_mem hs.1
    have hsp : IsSimple H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation (-l)) := by
      refine ⟨hmem,_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_hyperbolic (-l) (neg_pos.mpr
        hneg),?_⟩
      intro g hg
      rw [stableAxisDilation_geodesicAxis (-l) (neg_pos.mpr hneg),
        ←stableAxisDilation_geodesicAxis_of_ne_zero l hl]
      exact hs.2.2 g hg
    exact P.simple_dilation_intersection_polygon (-l) (neg_pos.mpr hneg) hsp
  · exact P.simple_dilation_intersection_polygon l hpos hs

/-- The actual source intersection construction is transported back to every original invariant unit-disc model. -/
theorem UnitDiscFuchsianGroup.simple_hyperbolic_axis_intersection
    {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup G)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hs : IsSimple G f) :
    ∃ q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, ∃ hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet,
      let N := P.normalizedHalfPlaneData q hq
      letI := N.nativeAction
      ∃ hr : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*q).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc,
      ∃ t : ℝ, 0 < t ∧ ∃ E : Set ℍ,
        (E = dilationAxisAnnulus t ∨ E = dihedralAxisRightAnnulus t) ∧
        ∃ D : Set P.domain.carrier, IsConvexFuchsianPolygon P D ∧
          P.conjugateCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*q) hr '' D =
            N.cayleyCoordinate '' (E ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion
              (G := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier) := by
  obtain ⟨q,hq,l,hl,he⟩ := P.hyperbolic_halfPlane_normalizer f hs.2.1 hs.1
  let N := P.normalizedHalfPlaneData q hq
  have hsN : IsSimple (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G) (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) := by
    rw [←he]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_conjugation G f q).mpr hs
  let nativeOriginalSimpleAxisAction := N.nativeAction
  obtain ⟨t,ht,E,hcases,hpoly⟩ := N.simple_signed_dilation_intersection_polygon l hl hsN
  let r := _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*q
  have hr : r.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    change (fun z => _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val
      z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _
    rw [←image_image,hq,cayleyMobius_image_openHalfPlane]
  let F : P.domain.carrier ≃ₜ N.cayleyData.domain.carrier := P.conjugateCoordinate r hr
  let e : G ≃* _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G) :=
    MulEquiv.trans (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
      G)
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G))
  have hEquiv (g : G) (x : P.domain.carrier) : F (g • x) = e g • F x := by
    apply Subtype.ext
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val (g.val.val x.val)) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val (g.val.val (q.val.symm
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val x.val))))))
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm_apply_apply,q.val.symm_apply_apply]
  have harea : Measure.map F P.area = N.cayleyData.area := P.conjugateCoordinate_area_map r hr
  have hiso : letI := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
      Isometry (fun z : Complex.UnitDisc => N.cayleyData.finiteCoordinate (F (P.finiteCoordinate.symm z))) :=
    P.conjugateCoordinate_isometry r hr
  have hpD : IsConvexFuchsianPolygon P
      (F ⁻¹' (N.cayleyCoordinate '' (E ∩ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion
        (G := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
          G) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier))) :=
    equivariant_fuchsian_polygon_preimage P N.cayleyData e F hEquiv harea hiso hpoly
  refine ⟨q,hq,hr,t,ht,E,hcases,_,hpD,?_⟩
  exact F.surjective.image_preimage _

end LowDimensionalTopology.Geometry.Fuchsian
