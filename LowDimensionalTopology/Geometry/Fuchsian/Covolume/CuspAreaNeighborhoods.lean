/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeometricFuchsianCharts
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspNormalizationGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.ParabolicAreaInfinity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Topology
open scoped OnePoint UpperHalfPlane Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance completionAreaCoordinateSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance completionAreaCoordinateSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

theorem geometricModelArea_unitDisc_eq {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (S : Set P.domain.carrier) (hS : MeasurableSet S) :
    geometricModelArea P.asFuchsianDisc S=P.area S := by
  have h1 : (1:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup).val '' P.asFuchsianDisc.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    change id '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
    rw [image_id]
  have he : geometricDiscChart P.asFuchsianDisc 1 h1=P.finiteCoordinate := by
    ext x
    apply OnePoint.coe_injective
    rw [geometricDiscChart_extended]
    change x.val=(((P.finiteCoordinate
      x:Complex.UnitDisc):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    exact ((_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe (P.finiteCoordinate
      x)).symm.trans
      (congrArg Subtype.val (P.finiteCoordinate.symm_apply_apply x))).symm
  rw [geometricModelArea_eq_discChart P.asFuchsianDisc 1 h1 S hS,he,P.area_apply S hS]
  rfl


theorem cuspCompletion_old_deep_subset_finiteTail {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .parabolic) :
    fuchsianCuspCompletionOld D ⁻¹'
      _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspDeepNeighborhood (fuchsianCuspChartNormalization
        D) c ⊆
      _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain ''
        {z : D.domain.carrier | z.val∈(fuchsianCuspChartNormalization D c).finiteTail
          ((fuchsianCuspChartNormalization D c).height+1)} := by
  intro x hx
  induction x using Quotient.inductionOn with
  | h z=>
    obtain ⟨a,⟨b,hb,rfl⟩,he⟩:=hx
    obtain ⟨g,hg⟩:=Quotient.exact he
    have hv : g.val.val z.val=b.val:=
      congrArg (_root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspAugmentedSphere
        (fuchsianCuspChartNormalization D)) hg
    rcases (fuchsianCuspChartNormalization D c).heightTail_one_cases _ b hb with hb|hb
    · have hm : (fuchsianParabolicPointRepresentative D c).val∈D.carrier:=
        hb ▸ hv ▸ D.invariant g z.val z.property
      exact False.elim ((fuchsianCuspChartNormalization D c).orbit_cusp_not_mem D.discontinuous 1
        (by change (fuchsianParabolicPointRepresentative D c).val∈D.carrier;exact hm))
    · refine ⟨g•z,?_,?_⟩
      · change g.val.val z.val∈(fuchsianCuspChartNormalization D c).finiteTail
          ((fuchsianCuspChartNormalization D c).height+1)
        rwa [hv]
      · exact Quotient.sound ⟨g,rfl⟩


theorem cusp_finiteTail_orbit_width_one {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) {S : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D.domain} {p :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S p) (t : ℝ) (x : D.domain.carrier)
    (hx : x.val∈C.finiteTail t) :
    ∃y : D.domain.carrier,_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain y=_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain x ∧
      ∃w : ℂ,0≤w.re∧w.re<1∧t<w.im∧C.normalizer.val y.val=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  obtain ⟨w,hw,hwx⟩:=hx
  let n:ℤ:=Int.floor w.re
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(n:ℂ))∈_root_.LowDimensionalTopology.Geometry.Surfaces.stableTranslationGroup :=
    (_root_.LowDimensionalTopology.Geometry.Surfaces.stableTranslationGroup_mem _).mpr ⟨-n,by simp only [Int.cast_neg]⟩
  obtain ⟨g,hg,hconj⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
    C.normalizer S.stabilizer _).mp
    (C.stabilizer_eq.symm ▸ hT)
  let G:H:=⟨g,hg.1⟩
  refine ⟨G•x,Quotient.sound ⟨G,rfl⟩,w-(n:ℂ),?_,?_,?_,?_⟩
  · change 0≤w.re-(n:ℝ)
    exact sub_nonneg.mpr (Int.floor_le w.re)
  · change w.re-(n:ℝ)<1
    have hh:=Int.lt_floor_add_one w.re
    dsimp only [n]
    linarith
  · change t<w.im at hw
    simpa only [Complex.sub_im,Complex.intCast_im,sub_zero] using hw
  · change C.normalizer.val (g.val x.val)=_
    calc
      _=(C.normalizer*g*C.normalizer⁻¹).val (C.normalizer.val x.val) := by
        change C.normalizer • (g • x.val)=C.normalizer • (g • (C.normalizer⁻¹ • (C.normalizer • x.val)))
        rw [inv_smul_smul]
      _=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(n:ℂ))).val (C.normalizer.val
        x.val):=
        congrArg (fun f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup=>f.val (C.normalizer.val
          x.val)) hconj
      _=((w-(n:ℂ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
        rw [←hwx,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
        congr 1


theorem unitDisc_cusp_completion_deep_finite_area {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (c : FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) :
    ∃U : Set P.domain.carrier,IsOpen U∧P.area U≠⊤ ∧
      fuchsianCuspCompletionOld P.asFuchsianDisc ⁻¹'
        _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspDeepNeighborhood (fuchsianCuspChartNormalization
          P.asFuchsianDisc) c ⊆
          _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection P.domain '' U := by
  let D:=P.asFuchsianDisc
  let C:=fuchsianCuspChartNormalization D c
  obtain ⟨h,he,hh⟩:=cuspNormalization_original_domain_upper D C
  let q:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(h:ℂ)*Complex.I)*C.normalizer
  have hq : q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    change (fun z=>(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(h:ℂ)*Complex.I)).val
      (C.normalizer.val z)) '' D.carrier=_
    rw [←image_image,he]
    exact vertical_cusp_shift_image h
  let E:=geometricHalfPlaneChart D q hq
  let a:=C.height+1-h
  have ha : 0<a := by dsimp only [a];linarith
  let T:Set ℍ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun _=>a) (Ioo (-1) 2)
  have hT : IsOpen T := by
    exact ((isOpen_lt continuous_const UpperHalfPlane.continuous_re).inter
      (isOpen_lt UpperHalfPlane.continuous_re continuous_const)).inter
        (isOpen_lt continuous_const UpperHalfPlane.continuous_im)
  let U:=E ⁻¹' T
  have hU : IsOpen U:=hT.preimage E.continuous
  have hA : P.area U=volume T := by
    rw [←geometricModelArea_unitDisc_eq P U hU.measurableSet,
      geometricModelArea_eq_halfPlaneChart D q hq U hU.measurableSet]
    change volume (E '' (E ⁻¹' T))=volume T
    rw [image_preimage_eq _ E.surjective]
  refine ⟨U,hU,?_,?_⟩
  · rw [hA,parabolic_vertical_strip_above_volume _ _ _ ha]
    exact ENNReal.ofReal_ne_top
  · intro x hx
    obtain ⟨z,hz,hzx⟩:=cuspCompletion_old_deep_subset_finiteTail D c hx
    obtain ⟨y,hy,w,hw0,hw1,hwt,hyw⟩:=cusp_finiteTail_orbit_width_one D C (C.height+1) z hz
    refine ⟨y,?_,hy.trans hzx⟩
    have hEy : _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (E y)=((w-(h:ℂ)*Complex.I:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
      change (((E y:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=_
      rw [geometricHalfPlaneChart_extended]
      change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
        (-(h:ℂ)*Complex.I)).val (C.normalizer.val y.val)=_
      rw [hyw,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
      congr 1
      ring
    have hEyC : (E y:ℂ)=w-(h:ℂ)*Complex.I:=OnePoint.coe_injective hEy
    have hre : (E y).re=w.re := by
      change (E y:ℂ).re=w.re
      simpa only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,
        Complex.ofReal_im,Complex.I_im,zero_mul,sub_zero] using congrArg Complex.re hEyC
    have him : (E y).im=w.im-h := by
      change (E y:ℂ).im=w.im-h
      simpa only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,
        Complex.ofReal_im,Complex.I_re,mul_zero,zero_add,add_zero] using congrArg Complex.im hEyC
    change (E y).re∈Ioo (-1) 2 ∧ a<(E y).im
    rw [hre,him]
    exact ⟨⟨by linarith,by linarith⟩,by dsimp only [a];linarith⟩

end LowDimensionalTopology.Geometry.Fuchsian
