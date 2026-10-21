/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.FiniteHullCuspBounds
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.FiniteAreaIdealBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspNormalizationGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteConvexBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped OnePoint UpperHalfPlane Complex.UnitDisc MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual closed Cayley coordinate intertwines the actual whole-sphere inverse Cayley map. -/
theorem closedCayley_inverse_sphere (p : 𝕔𝔻) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p).val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p) := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.injective
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p).val=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ • _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p)
  rw [smul_inv_smul]
  have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_toExtended (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.apply_symm_apply] at hh
  exact hh.symm

/-- The actual closed SL model isometry has exactly its original real Mobius action on every finite and ideal point of the whole compactified model. -/
theorem idealFanSLIsometry_halfPlane_sphere (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p : 𝕔𝔻) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry A).closedMap p)).val=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p).val := by
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGLClosedHalfPlaneHomeomorph (Matrix.SpecialLinearGroup.mapGL ℝ A) (by simp)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p)))).val=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm_apply_apply]
  change _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix (Matrix.SpecialLinearGroup.mapGL ℝ A))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm p).val=_
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_extended_action A _).symm

/-- Every genuine original cusp chart has a uniform real-coordinate bound on the actual original image of a finite closed hyperbolic hull. The original whole-disc normalizer is an actual coordinate change, not a geometric bound hypothesis. -/
theorem original_upper_chart_finite_hull_re_bound {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (h : ℝ)
    (hq : q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere h) (q₀ :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq₀ : q₀.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) {n : ℕ} (v : Fin
      n→𝕔𝔻) :
    ∃M : ℝ,0<M∧∀p : 𝕔𝔻,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈convexHull ℝ (range (fun
        i=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (v i)))→
      ∀w : ℂ,q.val (q₀⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p))=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→|w.re|≤M := by
  let r:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(h:ℂ)*Complex.I)*q
  have hr : r.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    change ((fun z=>(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(h:ℂ)*Complex.I)).val
      (q.val z)) '' D.carrier)=_
    rw [←image_image,hq]
    exact vertical_cusp_shift_image h
  have hshift (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (w : ℂ) (hw : q.val
    z=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
      r.val z=((w-(h:ℂ)*Complex.I:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(h:ℂ)*Complex.I)).val (q.val z)=_
    rw [hw,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
    congr 1
    ring
  let f:=r*q₀⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
  have hf : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    have him : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=
        r.val '' (q₀⁻¹.val '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)):=by
      rw [image_image,image_image]
      rfl
    have hcancel : q₀⁻¹.val '' (q₀.val '' D.carrier)=D.carrier:=by
      change q₀.val.symm '' (q₀.val '' D.carrier)=D.carrier
      exact q₀.val.symm_image_image _
    rw [him,cayleyMobius_image_openHalfPlane,←hq₀,hcancel,hr]
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL f hf
  obtain ⟨M,hM,hbound⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.finite_closed_hull_cusp_re_bounded v (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry A)
  refine ⟨M,hM,?_⟩
  intro p hp w hw
  have hvalue : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealFanSLIsometry A).closedMap p)).val=
      ((w-(h:ℂ)*Complex.I:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    rw [idealFanSLIsometry_halfPlane_sphere,hA,closedCayley_inverse_sphere]
    change r • (q₀⁻¹ • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius •
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ •
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p)))=_
    rw [smul_inv_smul]
    exact hshift _ w hw
  have hh:=hbound p hp (w-(h:ℂ)*Complex.I) hvalue
  simpa only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.I_re,mul_zero,
    Complex.ofReal_im,Complex.I_im,zero_mul,sub_zero] using hh

/-- Every genuine original cusp normalization inherits the actual finite-hull real-coordinate bound with no bounded-strip assumption. -/
theorem original_cusp_finite_hull_re_bound {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) {S : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D.domain} {η :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S η) (q₀ :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq₀ : q₀.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) {n : ℕ} (v : Fin
      n→𝕔𝔻) :
    ∃M : ℝ,0<M∧∀p : 𝕔𝔻,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈convexHull ℝ (range (fun
        i=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (v i)))→
      ∀w : ℂ,C.normalizer.val (q₀⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p))=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→|w.re|≤M := by
  obtain ⟨h,hq,_hh⟩:=cuspNormalization_original_domain_upper D C
  exact original_upper_chart_finite_hull_re_bound D C.normalizer h hq q₀ hq₀ v

/-- Every genuine closed disc point returns to the actual closure of the original whole disc. -/
theorem original_closed_model_mem_closure {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (q₀ : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq₀ : q₀.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (p : 𝕔𝔻) :
    q₀⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p)∈closure D.carrier := by
  have hp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p∈closure _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=by
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedOpenDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=by
      ext z
      cases z with
      | infty=>simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedOpenDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc]
      | coe z=>simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedOpenDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc,Metric.mem_ball,dist_zero_right]
    rw [←he]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closure_extendedOpenDisc,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_closedDiscToExtended]
    exact mem_range_self p
  rw [←hq₀] at hp
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p∈closure ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q₀) '' D.carrier) at hp
  rw [←(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q₀).image_closure] at hp
  obtain ⟨z,hz,he⟩:=hp
  have heq : q₀⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p)=z:=by
    change q₀.val.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p)=z
    rw [←he]
    exact q₀.val.symm_apply_apply z
  rw [heq]
  exact hz

/-- A whole-disc upper horizontal chart gives a genuine lower imaginary-coordinate bound on every original closed model point. -/
theorem original_upper_chart_closed_model_im_bound {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (h : ℝ)
    (hq : q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere h) (q₀ :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq₀ : q₀.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (p : 𝕔𝔻) (w : ℂ)
    (hw : q.val (q₀⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p))=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) : h≤w.im := by
  have hz:=original_closed_model_mem_closure D q₀ hq₀ p
  have him : (w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈closure (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere h):=by
    rw [←hq]
    change (w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈closure ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q) '' D.carrier)
    rw [←(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).image_closure]
    exact ⟨_,hz,hw⟩
  have hpre : w∈((↑) : ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⁻¹' closure (((↑) :
    ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {w : ℂ | h<w.im}):=him
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.onePoint_coe_preimage_closure_image] at hpre
  exact closure_minimal (fun z hz=>hz.le)
    (isClosed_le continuous_const Complex.continuous_im) hpre

/-- Every actual orbit cusp chart inherits uniform finite-coordinate bounds on a genuine original finite hyperbolic hull. No coordinate-bound hypothesis is supplied. -/
theorem original_orbit_cusp_finite_hull_coordinates {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .parabolic) (g : H)
    (q₀ : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq₀ : q₀.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    {n : ℕ} (v : Fin n→𝕔𝔻) :
    ∃M h : ℝ,0<M∧∀p : 𝕔𝔻,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈convexHull ℝ (range (fun
        i=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (v i)))→
      ∀w : ℂ,((fuchsianCuspChartNormalization D c).normalizer*g.val⁻¹).val
        (q₀⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p))=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→|w.re|≤M∧h≤w.im := by
  let C:=fuchsianCuspChartNormalization D c
  let q:=C.normalizer*g.val⁻¹
  obtain ⟨h,hC,_hh⟩:=cuspNormalization_original_domain_upper D C
  have hq : q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere h:=by
    change ((fun z=>C.normalizer.val (g.val⁻¹.val z)) '' D.carrier)=_
    rw [←image_image]
    have hg : g.val⁻¹.val '' D.carrier=D.carrier:=D.image_eq g⁻¹
    rw [hg,hC]
  obtain ⟨M,hM,hbound⟩:=original_upper_chart_finite_hull_re_bound D q h hq q₀ hq₀ v
  refine ⟨M,h,hM,?_⟩
  intro p hp w hw
  exact ⟨hbound p hp w hw,original_upper_chart_closed_model_im_bound D q h hq q₀ hq₀ p w hw⟩

/-- The actual original sphere image of the closed hyperbolic hull of a finite family of genuine closed model points. -/
def originalFiniteClosedHull (q₀ : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) {n : ℕ} (v : Fin
  n→𝕔𝔻) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=
  (fun p : 𝕔𝔻=>q₀⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p)) ''
    {p | _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈convexHull ℝ (range (fun
      i=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (v i)))}

/-- This actual original finite hull is compact in the original sphere topology. -/
theorem originalFiniteClosedHull_isCompact (q₀ : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) {n :
  ℕ} (v : Fin n→𝕔𝔻) :
    IsCompact (originalFiniteClosedHull q₀ v) := by
  have hc : IsClosed {p : 𝕔𝔻 | _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈
      convexHull ℝ (range (fun i=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (v i)))}:=
    ((finite_range _).isClosed_convexHull
      ℝ).preimage _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.continuous
  exact hc.isCompact.image ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
    q₀⁻¹).continuous.comp
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_closedDiscToExtended.continuous)

/-- All genuine translated cusp charts have proved real and lower-imaginary bounds on the actual original finite hull; the hypotheses are actual whole-disc coordinates, without supplied coordinate bounds. -/
theorem originalFiniteClosedHull_cusp_bounds {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (q₀ : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq₀ : q₀.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) {n : ℕ} (v : Fin
      n→𝕔𝔻) :
    ∀(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),∃M h : ℝ,
      ∀z∈originalFiniteClosedHull q₀ v,∀w : ℂ,
        ((fuchsianCuspChartNormalization D
          c).normalizer*g.val⁻¹).val z=(w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→
          |w.re|≤M∧h≤w.im := by
  intro c g
  obtain ⟨M,h,_hM,hbound⟩:=original_orbit_cusp_finite_hull_coordinates D c g q₀ hq₀ v
  refine ⟨M,h,?_⟩
  rintro z ⟨p,hp,rfl⟩ w hw
  exact hbound p hp w hw

end LowDimensionalTopology.Geometry.Fuchsian
