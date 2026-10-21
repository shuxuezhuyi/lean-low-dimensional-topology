/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.ParabolicSidePairing
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.DiscPolygonConjugation
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance parabolicNormalizerSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance parabolicNormalizerSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

theorem mobiusScaling_translation_conjugation (u : ℂˣ) (b : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b * (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u)⁻¹ = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation ((u:ℂ)*b) := by
  have hi : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
    u)⁻¹ = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u⁻¹ := (map_inv
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom u).symm
  rw [hi]
  apply mobius_ext_on_halfPlane
  intro z
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
    u).val ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b).val
    ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u⁻¹).val
    ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))) = _
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
  congr 1
  simp only [Units.val_inv_eq_inv_val]
  field_simp [u.ne_zero]

theorem parabolicSL_translation_projection (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t:ℂ) := by
  apply mobius_ext_on_halfPlane
  intro z
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]

/-- Every genuine real parabolic has a whole-half-plane normalizer to the unit translation or its inverse. -/
theorem realSL_parabolic_unit_normalizer (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    ∃ q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      (q * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A * q⁻¹ =
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∨
       q * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A * q⁻¹ = (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹) := by
  obtain ⟨s,t,ht,hst⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  have hproj : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius s * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius s)⁻¹ = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t:ℂ) := by
    rw [←map_inv,←map_mul,←map_mul]
    rcases hst with he | he
    · rw [he,parabolicSL_translation_projection]
    · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg,parabolicSL_translation_projection]
  let k : ℝ := |t|⁻¹
  have hk : 0 < k := inv_pos.mpr (abs_pos.mpr ht)
  let u : ℂˣ := Units.mk0 (k:ℂ) (Complex.ofReal_ne_zero.mpr hk.ne')
  let q := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius s
  have hsc : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    rw [←realSLMobius_verticalDilation k hk]
    exact realSLMobius_image_openHalfPlane _
  refine ⟨q,?_,?_⟩
  · change (fun z => (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u).val
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius s).val
    z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _
    rw [←image_image,realSLMobius_image_openHalfPlane,hsc]
  · have he : q * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A * q⁻¹ = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation ((k*t:ℝ):ℂ) := by
      calc _ = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius s * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius s)⁻¹) *
          (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling u)⁻¹ := by dsimp [q];group
           _ = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation ((u:ℂ)*(t:ℂ)) := by rw [hproj,mobiusScaling_translation_conjugation]
           _ = _ := by congr 1;exact (Complex.ofReal_mul k t).symm
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · have hkt : k*t = -1 := by dsimp [k];rw [abs_of_neg hneg];field_simp
      right
      rw [he,hkt,Complex.ofReal_neg,Complex.ofReal_one,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_neg]
    · have hkt : k*t = 1 := by dsimp [k];rw [abs_of_pos hpos];exact inv_mul_cancel₀ ht
      left
      rw [he,hkt,Complex.ofReal_one]

/-- Inversion preserves the true unique-fixed-point parabolic type. -/
theorem sidePairing_parabolic_inverse {f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (hf :
  _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f⁻¹ := by
  obtain ⟨w,hw⟩ := hf.2
  refine ⟨inv_ne_one.mpr hf.1,w,fun z => ?_⟩
  constructor
  · intro hz
    have hh := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_inv_fixed hz
    have hfix : f.val z = z := by simpa only [inv_inv] using hh
    exact (hw z).mp hfix
  · intro hz
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobius_inv_fixed ((hw z).mpr hz)

/-- The complete primitive parabolic stabilizer is unchanged by taking its inverse generator. -/
theorem sidePairing_primitive_parabolic_inverse {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) (hp : IsPrimitive G f) :
    IsPrimitive G f⁻¹ := by
  apply (primitive_iff_of_parabolic (sidePairing_parabolic_inverse hf)).mpr
  refine ⟨G.inv_mem hp.mem,?_⟩
  intro z hz
  have hfix : f.val z = z := by simpa only [inv_inv] using _root_.LowDimensionalTopology.Geometry.Mobius.mobius_inv_fixed hz
  simpa only [Subgroup.zpowers_inv] using hp.generates z hfix

/-- Any actual whole-disc half-plane normalizer supplies the full native group, without dropping elementary cases. -/
theorem UnitDiscFuchsianGroup.normalizedHalfPlaneData {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    HalfPlaneFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      G) where
  preserves g := by
    obtain ⟨f,hf,he⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
      q G g.val).mp g.property
    rw [←he,←hq,_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image,P.image_eq ⟨f,hf⟩,hq]
  discrete := by
    let parabolicNormalizerOriginalDiscrete : DiscreteTopology G := P.discrete
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q G

/-- A genuine parabolic has a normalizer of the entire original model, not merely a fixed-point normal form. -/
theorem UnitDiscFuchsianGroup.parabolic_halfPlane_normalizer {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) (hfG : f ∈ G) :
    ∃ q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      (q*f*q⁻¹ = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∨ q*f*q⁻¹ = (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹) := by
  let p := _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
  let f0 := p*f*p⁻¹
  have hpres : f0.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    rw [←cayleyInverse_unitDisc_image]
    change (p*f*p⁻¹).val '' (p.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) = p.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image,P.image_eq ⟨f,hfG⟩]
  have hf0 : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f0 := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨p,rfl⟩)).mp hf
  obtain ⟨A,hA⟩ := mobius_preserves_halfPlane_exists_SL f0 hpres
  have hAP : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := hA ▸ hf0
  obtain ⟨r,hr,hunit⟩ := realSL_parabolic_unit_normalizer A hAP
  refine ⟨r*p,?_,?_⟩
  · change (fun z => r.val (p.val z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _
    rw [←image_image,cayleyInverse_unitDisc_image,hr]
  · have he : (r*p)*f*(r*p)⁻¹ = r*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*r⁻¹ := by rw [hA];dsimp [f0];group
    rwa [he]

/-- Both translation orientations genuinely pair sides of the corrected original Ford polygon. -/
theorem primitive_signed_unitTranslation_side_pairing {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hp :
      IsPrimitive H f)
    (hf : f = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∨ f =
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹) :
    ∃ D : Set P.cayleyData.domain.carrier, ∃ hD : IsConvexFuchsianPolygon P.cayleyData D,
      ∃ s : FuchsianPolygonSides P.cayleyData D,
        (fuchsianSideElement hD s).val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*f*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ := by
  rcases hf with he | he
  · subst f
    obtain ⟨s,hs⟩ := primitive_unitTranslation_side_pairing P hp
    exact ⟨_,primitive_unitTranslation_Ford_polygon P hp,s,congrArg (fun a => a.val) hs⟩
  · subst f
    have hpar : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr one_ne_zero
    have hpT : IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) := by
      simpa only [inv_inv] using sidePairing_primitive_parabolic_inverse (sidePairing_parabolic_inverse hpar) hp
    obtain ⟨s,hs⟩ := primitive_unitTranslation_side_pairing P hpT
    let hD := primitive_unitTranslation_Ford_polygon P hpT
    refine ⟨_,hD,fuchsianPairedSide hD s,?_⟩
    rw [fuchsianSideElement_paired]
    change (fuchsianSideElement hD s).val⁻¹ = _
    have hv : (fuchsianSideElement hD s).val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ :=
      congrArg (fun a => a.val) hs
    rw [hv]
    group

/-- Every original primitive parabolic pairs sides of a genuine convex locally finite fundamental polygon. -/
theorem primitive_parabolic_side_pairing {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup G) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) (hp : IsPrimitive G f) :
    ∃ D : Set P.domain.carrier, ∃ hD : IsConvexFuchsianPolygon P D,
      ∃ s : FuchsianPolygonSides P D, (fuchsianSideElement hD s).val = f := by
  obtain ⟨q,hq,hunit⟩ := P.parabolic_halfPlane_normalizer f hf hp.mem
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G
  let N := P.normalizedHalfPlaneData q hq
  let Q := N.cayleyData
  let k := q*f*q⁻¹
  have hkp : IsPrimitive K k := (isPrimitive_conjugation_iff G f q).mpr hp
  obtain ⟨D,hD,s,hs⟩ := primitive_signed_unitTranslation_side_pairing N k hkp hunit
  let r := _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*q
  have hr : r.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    change (fun z => _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val
      z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _
    rw [←image_image,hq,cayleyMobius_image_openHalfPlane]
  let e : G ≃* _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius K :=
    MulEquiv.trans (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
      G)
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius K)
  let F : P.domain.carrier ≃ₜ Q.domain.carrier := P.conjugateCoordinate r hr
  have hEquiv (g : G) (x : P.domain.carrier) : F (g • x) = e g • F x := by
    apply Subtype.ext
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val (g.val.val x.val)) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val (g.val.val (q.val.symm
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val x.val))))))
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm_apply_apply,q.val.symm_apply_apply]
  have harea : Measure.map F P.area = Q.area := P.conjugateCoordinate_area_map r hr
  have hiso : letI := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
      Isometry (fun z : Complex.UnitDisc => Q.finiteCoordinate (F (P.finiteCoordinate.symm z))) :=
    P.conjugateCoordinate_isometry r hr
  obtain ⟨hP,t,ht⟩ := equivariant_fuchsian_side_element_preimage P Q e F hEquiv harea hiso hD s
  have hse : fuchsianSideElement hD s = e ⟨f,hp.mem⟩ := Subtype.ext hs
  rw [hse,e.symm_apply_apply] at ht
  exact ⟨_,hP,t,congrArg (fun a : G => a.val) ht⟩

end LowDimensionalTopology.Geometry.Fuchsian
