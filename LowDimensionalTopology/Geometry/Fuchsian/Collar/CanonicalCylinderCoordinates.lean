/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalCollarModels
public import Mathlib.Topology.Covering.AddCircle
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.CyclicAxisFundamentalDomains
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane OnePoint MatrixGroups Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Genuine global native coordinates: logarithmic height and signed
normal ratio. A positive dilation translates only the first coordinate. -/
def halfPlaneLogRatioHomeomorph : ℍ ≃ₜ ℝ×ℝ where
  toFun z:=(Real.log z.im,z.re/z.im)
  invFun p:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (Real.exp p.1*p.2) (Real.exp
    p.1) (Real.exp_pos _)
  left_inv z:=by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change Real.exp (Real.log z.im)*(z.re/z.im)=z.re
      rw [Real.exp_log z.im_pos]
      field_simp
    · change Real.exp (Real.log z.im)=z.im
      exact Real.exp_log z.im_pos
  right_inv p:=by
    apply Prod.ext
    · change Real.log (Real.exp p.1)=p.1
      exact Real.log_exp _
    · change Real.exp p.1*p.2/Real.exp p.1=p.2
      field_simp
  continuous_toFun:=by
    apply Continuous.prodMk
    · exact UpperHalfPlane.continuous_im.log (fun z=>z.im_pos.ne')
    · exact UpperHalfPlane.continuous_re.div UpperHalfPlane.continuous_im (fun z=>z.im_pos.ne')
  continuous_invFun:=by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun p:ℝ×ℝ=>(⟨Real.exp p.1*p.2,Real.exp p.1⟩:ℂ))
    have he:Continuous (fun p:ℝ×ℝ=>Real.exp p.1):=Real.continuous_exp.comp continuous_fst
    exact Complex.equivRealProdCLM.symm.continuous.comp ((he.mul continuous_snd).prodMk he)

/-- The exact inverse native coordinates. -/
theorem halfPlaneLogRatioHomeomorph_symm_im (p:ℝ×ℝ) :
    (halfPlaneLogRatioHomeomorph.symm p).im=Real.exp p.1 := rfl

theorem halfPlaneLogRatioHomeomorph_symm_re (p:ℝ×ℝ) :
    (halfPlaneLogRatioHomeomorph.symm p).re=Real.exp p.1*p.2 := rfl

/-- The exact signed normal ratio of the genuine vertical-axis canonical strip. -/
def logarithmicCanonicalStrip (b:ℝ) : Set ℍ:=
  {z | z.re/z.im∈Ioo (-b) b}

/-- The native strip is the product of the real geodesic parameter and
the actual open transverse interval, with its genuine native topology. -/
def logarithmicCanonicalStripHomeomorph (b:ℝ) :
    logarithmicCanonicalStrip b ≃ₜ ℝ×Ioo (-b) b where
  toFun z:=⟨Real.log z.val.im,⟨z.val.re/z.val.im,z.property⟩⟩
  invFun p:=⟨halfPlaneLogRatioHomeomorph.symm (p.1,p.2.val),by
    change (Real.exp p.1*p.2.val)/(Real.exp p.1)∈Ioo (-b) b
    simpa only [mul_div_cancel_left₀ _ (Real.exp_ne_zero _)] using p.2.property⟩
  left_inv z:=by
    apply Subtype.ext
    exact halfPlaneLogRatioHomeomorph.left_inv z.val
  right_inv p:=by
    apply Prod.ext
    · change Real.log (Real.exp p.1)=p.1
      exact Real.log_exp _
    · apply Subtype.ext
      change Real.exp p.1*p.2.val/Real.exp p.1=p.2.val
      field_simp
  continuous_toFun:=by
    apply Continuous.prodMk
    · exact (UpperHalfPlane.continuous_im.comp continuous_subtype_val).log
        (fun z=>z.val.im_pos.ne')
    · apply Continuous.subtype_mk
      exact (UpperHalfPlane.continuous_re.comp continuous_subtype_val).div
        (UpperHalfPlane.continuous_im.comp continuous_subtype_val) (fun z=>z.val.im_pos.ne')
  continuous_invFun:=by
    apply Continuous.subtype_mk
    exact halfPlaneLogRatioHomeomorph.symm.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- Every actual dilation power translates the genuine logarithmic
height coordinate and fixes the genuine transverse coordinate. -/
theorem dilation_logRatio_coordinates (l b:ℝ) (n:ℤ) (p:ℝ×Ioo (-b) b) :
    (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation
      l^n).val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint
      (((logarithmicCanonicalStripHomeomorph b).symm p).val))=
      _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ((logarithmicCanonicalStripHomeomorph b).symm (p.1+(n:ℝ)*l,p.2)) := by
  change (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n).val
    (((((logarithmicCanonicalStripHomeomorph b).symm
      p).val:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=_
  rw [stableAxisDilation_zpow_coe]
  change ((((Real.exp ((n:ℝ)*l):ℝ):ℂ)*
      (⟨Real.exp p.1*p.2.val,Real.exp p.1⟩:ℂ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
      ((⟨Real.exp (p.1+(n:ℝ)*l)*p.2.val,Real.exp
        (p.1+(n:ℝ)*l)⟩:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  apply congrArg ((↑):ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,add_zero,Real.exp_add] <;> ring

/-- The actual product-period map, on genuine transverse strip coordinates. -/
def logRatioPeriodMap (l b:ℝ) (p:ℝ×Ioo (-b) b) : AddCircle l×Ioo (-b) b :=
  ((p.1:AddCircle l),p.2)

theorem logRatioPeriodMap_isOpenQuotientMap (l b:ℝ) :
    IsOpenQuotientMap (logRatioPeriodMap l b) :=
  QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id

/-- The genuine product-period fibers retain exactly the original
integer period and the actual transverse coordinate. -/
theorem logRatioPeriodMap_fiber (l b:ℝ) (p q:ℝ×Ioo (-b) b) :
    logRatioPeriodMap l b p=logRatioPeriodMap l b q ↔
      ∃n:ℤ,p.1=q.1+(n:ℝ)*l ∧ p.2=q.2 := by
  constructor
  · intro h
    have ht: (p.1:AddCircle l)=q.1:=congrArg Prod.fst h
    obtain ⟨n,hn⟩:=AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp ht)
    change n • l=p.1-q.1 at hn
    rw [zsmul_eq_mul] at hn
    exact ⟨n,by linarith only [hn],congrArg (fun x:AddCircle l×Ioo (-b) b=>x.2) h⟩
  · rintro ⟨n,hn,hr⟩
    apply Prod.ext
    · apply QuotientAddGroup.eq_iff_sub_mem.mpr
      apply AddSubgroup.mem_zmultiples_iff.mpr
      refine ⟨n,?_⟩
      rw [zsmul_eq_mul]
      linarith only [hn]
    · exact hr

/-- The restricted original sphere orbit relation is exactly the genuine
circle-period fiber relation, throughout the whole canonical strip. -/
theorem logRatio_dilation_orbitRel_iff (l b:ℝ) (p q:ℝ×Ioo (-b) b) :
    (MulAction.orbitRel (Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l))
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ((logarithmicCanonicalStripHomeomorph
        b).symm p).val)
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ((logarithmicCanonicalStripHomeomorph
        b).symm q).val) ↔
      logRatioPeriodMap l b p=logRatioPeriodMap l b q := by
  let E:=logarithmicCanonicalStripHomeomorph b
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨n,hn⟩:=f.property
    change f.val.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (E.symm
      q).val)=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (E.symm p).val at hf
    rw [←hn,dilation_logRatio_coordinates] at hf
    have he:(q.1+(n:ℝ)*l,q.2)=p:=E.symm.injective
      (Subtype.ext (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective hf))
    exact (logRatioPeriodMap_fiber l b p q).mpr
      ⟨n,(congrArg Prod.fst he).symm,(congrArg Prod.snd he).symm⟩
  · intro h
    obtain ⟨n,hn,hr⟩:=(logRatioPeriodMap_fiber l b p q).mp h
    refine ⟨⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n,Subgroup.mem_zpowers_iff.mpr
      ⟨n,rfl⟩⟩,?_⟩
    change (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation
      l^n).val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (E.symm
      q).val)=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (E.symm p).val
    rw [dilation_logRatio_coordinates]
    have he:(q.1+(n:ℝ)*l,q.2)=p:=Prod.ext hn.symm hr.symm
    rw [he]

/-- The actual cyclic canonical-strip quotient is the genuine product
of the additive circle and the actual open transverse interval. -/
def logarithmicCanonicalStripQuotientHomeomorph (l b:ℝ) :
    Quotient ((MulAction.orbitRel (Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation
      l)) _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap
      (fun z:logarithmicCanonicalStrip b=>_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint
        z.val)) ≃ₜ
      AddCircle l×Ioo (-b) b := by
  let E:=logarithmicCanonicalStripHomeomorph b
  let F:C(ℝ×Ioo (-b) b,AddCircle l×Ioo (-b) b):=
    ⟨logRatioPeriodMap l b,(logRatioPeriodMap_isOpenQuotientMap l b).continuous⟩
  have hF:IsQuotientMap F:=(logRatioPeriodMap_isOpenQuotientMap l b).isQuotientMap
  refine (Homeomorph.Quotient.congr (rY:=Setoid.ker F) E ?_).trans hF.homeomorph
  intro z w
  have h:=logRatio_dilation_orbitRel_iff l b (E z) (E w)
  change (MulAction.orbitRel (Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l))
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint
      z.val) (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint w.val) ↔
    logRatioPeriodMap l b (E z)=logRatioPeriodMap l b (E w)
  simpa only [E,Homeomorph.symm_apply_apply] using h

/-- A nonzero actual dilation period gives the source topological
collar model, a genuine circle times the genuine open transverse interval. -/
def logarithmicCanonicalStripQuotientCircle (l b:ℝ) (hl:l≠0) :
    Quotient ((MulAction.orbitRel (Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation
      l)) _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap
      (fun z:logarithmicCanonicalStrip b=>_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint
        z.val)) ≃ₜ
      Circle×Ioo (-b) b :=
  (logarithmicCanonicalStripQuotientHomeomorph l b).trans
    ((AddCircle.homeomorphCircle hl).prodCongr (Homeomorph.refl _))

/-- The actual sphere trace of the normalized genuine canonical strip. -/
def logarithmicCanonicalSphere (b:ℝ) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=
  _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' logarithmicCanonicalStrip b

/-- The actual restricted sphere quotient has the same genuine product
collar model; no auxiliary replacement orbit relation is used. -/
def logarithmicCanonicalSphereQuotientCircle (l b:ℝ) (hl:l≠0) :
    Quotient ((MulAction.orbitRel (Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation
      l)) _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex).comap
      (Subtype.val:logarithmicCanonicalSphere b→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ≃ₜ Circle×Ioo (-b) b := by
  let E:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.isEmbedding.homeomorphImage (logarithmicCanonicalStrip b)
  exact (Homeomorph.Quotient.congr E (fun _ _=>Iff.rfl)).symm.trans
    (logarithmicCanonicalStripQuotientCircle l b hl)

/-- The source canonical width becomes exactly the actual transverse
interval in the normalized genuine product model. -/
theorem nativeCanonicalSphere_axis0 (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (haxis:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp
      hA)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0) :
    nativeCanonicalSphere A=logarithmicCanonicalSphere
      (1/Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)) := by
  rw [nativeCanonicalSphere,logarithmicCanonicalSphere]
  congr 1
  ext z
  rw [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_region_hyperbolic A hA).1]
  change Real.sinh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA.1.1
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA)).pointDist z)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)<1 ↔
    z.re/z.im∈Ioo (-(1/Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)))
      (1/Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2))
  rw [haxis,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalLine_pointDist_sinh,sub_zero]
  have hs:0<Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2):=by
    apply Real.sinh_pos_iff.mpr
    linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos A hA.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA)]
  change |z.re|/z.im*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)<1 ↔
    -(1/Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2))<z.re/z.im ∧
      z.re/z.im<1/Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)
  rw [←abs_lt,abs_div,abs_of_pos z.im_pos]
  exact (lt_div_iff₀ hs).symm

/-- The actual sphere image of the genuine vertical line is exactly
the actual imaginary geodesic used by the cyclic stabilizer model. -/
theorem native_vertical_axis_sphere :
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := by
  have hr:range _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier:=by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      rfl
    · intro hz
      refine ⟨Real.log z.im,?_⟩
      apply UpperHalfPlane.ext
      apply Complex.ext
      · exact hz.symm
      · exact Real.exp_log z.im_pos
  rw [←hr,←Set.range_comp]
  rfl

/-- The genuine original collar and its full cyclic stabilizer admit
one simultaneous actual geometric normalization. No period, cyclicity
or target strip is postulated. -/
theorem canonicalCollarSubset_normalizer {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    ∃q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      ∃l:ℝ,0<l ∧ ∃b:ℝ,0<b ∧
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (canonicalCollarSubset
          P hE A hs).stabilizer=
          Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) ∧
        q.val '' (canonicalCollarSubset P hE A hs).carrier=logarithmicCanonicalSphere b := by
  let S:=canonicalAxisSubset P hE A hs
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hs.2.1.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hs.2.1.1.1).mp hs.2.1)
  obtain ⟨q,hqH,hqL⟩:=_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxis_nativeLine_normalizer L
  have hqS:q.val '' S.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis:=hqL
  have hn:S.stabilizer≠⊥:=by
    intro he
    have hf:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈S.stabilizer:=⟨hs.1,nativeHyperbolicAxisSphere_self_image A hs.2.1⟩
    rw [he] at hf
    exact hs.2.1.1.1 hf
  obtain ⟨l,hl,hK,_hCircle⟩:=S.normalizedAxis_quotient_circle P.discrete
    (fun g hg=>P.preserves ⟨g,hg⟩) (fun g hg hEll=>(hE ⟨g,hg⟩ hEll).elim)
    hn q hqH hqS
  have hKR:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (canonicalCollarSubset P hE A hs).stabilizer=
      Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l):=by
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H (nativeCanonicalSphere A))=_
    rw [nativeCanonicalSphere_stabilizer_eq_axis P A hs.2.1]
    exact hK
  obtain ⟨B,hB⟩:=mobius_preserves_halfPlane_exists_SL q hqH
  let C:=B*A*B⁻¹
  have hC:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C):=by
    dsimp only [C]
    simpa only [map_mul,map_inv] using _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward _ _ hs.2.1
  have hCS:nativeHyperbolicAxisSphere C hC=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis:=by
    rw [nativeHyperbolicAxisSphere_conjugation A B hs.2.1,hB]
    exact hqS
  have hCaxis:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff C hC.1.1).mp hC)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
    apply (Set.image_injective.mpr _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective)
    exact hCS.trans native_vertical_axis_sphere.symm
  let b:=1/Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C)/2)
  have hb:0<b:=by
    apply one_div_pos.mpr
    apply Real.sinh_pos_iff.mpr
    linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos C hC.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff C hC.1.1).mp hC)]
  refine ⟨q,hqH,l,hl,b,hb,hKR,?_⟩
  change q.val '' nativeCanonicalSphere A=logarithmicCanonicalSphere b
  rw [←hB,←nativeCanonicalSphere_conjugation]
  exact nativeCanonicalSphere_axis0 C hC hCaxis

/-- Every genuine original simple-hyperbolic canonical collar is
actually a circle times an open interval, as a region in the genuine
original whole-group quotient surface. -/
theorem canonicalCollarSubset_image_circle_product {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    ∃b:ℝ,0<b ∧ Nonempty ((canonicalCollarSubset P hE A hs).quotientImage ≃ₜ Circle×Ioo (-b) b) := by
  obtain ⟨q,_hqH,l,hl,b,hb,hK,hS⟩:=canonicalCollarSubset_normalizer P hE A hs
  let S:=canonicalCollarSubset P hE A hs
  have ho:IsOpen (Subtype.val ⁻¹' S.carrier:Set P.asFuchsianDisc.domain.carrier):=
    (canonicalCollarSubset_isOpen P hE A hs).preimage continuous_subtype_val
  have E:S.Quotient ≃ₜ Circle×Ioo (-b) b:=by
    have E:=_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisConjugateQuotientHomeomorph S.stabilizer S.carrier q
    rw [hK,hS] at E
    exact E.trans (logarithmicCanonicalSphereQuotientCircle l b hl.ne')
  exact ⟨b,hb,⟨(S.openQuotientHomeomorph ho).symm.trans E⟩⟩

end LowDimensionalTopology.Geometry.Fuchsian
