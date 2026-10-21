/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticNontriangleSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.IdealTriangleCornerSectors
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.NonTriangleParabolicEllipticBounds
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.NontriangleCanonicalRegions
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicHyperbolicSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticParabolicTriangles
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPositiveReplacements
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane OnePoint MatrixGroups Pointwise ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
attribute [local instance] sharpEllipticEvaluationAction

/-- The zero-angle corner is the genuine parabolic matrix T(2)S. -/
theorem sharpParabolicCorner_eq : standardHeckeCornerSL 0=idealCornerSL 0 := by
  norm_num [standardHeckeCornerSL,idealCornerSL]

theorem sharpParabolicSector_eq : sharpEllipticSector 0=idealCornerSector 0 := by
  ext z
  norm_num [sharpEllipticSector,sharpEllipticCos,idealCornerSector]

theorem sharpParabolicSector_packing (g : ℍ≃ᵢℍ)
    (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL
      0))) (hne : g≠1) :
    Disjoint (g • sharpEllipticSector 0) (sharpEllipticSector 0) := by
  rw [sharpParabolicCorner_eq] at hg
  rw [sharpParabolicSector_eq]
  exact idealCornerSector_zero_disjoint g hg hne

theorem sharpParabolicSector_negative (z : ℍ) (hz : z.re<0) : z∈sharpEllipticSector 0 := by
  change z.re<sharpEllipticCos 0 ∧ z.re<sharpEllipticCos 0*Complex.normSq (z:ℂ)
  norm_num [sharpEllipticCos]
  exact ⟨by linarith,hz.trans_le (Complex.normSq_nonneg _)⟩

theorem sharpParabolicLeftSector_packing (t : ℝ) (g : ℍ≃ᵢℍ)
    (hg : g∈sharpEllipticLeftCyclic 0 t) (hne : g≠1) :
    Disjoint (g • sharpEllipticLeftSector 0 t) (sharpEllipticLeftSector 0 t) := by
  obtain ⟨a,ha,he⟩:=hg
  have ha1 : a≠1:=by
    intro h
    rw [h,map_one] at he
    exact hne he.symm
  have hdis:=sharpParabolicSector_packing a ha ha1
  apply disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ hz
  apply disjoint_left.mp hdis
  · refine ⟨sharpEllipticMirror t x,hx,?_⟩
    change a (sharpEllipticMirror t x)=sharpEllipticMirror t (g x)
    rw [←he]
    change _=sharpEllipticMirror t (sharpEllipticMirror t (a ((sharpEllipticMirror t)⁻¹ x)))
    rw [sharpEllipticMirror_involutive,sharpEllipticMirror_inv]
  · exact hz

theorem sharpParabolicElliptic_sectors_cover (q : ℕ) (hq : 2≤ q) (t : ℝ) (ht : 0<t) :
    sharpEllipticLeftSector 0 t∪sharpEllipticSector q=univ := by
  apply eq_univ_of_forall
  intro z
  by_cases hx : z.re<0
  · exact Or.inr (sharpEllipticSector_contains_negative q hq z hx)
  · apply Or.inl
    apply sharpParabolicSector_negative
    rw [sharpEllipticMirror_re]
    linarith [not_lt.mp hx]

theorem sharpParabolicElliptic_gap_strip (q : ℕ) (hq : 2≤ q) (t : ℝ) (z : ℍ)
    (hz : -t<z.re ∧ z.re<0) : z∈sharpEllipticNativeGap 0 q t := by
  constructor
  · apply sharpParabolicSector_negative
    rw [sharpEllipticMirror_re]
    linarith [hz.1]
  · exact sharpEllipticSector_contains_negative q hq z hz.2

theorem sharpParabolicElliptic_gap_nonempty (q : ℕ) (hq : 2≤ q) (t : ℝ) (ht : 0<t) :
    (sharpEllipticNativeGap 0 q t).Nonempty := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-t/2) 1 (by norm_num),sharpParabolicElliptic_gap_strip q hq t _ ?_⟩
  change -t< -t/2 ∧ -t/2<0
  constructor <;> linarith

theorem sharpParabolicElliptic_gap_wandering (q : ℕ) (hq : 2≤ q) (t : ℝ) (ht : 0<t)
    (g : ℍ≃ᵢℍ) (hg : g∈sharpEllipticNativeGroup 0 q t) (hne : g≠1) :
    Disjoint (g • sharpEllipticNativeGap 0 q t) (sharpEllipticNativeGap 0 q t) :=
  two_packing_domains_wandering (sharpEllipticLeftCyclic 0 t) (sharpEllipticRightCyclic q)
    (sharpEllipticLeftSector 0 t) (sharpEllipticSector q)
    (sharpParabolicLeftSector_packing t) (sharpEllipticSector_packing q hq)
    (sharpParabolicElliptic_sectors_cover q hq t ht) g hg hne

theorem sharpParabolicElliptic_native_discrete (q : ℕ) (hq : 2≤ q) (t : ℝ) (ht : 0<t) :
    DiscreteTopology (sharpEllipticNativeGroup 0 q t) := by
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteTopology_of_wandering_open (sharpEllipticNativeGap
    0 q t)
    (sharpEllipticNativeGap_isOpen 0 q t) (sharpParabolicElliptic_gap_nonempty q hq t ht)
  intro g hne
  apply sharpParabolicElliptic_gap_wandering q hq t ht g.val g.property
  intro he
  exact hne (Subtype.ext he)

/-- This is the actual parabolic/elliptic group; no discreteness is a field of its definition. -/
abbrev sharpParabolicEllipticGroup (q : ℕ) (t : ℝ) := sharpEllipticMobiusGroup 0 q t

theorem sharpParabolicEllipticData (q : ℕ) (hq : 2≤ q) (t : ℝ) (ht : 0<t) :
    HalfPlaneFuchsianGroup (sharpParabolicEllipticGroup q t) := by
  let : DiscreteTopology (sharpEllipticNativeGroup 0 q t):=sharpParabolicElliptic_native_discrete q hq t ht
  exact nativeConformalSubgroup_halfPlaneData _ _

def sharpParabolicNormalizer (t : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  modularInversionSL*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (1+t)

theorem sharpParabolicNormalizer_conjugation (t : ℝ) :
    sharpParabolicNormalizer t*sharpEllipticLeftSL 0 t*(sharpParabolicNormalizer t)⁻¹=
      -(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) := by
  ext i j
  fin_cases i <;>fin_cases j <;>
    norm_num [sharpParabolicNormalizer,sharpEllipticLeftSL,sharpEllipticCos,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two] <;>ring

theorem sharpParabolicLeft_parabolic (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpEllipticLeftSL 0 t)) := by
  have hp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpParabolicNormalizer t*sharpEllipticLeftSL 0 t*
      (sharpParabolicNormalizer t)⁻¹)):=by
    rw [sharpParabolicNormalizer_conjugation,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg,parabolicSL_translation_projection]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff _).mpr (by norm_num)
  rw [map_mul,map_mul,map_inv] at hp
  exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpParabolicNormalizer t),rfl⟩)).mpr hp

theorem sharpParabolicElliptic_nonElementary (q : ℕ) (hq : 3≤ q) (t : ℝ) (ht : 0<t) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (sharpParabolicEllipticGroup q t) := by
  let H:=sharpParabolicEllipticGroup q t
  let P:=sharpParabolicEllipticData q (by omega) t ht
  intro he
  let : Finite H:=elementary_elliptic_noninvolution_finite P.asFuchsianDisc he _
    (sharpEllipticRight_mem 0 q t) (sharpEllipticCorner_elliptic q (by omega))
    (by rw [sharpEllipticCorner_order q (by omega)];omega)
  have ho : IsOfFinOrder (⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpEllipticLeftSL 0
    t),sharpEllipticLeft_mem 0 q t⟩:H):=
    isOfFinOrder_of_finite _
  have ho' : IsOfFinOrder (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpEllipticLeftSL 0 t)):=by
    obtain ⟨n,hn,hpow⟩:=ho.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,congrArg Subtype.val hpow⟩
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_or_loxodromic_not_isOfFinOrder _ (Or.inl
    (sharpParabolicLeft_parabolic t)) ho'

theorem sharpParabolicElliptic_gap_real_midpoint (q : ℕ) (hq : 2≤ q) (t : ℝ) (ht : 0<t) :
    (((-t/2:ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈sharpEllipticSphereGap 0 q t := by
  rw [sharpEllipticSphereGap_mem]
  have hm : sharpEllipticPlaneMirror t ((-t/2:ℝ):ℂ)=((-t/2:ℝ):ℂ):=by
    rw [sharpEllipticPlaneMirror,Complex.conj_ofReal]
    push_cast
    ring
  have hc₁:=show 0≤ sharpEllipticCos 0 by norm_num [sharpEllipticCos]
  have hc₂:=sharpEllipticCos_nonneg q hq
  change sharpEllipticPlaneMirror t ((-t/2:ℝ):ℂ)∈sharpEllipticPlaneSector 0 ∧
    ((-t/2:ℝ):ℂ)∈sharpEllipticPlaneSector q
  rw [hm]
  constructor <;> constructor
  all_goals change -t/2<_
  · linarith
  · exact (by linarith : -t/2<0).trans_le (mul_nonneg hc₁ (Complex.normSq_nonneg _))
  · linarith
  · exact (by linarith : -t/2<0).trans_le (mul_nonneg hc₂ (Complex.normSq_nonneg _))

theorem sharpParabolicElliptic_gap_ordinary (q : ℕ) (hq : 2≤ q) (t : ℝ) (ht : 0<t) :
    sharpEllipticSphereGap 0 q t⊆_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet (sharpEllipticMobiusGroup 0 q t) := by
  let P:=sharpParabolicEllipticData q hq t ht
  let N:=sharpEllipticNativeGroup 0 q t
  let M:=nativeConformalSubgroupMobiusHom N (sharpEllipticNativeGroup_conformal 0 q t)
  let :=P.nativeAction
  apply halfPlane_native_wandering_gap_ordinary P _ (sharpEllipticSphereGap_isOpen 0 q t)
  change ∀g : sharpEllipticMobiusGroup 0 q t,g≠1→
    Disjoint (g • (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' sharpEllipticSphereGap 0 q
      t))
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' sharpEllipticSphereGap 0 q t)
  intro g hg
  obtain ⟨f,hf⟩:=g.property
  have hfne : f.val≠1:=by
    intro h
    have hf1 : f=1:=Subtype.ext h
    apply hg
    apply Subtype.ext
    rw [←hf,hf1,map_one]
    rfl
  have he (z : ℍ) : g • z=f.val z:=by
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    rw [←P.nativeAction_boundary,←hf]
    exact nativeConformalSubgroupMobiusHom_action N (sharpEllipticNativeGroup_conformal 0 q t) f z
  rw [sharpEllipticSphereGap_native_trace]
  have hset : g • sharpEllipticNativeGap 0 q t=f.val '' sharpEllipticNativeGap 0 q t:=by
    apply image_congr
    intro z _
    exact he z
  rw [hset]
  exact sharpParabolicElliptic_gap_wandering q hq t ht f.val f.property hfne


theorem sharpParabolicElliptic_secondKind (q : ℕ) (hq : 3≤q) (t : ℝ) (ht : 0<t) :
    (sharpParabolicEllipticData q (by omega) t ht).asFuchsianDisc.IsSecondKind := by
  let P:=sharpParabolicEllipticData q (by omega) t ht
  have hx:=sharpParabolicElliptic_gap_ordinary q (by omega) t ht
    (sharpParabolicElliptic_gap_real_midpoint q (by omega) t ht)
  refine ⟨P.asFuchsianDisc.limitSet_subset_frontier,?_⟩
  intro hfull
  have hfront : (((-t/2:ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    rw [nielsen_openHalfPlane_frontier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary]
    simp
  have hlim:=hfull hfront
  rw [fuchsianLimitSet_eq_nonElementary _ (sharpParabolicElliptic_nonElementary q hq t ht)] at hlim
  exact hx hlim

theorem sharpParabolicElliptic_not_triangle (q : ℕ) (hq : 3≤q) (t : ℝ) (ht : 0<t) :
    ¬IsMobiusTriangleGroup (sharpParabolicEllipticGroup q t) :=
  secondKind_not_mobiusTriangleGroup (sharpParabolicEllipticData q (by omega) t ht).asFuchsianDisc
    (sharpParabolicElliptic_nonElementary q hq t ht) (sharpParabolicElliptic_secondKind q hq t ht)

def sharpParabolicHeightDen (q : ℕ) (t : ℝ) : ℝ :=
  (1+t)^2+2*(1+t)*sharpEllipticCos q+1

theorem sharpParabolicHeightDen_pos (q : ℕ) (hq : 2≤q) (t : ℝ) :
    0<sharpParabolicHeightDen q t := by
  unfold sharpParabolicHeightDen
  nlinarith [sq_nonneg (1+t+sharpEllipticCos q),sharpElliptic_trig q,
    sq_pos_of_pos (sharpEllipticSin_pos q hq)]

theorem sharpParabolicCenter_im (q : ℕ) (hq : 2≤q) (t : ℝ) :
    (sharpParabolicNormalizer t • sharpEllipticRightCenter q hq).im=
      sharpEllipticSin q/sharpParabolicHeightDen q t := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.sl2_im_smul]
  change sharpEllipticSin q/Complex.normSq
    (((sharpParabolicNormalizer t 1 0:ℝ):ℂ)*(sharpEllipticRightCenter q hq:ℂ)+
      ((sharpParabolicNormalizer t 1 1:ℝ):ℂ))=_
  congr 1
  norm_num [sharpParabolicNormalizer,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,Matrix.mul_apply,
    Fin.sum_univ_two,sharpEllipticRightCenter,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply,
    sharpParabolicHeightDen]
  nlinarith [sharpElliptic_trig q]

theorem sharpParabolicElliptic_transformed_radial (q : ℕ) (hq : 2≤q) (t : ℝ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpParabolicNormalizer t*standardHeckeCornerSL q*
      (sharpParabolicNormalizer t)⁻¹)) z=
      sharpEllipticSin q*Real.sinh (dist
        (sharpParabolicNormalizer t • sharpEllipticRightCenter q hq) z) := by
  let Q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpParabolicNormalizer t)
  have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement_conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q)) Q (Q.symm z)
  rw [Q.apply_symm_apply] at h
  rw [←hSLIsometry_conjugation,sharpEllipticCorner_radial q hq] at h
  have hd:=Q.dist_eq (sharpEllipticRightCenter q hq) (Q.symm z)
  rw [Q.apply_symm_apply] at hd
  rw [←hd] at h
  exact h

/-- This is the actual all-half-plane infimum, rather than a bound at a test point. -/
theorem sharpParabolicElliptic_displacementM_square (q : ℕ) (hq : 2≤q) (t : ℝ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL 0 t))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q)))^2=
      (sharpParabolicHeightDen q t)^2/
        (4*((sharpEllipticSin q)^2+sharpParabolicHeightDen q t)) := by
  let Q:=sharpParabolicNormalizer t
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (Q*sharpEllipticLeftSL 0 t*Q⁻¹))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (Q*standardHeckeCornerSL q*Q⁻¹))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL 0 t))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q)):=by
    rw [hSLIsometry_conjugation,hSLIsometry_conjugation,_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_conjugation]
  rw [sharpParabolicNormalizer_conjugation,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_neg] at hc
  rw [←hc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_comm]
  rw [parabolic_radial_displacementM_square _ _
    (Q • sharpEllipticRightCenter q hq) (sharpEllipticSin q) 1
    (sharpEllipticSin_pos q hq) (by norm_num)
    (sharpParabolicElliptic_transformed_radial q hq t)
    (by
      intro z
      change Real.sinh (dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1 • z)/2)=_
      simpa only [abs_one] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.translation_half_displacement 1 z)]
  rw [sharpParabolicCenter_im]
  have hs:=sharpEllipticSin_pos q hq
  have hL:=sharpParabolicHeightDen_pos q hq t
  have hd : 0<(sharpEllipticSin q)^2+sharpParabolicHeightDen q t:=by positivity
  have hh : 0<sharpEllipticSin q*(sharpEllipticSin q/sharpParabolicHeightDen q t)+1:=by positivity
  field_simp [hs.ne',hL.ne',hd.ne',hh.ne']

def sharpParabolicEllipticM (q : ℕ) (t : ℝ) : ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL 0 t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q))

def sharpParabolicEllipticSourceBound (q : ℕ) : ℝ :=
  Real.sqrt ((1+sharpEllipticCos q)/(3-sharpEllipticCos q))

theorem sharpParabolicEllipticM_sqrt (q : ℕ) (hq : 2≤q) (t : ℝ) :
    sharpParabolicEllipticM q t=Real.sqrt ((sharpParabolicHeightDen q t)^2/
      (4*((sharpEllipticSin q)^2+sharpParabolicHeightDen q t))) := by
  calc
    _=Real.sqrt ((sharpParabolicEllipticM q t)^2):=
      (Real.sqrt_sq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)).symm
    _=_:=congrArg Real.sqrt (sharpParabolicElliptic_displacementM_square q hq t)

theorem sharpParabolicEllipticM_zero (q : ℕ) (hq : 2≤q) :
    sharpParabolicEllipticM q 0=sharpParabolicEllipticSourceBound q := by
  rw [sharpParabolicEllipticM_sqrt q hq]
  apply congrArg Real.sqrt
  have hL : sharpParabolicHeightDen q 0=2*(1+sharpEllipticCos q):=by
    simp only [sharpParabolicHeightDen,add_zero,one_pow]
    ring
  have hden : (sharpEllipticSin q)^2+2*(1+sharpEllipticCos q)=
      (3-sharpEllipticCos q)*(1+sharpEllipticCos q):=by
    nlinarith [sharpElliptic_trig q]
  rw [hL,hden]
  have hk : 0<1+sharpEllipticCos q:=by linarith [sharpEllipticCos_nonneg q hq]
  have hd : 0<3-sharpEllipticCos q:=by
    have h:=Real.cos_le_one (Real.pi/(q:ℝ))
    change sharpEllipticCos q≤1 at h
    linarith
  field_simp [hk.ne',hd.ne']
  ring

theorem sharpParabolicEllipticM_continuousAt_zero (q : ℕ) (hq : 2≤q) :
    ContinuousAt (sharpParabolicEllipticM q) 0 := by
  have hL : Continuous (sharpParabolicHeightDen q):=by unfold sharpParabolicHeightDen;fun_prop
  have hn : Continuous (fun t=>(sharpParabolicHeightDen q t)^2):=hL.pow 2
  have hd : Continuous (fun t=>4*((sharpEllipticSin q)^2+sharpParabolicHeightDen q t)):=by fun_prop
  have hpos : 0<4*((sharpEllipticSin q)^2+sharpParabolicHeightDen q 0):=by
    have h:=sharpParabolicHeightDen_pos q hq 0
    positivity
  have hf : sharpParabolicEllipticM q=(fun t=>Real.sqrt ((sharpParabolicHeightDen q t)^2/
      (4*((sharpEllipticSin q)^2+sharpParabolicHeightDen q t)))):=
    funext (sharpParabolicEllipticM_sqrt q hq)
  rw [hf]
  exact Real.continuous_sqrt.continuousAt.comp (hn.continuousAt.div hd.continuousAt hpos.ne')

theorem sharpParabolicEllipticM_tendsto (q : ℕ) (hq : 2≤q) :
    Tendsto (sharpParabolicEllipticM q) (𝓝[>] (0:ℝ)) (𝓝 (sharpParabolicEllipticSourceBound q)) := by
  have h:=(sharpParabolicEllipticM_continuousAt_zero q hq).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 (0:ℝ))
  rwa [sharpParabolicEllipticM_zero q hq] at h

theorem sharpParabolicElliptic_approaches_source (q : ℕ) (hq : 2≤q) (ε : ℝ) (hε : 0<ε) :
    ∃t : ℝ,0<t ∧ sharpParabolicEllipticM q t<sharpParabolicEllipticSourceBound q+ε := by
  have he : ∀ᶠt in 𝓝 (0:ℝ),sharpParabolicEllipticM q t<sharpParabolicEllipticSourceBound q+ε:=by
    have htarget : ∀ᶠy in 𝓝 (sharpParabolicEllipticM q 0),y<sharpParabolicEllipticSourceBound q+ε:=by
      rw [sharpParabolicEllipticM_zero q hq]
      exact eventually_lt_nhds (by linarith)
    exact (sharpParabolicEllipticM_continuousAt_zero q hq).tendsto.eventually htarget
  obtain ⟨δ,hδ,hball⟩:=Metric.eventually_nhds_iff.mp he
  refine ⟨δ/2,by linarith,hball ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_pos (by linarith : 0<δ/2)]
  linarith

/-- Each legal order at least three has genuine nontriangle original groups
approaching the printed bound; the limiting group itself is not used. -/
theorem parabolic_elliptic_nontriangle_order_displacement_bound_sharp (q : ℕ) (hq : 3≤q) (ε : ℝ) (hε : 0<ε) :
    ∃H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∃D : FuchsianDisc H,∃f g : H,
      Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)=H ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H ∧ ¬IsMobiusTriangleGroup H ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val ∧ orderOf g.val=q ∧
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D f g<Real.sqrt
        ((1+Real.cos (Real.pi/(q:ℝ)))/(3-Real.cos (Real.pi/(q:ℝ))))+ε := by
  obtain ⟨t,ht,hM⟩:=sharpParabolicElliptic_approaches_source q (by omega) ε hε
  let H:=sharpParabolicEllipticGroup q t
  let P:=sharpParabolicEllipticData q (by omega) t ht
  let f : H:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpEllipticLeftSL 0
    t),sharpEllipticLeft_mem 0 q t⟩
  let g : H:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL
    q),sharpEllipticRight_mem 0 q t⟩
  refine ⟨H,P.asFuchsianDisc,f,g,(sharpEllipticMobiusGroup_generators 0 q t).symm,
    sharpParabolicElliptic_nonElementary q hq t ht,sharpParabolicElliptic_not_triangle q hq t ht,
    sharpParabolicLeft_parabolic t,sharpEllipticCorner_elliptic q (by omega),
    sharpEllipticCorner_order q (by omega),?_⟩
  rw [halfPlane_realSL_displacementM P f g _ _ rfl rfl]
  exact hM

end LowDimensionalTopology.Geometry.Fuchsian
