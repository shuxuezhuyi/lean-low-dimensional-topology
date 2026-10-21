/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.PingPong
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.QuarterSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.ParabolicSideNormalizers
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianLimitSets
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped UpperHalfPlane OnePoint MatrixGroups Topology Pointwise ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The original lower-unipotent parabolic family. -/
def schottkyParabolicSL (c : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![1,0;c,1],by norm_num [Matrix.det_fin_two]⟩

def schottkyParabolicSLHom : Multiplicative ℝ→*Matrix.SpecialLinearGroup (Fin 2) ℝ where
  toFun c:=schottkyParabolicSL c.toAdd
  map_one':=by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [schottkyParabolicSL]
  map_mul' c d:=by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [schottkyParabolicSL,Matrix.mul_apply,Fin.sum_univ_two,add_comm]

theorem schottkyParabolicSL_zpow (c : ℝ) (k : ℤ) :
    schottkyParabolicSL c^k=schottkyParabolicSL ((k:ℝ)*c) := by
  change schottkyParabolicSLHom (Multiplicative.ofAdd c)^k=_
  rw [←map_zpow]
  change schottkyParabolicSL ((Multiplicative.ofAdd c^k).toAdd)=_
  rw [toAdd_zpow]
  congr 1
  exact zsmul_eq_mul c k

theorem schottkyParabolicSL_coe (c : ℝ) (z : ℂ) (hz : (c:ℂ)*z+1≠0) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL
      c)).val (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
      ((z/((c:ℂ)*z+1):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom (schottkyParabolicSL
      c))).val (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=_
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe]
  simp [schottkyParabolicSL,hz]

theorem schottkyParabolicSL_nontrivial (c : ℝ) (hc : c≠0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL c)≠1 := by
  intro hid
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL c)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (1:Matrix.SpecialLinearGroup (Fin 2) ℝ):=by
    simpa only [map_one] using hid
  rcases (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_iff_sign _ _).mp he with he|he
  all_goals
    have hh:=congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) ℝ=>A 1 0) he
    apply hc
    first | simpa [schottkyParabolicSL] using hh | simpa [schottkyParabolicSL] using hh.symm

theorem schottkyParabolicSL_parabolic (c : ℝ) (hc : c≠0) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL c)) := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff _ (schottkyParabolicSL_nontrivial
    c hc)).mpr
  norm_num [schottkyParabolicSL,Matrix.trace_fin_two]

theorem schottkyParabolicSL_zero (c : ℝ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL c)).val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  rw [schottkyParabolicSL_coe c 0 (by simp)]
  simp

/-- The true native half-displacement of the original parabolic family. -/
theorem schottkyParabolicSL_half_displacement (c : ℝ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (schottkyParabolicSL c)) z=
      |c| *Complex.normSq (z:ℂ)/(2*z.im) := by
  change Real.sinh (dist z (schottkyParabolicSL c•z)/2)=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_half_displacement_polynomial]
  change ‖(c:ℂ)*(z:ℂ)^2+(1-1)*(z:ℂ)-0‖/(2*z.im)=_
  simp [norm_pow,Complex.normSq_eq_norm_sq]

/-- An actual all-plane product formula, not a chosen-point bound. -/
theorem schottkyParabolicSL_product (c : ℝ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) z*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (schottkyParabolicSL c)) z=
        |c| *Complex.normSq (z:ℂ)/(4*z.im^2) := by
  change Real.sinh (dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z)/2)*_= _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.translation_half_displacement,schottkyParabolicSL_half_displacement]
  norm_num only [abs_one]
  field_simp
  ring

/-- The literal all-point infimum in the source is exactly |c|/4. -/
theorem schottkyParabolicSL_displacementP (c : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (schottkyParabolicSL c))=|c|/4 := by
  apply le_antisymm
  · have he:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_le (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (schottkyParabolicSL c)) UpperHalfPlane.I
    rw [schottkyParabolicSL_product] at he
    simpa using he
  · apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_lower_bound _ _ _).mpr
    intro z
    rw [schottkyParabolicSL_product]
    apply (le_div_iff₀ (by positivity : 0<4*z.im^2)).mpr
    rw [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    nlinarith only [mul_nonneg (abs_nonneg c) (sq_nonneg z.re)]

/-- The two actual parabolic fixed points are distinct, so the original
generated group is genuinely non-elementary for every nonzero parameter. -/
theorem schottkyParabolicSL_pair_nonElementary (c : ℝ) (hc : c≠0) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL c)}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  have hT:=quarterTranslation_parabolic
  have hU:=schottkyParabolicSL_parabolic c hc
  apply parabolic_pair_nonElementary_of_no_common_fixed _ _ hT
  apply parabolic_fixed_points_no_common _ _ hT hU ∞ ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  · rw [quarterTranslation_projection]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1
  · exact schottkyParabolicSL_zero c
  · exact OnePoint.infty_ne_coe _

/-- Nonzero integer translates of a narrow vertical strip have large real part. -/
theorem schottky_integer_translation_large (k : ℤ) (hk : k≠0) (z : ℂ)
    (hz : |z.re|<1/2) : 1/2 < |z.re+(k:ℝ)| := by
  have hkA : (1:ℝ)≤|(k:ℝ)|:=by
    exact_mod_cast (Int.one_le_abs hk)
  have ht : |(k:ℝ)|≤|z.re+(k:ℝ)|+|z.re|:=by
    calc
      _=|(z.re+(k:ℝ))+(-z.re)|:=by congr 1;ring
      _≤_:=by simpa only [Real.norm_eq_abs,abs_neg] using norm_add_le (z.re+(k:ℝ)) (-z.re)
  linarith only [hkA,ht,hz]

/-- Every nonidentity lower parabolic power maps outside a small Euclidean
circle strictly into that circle. The coefficient estimate is proved here. -/
theorem schottky_inverse_norm_bound (c a : ℝ) (hc : 0<c) (ha : 0<a)
    (hca : 2<c*a) (k : ℤ) (hk : k≠0) (z : ℂ) (hz : a<‖z‖) :
    1/a<‖z⁻¹+((k:ℝ)*c:ℝ)‖ ∧ ‖(z⁻¹+((k:ℝ)*c:ℝ))⁻¹‖<a := by
  have hz0 : z≠0:=norm_pos_iff.mp (lt_trans ha hz)
  have hi : ‖z⁻¹‖<1/a:=by
    rw [norm_inv,←one_div]
    exact one_div_lt_one_div_of_lt ha hz
  have hkA : (1:ℝ)≤|(k:ℝ)|:=by exact_mod_cast (Int.one_le_abs hk)
  have hcoef : c≤‖(((k:ℝ)*c:ℝ):ℂ)‖:=by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos hc]
    exact le_mul_of_one_le_left hc.le hkA
  have hsum : ‖(((k:ℝ)*c:ℝ):ℂ)‖≤‖z⁻¹+((k:ℝ)*c:ℝ)‖+‖z⁻¹‖:=by
    calc
      _=‖(z⁻¹+((k:ℝ)*c:ℝ))-z⁻¹‖:=by congr 1;ring
      _≤_:=norm_sub_le _ _
  have hcap : 2/a<c:=(div_lt_iff₀ ha).mpr (by nlinarith only [hca])
  have hcap' : (1/a)+(1/a)<c:=by
    calc
      (1/a)+(1/a)=2/a:=by ring
      _<c:=hcap
  have hden : 1/a<‖z⁻¹+((k:ℝ)*c:ℝ)‖:=by linarith only [hi,hcoef,hsum,hcap']
  refine ⟨hden,?_⟩
  rw [norm_inv]
  have hh:=one_div_lt_one_div_of_lt (one_div_pos.mpr ha) hden
  simpa only [one_div_one_div,one_div,inv_inv] using hh

/-- The exact original fractional action in inverse-coordinate form,
with its actual pole excluded explicitly. -/
theorem schottkyParabolicSL_inverse_coe (c : ℝ) (z : ℂ) (hz : z≠0)
    (hd : z⁻¹+(c:ℂ)≠0) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL
      c)).val (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
      (((z⁻¹+(c:ℂ))⁻¹:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  have he : (c:ℂ)*z+1=(z⁻¹+(c:ℂ))*z:=by
    rw [add_mul,inv_mul_cancel₀ hz]
    ring
  rw [schottkyParabolicSL_coe _ _ (he ▸ mul_ne_zero hd hz)]
  congr 1
  rw [he]
  field_simp

/-- Exact original-sphere integer translation action. -/
theorem schottkyTranslation_zpow_coe (k : ℤ) (z : ℂ) :
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      1))^k).val (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
      ((z+(k:ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  rw [←map_zpow,hTranslationSL_zpow,mul_one,parabolicSL_translation_projection,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]

/-- Exact original-sphere lower-parabolic powers away from their genuine pole. -/
theorem schottkyParabolic_zpow_inverse_coe (c a : ℝ) (hc : 0<c) (ha : 0<a)
    (hca : 2<c*a) (k : ℤ) (hk : k≠0) (z : ℂ) (hz : a<‖z‖) :
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL
      c))^k).val (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
      (((z⁻¹+((k:ℝ)*c:ℝ))⁻¹:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  have hd : z⁻¹+((k:ℝ)*c:ℝ)≠0:=norm_pos_iff.mp
    ((one_div_pos.mpr ha).trans (schottky_inverse_norm_bound c a hc ha hca k hk z hz).1)
  rw [←map_zpow,schottkyParabolicSL_zpow]
  exact schottkyParabolicSL_inverse_coe _ _ (norm_pos_iff.mp (ha.trans hz)) hd

def schottkyOuter : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=
  ((↑) : ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z : ℂ | 1/2 < |z.re|}

def schottkyInner (a : ℝ) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=
  ((↑) : ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z : ℂ | ‖z‖<a}

def schottkyGap (a : ℝ) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=
  ((↑) : ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' {z : ℂ | |z.re|<1/2 ∧ a<‖z‖}

/-- Nonidentity powers of the original unit translation send the entire
small circle, including exterior points of the half-plane model, into the strip complement. -/
theorem schottky_translation_inner (a : ℝ) (ha : a<1/2)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg : g∈Subgroup.zpowers
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)))
    (hne : g≠1) : g • schottkyInner a⊆schottkyOuter := by
  obtain ⟨k,rfl⟩:=hg
  have hk : k≠0:=by rintro rfl;exact hne (zpow_zero _)
  rintro w ⟨v,⟨z,hz,rfl⟩,rfl⟩
  refine ⟨z+(k:ℝ),?_,(schottkyTranslation_zpow_coe k z).symm⟩
  change 1/2 < |(z+(k:ℝ):ℂ).re|
  rw [Complex.add_re,Complex.ofReal_re]
  exact schottky_integer_translation_large k hk z
    ((Complex.abs_re_le_norm z).trans_lt (hz.trans ha))

/-- The same original powers carry the genuine open gap into that complement. -/
theorem schottky_translation_gap (a : ℝ)
    (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg : g∈Subgroup.zpowers
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)))
    (hne : g≠1) : g • schottkyGap a⊆schottkyOuter := by
  obtain ⟨k,rfl⟩:=hg
  have hk : k≠0:=by rintro rfl;exact hne (zpow_zero _)
  rintro w ⟨v,⟨z,hz,rfl⟩,rfl⟩
  exact ⟨z+(k:ℝ),by
    change 1/2 < |(z+(k:ℝ):ℂ).re|
    rw [Complex.add_re,Complex.ofReal_re]
    exact schottky_integer_translation_large k hk z hz.1,
    (schottkyTranslation_zpow_coe k z).symm⟩

/-- Every nonidentity lower-parabolic power takes the whole outer strip
into the small circle in the original compactified complex plane. -/
theorem schottky_parabolic_outer (c a : ℝ) (hc : 0<c) (ha : 0<a) (hau : a<1/2)
    (hca : 2<c*a) (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL
      c))) (hne : g≠1) :
    g • schottkyOuter⊆schottkyInner a := by
  obtain ⟨k,rfl⟩:=hg
  have hk : k≠0:=by rintro rfl;exact hne (zpow_zero _)
  rintro w ⟨v,⟨z,hz,rfl⟩,rfl⟩
  have hza : a<‖z‖:=lt_of_lt_of_le (hau.trans hz) (Complex.abs_re_le_norm z)
  exact ⟨(z⁻¹+((k:ℝ)*c:ℝ))⁻¹,
    (schottky_inverse_norm_bound c a hc ha hca k hk z hza).2,
    (schottkyParabolic_zpow_inverse_coe c a hc ha hca k hk z hza).symm⟩

theorem schottky_parabolic_gap (c a : ℝ) (hc : 0<c) (ha : 0<a)
    (hca : 2<c*a) (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL
      c))) (hne : g≠1) :
    g • schottkyGap a⊆schottkyInner a := by
  obtain ⟨k,rfl⟩:=hg
  have hk : k≠0:=by rintro rfl;exact hne (zpow_zero _)
  rintro w ⟨v,⟨z,hz,rfl⟩,rfl⟩
  exact ⟨(z⁻¹+((k:ℝ)*c:ℝ))⁻¹,
    (schottky_inverse_norm_bound c a hc ha hca k hk z hz.2).2,
    (schottkyParabolic_zpow_inverse_coe c a hc ha hca k hk z hz.2).symm⟩

theorem schottkyGap_isOpen (a : ℝ) : IsOpen (schottkyGap a) := by
  apply OnePoint.isOpen_image_coe.mpr
  exact (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    (isOpen_lt continuous_const continuous_norm)

/-- The genuine open gap contains an original real boundary point. -/
theorem schottkyGap_real_nonempty (a : ℝ) (ha : 0<a) (hau : a<1/2) :
    ∃x:ℝ,((x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈schottkyGap a := by
  let x : ℝ:=(a+1/2)/2
  have hx : 0<x:=by dsimp only [x];linarith only [ha]
  refine ⟨x,(x:ℂ),?_,rfl⟩
  change |(x:ℂ).re|<1/2 ∧ a<‖(x:ℂ)‖
  simp only [Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx]
  dsimp only [x]
  constructor <;> linarith only [hau]

theorem schottkyOuter_disjoint_gap (a : ℝ) : Disjoint schottkyOuter (schottkyGap a) := by
  apply disjoint_left.mpr
  rintro z ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
  have he' : v=u:=OnePoint.coe_injective he
  subst v
  exact (not_lt_of_ge hu.le) hv.1

theorem schottkyInner_disjoint_gap (a : ℝ) : Disjoint (schottkyInner a) (schottkyGap a) := by
  apply disjoint_left.mpr
  rintro z ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
  have he' : v=u:=OnePoint.coe_injective he
  subst v
  exact lt_asymm hu hv.2

def schottkyParabolicGroup (c : ℝ) : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup:=
  Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL c)} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)

theorem schottkyParabolicGroup_eq_sup (c : ℝ) :
    schottkyParabolicGroup c=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))⊔
      Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL c)) := by
  rw [Subgroup.zpowers_eq_closure,Subgroup.zpowers_eq_closure,←Subgroup.closure_union]
  congr 1

/-- The original generated whole group has a genuine open wandering gap
on the sphere; the normal-word argument controls every actual member. -/
theorem schottkyParabolicGroup_wandering (c a : ℝ) (hc : 0<c) (ha : 0<a)
    (hau : a<1/2) (hca : 2<c*a) (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hg : g∈schottkyParabolicGroup c) (hne : g≠1) :
    Disjoint (g • schottkyGap a) (schottkyGap a) := by
  let A:=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))
  let B:=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL c))
  let F : Bool→Type:=fun | false=>A | true=>B
  let schottkyFactorGroups : ∀b,Group (F b):=fun | false=>inferInstance | true=>inferInstance
  let f : ∀b,F b→*_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup:=fun | false=>A.subtype | true=>B.subtype
  let R : Bool→Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=fun b=>if b then schottkyInner a else schottkyOuter
  have hpp : Pairwise fun i j=>∀h:F i,h≠1→f i h • R j⊆R i:=by
    intro i j hij h hh
    cases i <;> cases j
    · exact False.elim (hij rfl)
    · exact schottky_translation_inner a hau h.val h.property (fun he=>hh (Subtype.ext he))
    · exact schottky_parabolic_outer c a hc ha hau hca h.val h.property (fun he=>hh (Subtype.ext he))
    · exact False.elim (hij rfl)
  have hstart : ∀i (h:F i),h≠1→f i h • schottkyGap a⊆R i:=by
    intro i h hh
    cases i
    · exact schottky_translation_gap a h.val h.property (fun he=>hh (Subtype.ext he))
    · exact schottky_parabolic_gap c a hc ha hca h.val h.property (fun he=>hh (Subtype.ext he))
  have hgap : ∀i,Disjoint (R i) (schottkyGap a):=by
    intro i
    cases i
    · exact schottkyOuter_disjoint_gap a
    · exact schottkyInner_disjoint_gap a
  have hrange : (Monoid.CoprodI.lift f).range=schottkyParabolicGroup c:=by
    rw [Monoid.CoprodI.range_eq_iSup]
    change (⨆b:Bool,(f b).range)=schottkyParabolicGroup c
    rw [iSup_bool_eq]
    change B.subtype.range⊔A.subtype.range=schottkyParabolicGroup c
    rw [Subgroup.range_subtype,Subgroup.range_subtype,sup_comm,schottkyParabolicGroup_eq_sup]
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.pingPong_range_wandering f R (schottkyGap
    a) hpp hstart hgap g _ hne
  rwa [hrange]

/-- The nonempty gap is constructed from the original source parameter. -/
theorem schottky_gap_parameter (c : ℝ) (hc : 4<c) :
    ∃a:ℝ,0<a ∧ a<1/2 ∧ 2<c*a := by
  have hcpos : 0<c:=by linarith only [hc]
  refine ⟨1/4+1/c,by positivity,?_,?_⟩
  · have hi:=one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<4) hc
    linarith only [hi]
  · have he : c*(1/c)=1:=by field_simp
    nlinarith only [hc,he]

/-- Every actual parameter c>4 gives a discrete original whole Mobius group. -/
theorem schottkyParabolicGroup_discrete (c : ℝ) (hc : 4<c) :
    _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (schottkyParabolicGroup c) := by
  obtain ⟨a,ha,hau,hca⟩:=schottky_gap_parameter c hc
  obtain ⟨x,hx⟩:=schottkyGap_real_nonempty a ha hau
  let p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=(x:ℂ)
  let f : schottkyParabolicGroup c→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=fun g=>g.val.val p
  have hcont : Continuous f:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusLocal_eval_continuous
    p).comp continuous_subtype_val
  have he : f ⁻¹' schottkyGap a=({1}:Set (schottkyParabolicGroup c)):=by
    ext g
    constructor
    · intro hgp
      apply Set.mem_singleton_iff.mpr
      by_contra hg
      have hne : g.val≠1:=fun h=>hg (Subtype.ext h)
      have hd:=schottkyParabolicGroup_wandering c a (by linarith only [hc]) ha hau hca g.val g.property hne
      exact disjoint_left.mp hd ⟨p,hx,rfl⟩ hgp
    · rintro rfl
      exact hx
  apply discreteTopology_of_isOpen_singleton_one
  rw [←he]
  exact (schottkyGap_isOpen a).preimage hcont

/-- The wandering gap is disjoint from the closure of all actual
loxodromic fixed points, hence belongs to the original ordinary set. -/
theorem schottkyGap_subset_ordinary (c a : ℝ) (hc : 0<c) (ha : 0<a)
    (hau : a<1/2) (hca : 2<c*a) : schottkyGap a⊆_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet (schottkyParabolicGroup c) := by
  have hsub : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLoxodromicFixedPointSet (schottkyParabolicGroup c)⊆(schottkyGap a)ᶜ:=by
    rintro z ⟨g,hg,hfix⟩ hz
    have hd:=schottkyParabolicGroup_wandering c a hc ha hau hca g.val g.property hg.1
    exact disjoint_left.mp hd ⟨z,hz,hfix⟩ hz
  have hcl : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet (schottkyParabolicGroup
    c)⊆(schottkyGap a)ᶜ:=
    closure_minimal hsub (schottkyGap_isOpen a).isClosed_compl
  intro z hz hlim
  exact hcl hlim hz

/-- The literal generated group preserves the original half-plane and is
discrete; its invariant-disc data are derived from the actual real lifts. -/
theorem schottkyParabolicGroup_data (c : ℝ) (hc : 4<c) :
    HalfPlaneFuchsianGroup (schottkyParabolicGroup c) where
  preserves g:=by
    have hreal : schottkyParabolicGroup c≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range:=by
      apply (Subgroup.closure_le _).mpr
      intro f hf
      rcases hf with rfl|rfl
      · exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1,rfl⟩
      · exact ⟨schottkyParabolicSL c,rfl⟩
    obtain ⟨A,hA⟩:=hreal g.property
    rw [←hA]
    exact realSLMobius_image_openHalfPlane A
  discrete:=schottkyParabolicGroup_discrete c hc

/-- The genuine original Fuchsian group is of the second kind: a real
boundary point lies in its proved ordinary gap. -/
theorem schottkyParabolicGroup_secondKind (c : ℝ) (hc : 4<c) :
    (schottkyParabolicGroup_data c hc).asFuchsianDisc.IsSecondKind := by
  obtain ⟨a,ha,hau,hca⟩:=schottky_gap_parameter c hc
  obtain ⟨x,hx⟩:=schottkyGap_real_nonempty a ha hau
  have hxO:=schottkyGap_subset_ordinary c a (by linarith only [hc]) ha hau hca hx
  refine ⟨(schottkyParabolicGroup_data c hc).asFuchsianDisc.limitSet_subset_frontier,?_⟩
  intro hfull
  have hxF : ((x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    rw [nielsen_openHalfPlane_frontier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary]
    simp
  have hxL:=hfull hxF
  rw [fuchsianLimitSet_eq_nonElementary (schottkyParabolicGroup c)
    (schottkyParabolicSL_pair_nonElementary c (by linarith only [hc]))] at hxL
  exact hxO hxL

/-- The actual second-kind parabolic examples approach the sharp improved
constant one in the true all-point product infimum. -/
theorem schottkyParabolic_secondKind_approaches (ε : ℝ) (hε : 0<ε) :
    ∃c:ℝ,∃hc:4<c,
      (schottkyParabolicGroup_data c hc).asFuchsianDisc.IsSecondKind ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (schottkyParabolicGroup c) ∧
      1<_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (schottkyParabolicSL c)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (schottkyParabolicSL c))<1+ε := by
  let c:=4+2*ε
  have hc : 4<c:=by dsimp only [c];linarith only [hε]
  refine ⟨c,hc,schottkyParabolicGroup_secondKind c hc,
    schottkyParabolicSL_pair_nonElementary c (by linarith only [hc]),?_,?_⟩
  all_goals
    rw [schottkyParabolicSL_displacementP,abs_of_pos (by linarith only [hc] : 0<c)]
    dsimp only [c]
    linarith only [hε]

/--
Exact source parameter t: the lower-left coefficient
is c=1/t, with its original open range and genuine second-kind group.
-/
theorem parabolic_schottky_source_parameter (t : ℝ) (ht : 0<t) (htu : t<1/4) :
    ∃hc:4<1/t,
      (schottkyParabolicGroup_data (1/t) hc).asFuchsianDisc.IsSecondKind ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (schottkyParabolicGroup (1/t)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (schottkyParabolicSL (1/t)))=1/(4*t) := by
  have hc : 4<1/t:=(lt_div_iff₀ ht).mpr (by linarith only [htu])
  refine ⟨hc,schottkyParabolicGroup_secondKind (1/t) hc,
    schottkyParabolicSL_pair_nonElementary (1/t) (by positivity),?_⟩
  rw [schottkyParabolicSL_displacementP,abs_of_pos (one_div_pos.mpr ht)]
  ring

/--
The literal geometric construction: reflection in
the circle with center -t and radius t, followed by reflection in the
imaginary axis, equals the original source parabolic on every native point.
-/
theorem schottkyParabolicSL_source_reflections (t : ℝ) (ht : 0<t) :
    (schottkyParabolicSL (1/t) • · : ℍ→ℍ)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection 0 ∘ _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection (-t) t ht := by
  funext z
  apply UpperHalfPlane.ext
  change ((schottkyParabolicSL (1/t)•z:ℍ):ℂ)=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection 0
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection (-t) t ht z):ℂ)
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [schottkyParabolicSL]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_coe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe]
  have htC : (t:ℂ)≠0:=by exact_mod_cast ht.ne'
  have hzT : (z:ℂ)+(t:ℂ)≠0:=by
    intro h
    have hi:=congrArg Complex.im h
    simp only [Complex.add_im,Complex.ofReal_im,Complex.zero_im,add_zero,UpperHalfPlane.coe_im] at hi
    exact z.im_pos.ne' hi
  simp only [map_add,map_div₀,map_pow,map_sub,Complex.conj_ofReal,Complex.conj_conj]
  push_cast
  field_simp [htC,hzT]
  ring

end LowDimensionalTopology.Geometry.Fuchsian
