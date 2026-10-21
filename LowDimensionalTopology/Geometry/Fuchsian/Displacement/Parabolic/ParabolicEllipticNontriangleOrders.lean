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

/-- The exact scalar bound forced by the true primitive-center height. -/
theorem parabolic_radial_height_order_scalar (s k v : ℝ) (hs : 0<s) (hk : 0<k)
    (hv : 0<v) (hh : 2*k*v≤ s) :
    k^2/(s^2+2*k)≤ s/(4*v*(s*v+1)) := by
  have hd : 0<4*v*(s*v+1):=by positivity
  have he : 0<s^2+2*k:=by positivity
  have hsq:=(sq_le_sq₀ (show 0≤2*k*v by positivity) hs.le).mpr hh
  have hp:=mul_le_mul_of_nonneg_left hsq hs.le
  have hl:=mul_le_mul_of_nonneg_left hh (show 0≤2*k by positivity)
  apply (div_le_div_iff₀ he hd).mpr
  nlinarith only [hp,hl]

/-- A true nontriangle ambient group excludes every elliptic mixed product. -/
theorem HalfPlaneFuchsianGroup.nontriangle_translation_product_trace
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (hnt : ¬IsMobiusTriangleGroup H) (t : ℝ) (ht : t≠0)
    (hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H) : 4≤(Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*B).val)^2 := by
  by_contra hn
  have hlt : (Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
    t*B).val)^2<4:=lt_of_not_ge hn
  have hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*B)≠1:=by
    intro he
    have h1 : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (1:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)=(4:ℂ):=by
      have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace (1:Matrix.SpecialLinearGroup
        (Fin 2) ℝ)
      norm_num [Matrix.trace_fin_two] at hh
      exact hh
    have hh:=congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace he
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,h1] at hh
    have hr : (Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      t*B).val)^2=4:=Complex.ofReal_injective hh
    linarith
  have hprod : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*B)):=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ hne).mpr hlt
  have hp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)):=by
    rw [parabolicSL_translation_projection]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff _).mpr (by exact_mod_cast ht)
  exact hnt (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.parabolic_elliptic_product_forces_triangle
    P _ B hp hB hT hBH hprod)

/-- Both actual translation directions give the order-sensitive coefficient gap. -/
theorem HalfPlaneFuchsianGroup.nontriangle_translation_elliptic_coefficient
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (hnt : ¬IsMobiusTriangleGroup H) (t : ℝ) (ht : t≠0)
    (hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H) : 2+|Matrix.trace B.val|≤ |t*B 1 0| := by
  have hmT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t))∈H:=by
    rw [canonical_translation_inverse,map_inv]
    exact H.inv_mem hT
  have hp:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nontriangle_translation_product_trace P hnt t ht hT B hB hBH
  have hm:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nontriangle_translation_product_trace P hnt (-t) (neg_ne_zero.mpr ht) hmT B hB hBH
  rw [canonical_translation_mul_trace] at hp hm
  have hm' : 4≤(Matrix.trace B.val-t*B 1 0)^2:=by simpa only [neg_mul,sub_eq_add_neg] using hm
  have hg:=trace_pair_abs_gap (Matrix.trace B.val) (t*B 1 0) hp hm'
  have htr := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB
  have hsmall : |Matrix.trace B.val|<2:=by nlinarith [sq_abs (Matrix.trace B.val),abs_nonneg (Matrix.trace B.val)]
  by_contra hn
  have hu : |t*B 1 0|<2+|Matrix.trace B.val|:=lt_of_not_ge hn
  have ha : |Matrix.trace B.val|-|t*B 1 0|<2:=by linarith [abs_nonneg (t*B 1 0)]
  have hb : -2< |Matrix.trace B.val|-|t*B 1 0|:=by linarith
  have hp:=mul_pos (by linarith : 0<2-(|Matrix.trace B.val|-|t*B 1 0|))
    (by linarith : 0<2+(|Matrix.trace B.val|-|t*B 1 0|))
  nlinarith only [hp,hg]

/-- Exact least-rotation bound, using only the original nontriangle group. -/
theorem HalfPlaneFuchsianGroup.nontriangle_translation_least_elliptic_bound
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (hnt : ¬IsMobiusTriangleGroup H) (t : ℝ) (ht : t≠0)
    (hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H) (hl : HasLeastEllipticRotation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hq : 3≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    Real.sqrt ((1+Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)))/
      (3-Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))))≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  let θ:=Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
  let s:=Real.sin θ
  let c:=Real.cos θ
  let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  let v:=u.im/|t|
  have hqR : (2:ℝ)<orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by exact_mod_cast (by omega : 2<orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
  have hθ:=pi_div_acute_of_two_lt (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) hqR
  have hs : 0<s:=Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2,Real.pi_pos])
  have hc : 0<c:=Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
  have htpos : 0< |t|:=abs_pos.mpr ht
  have hv : 0<v:=div_pos u.im_pos htpos
  have hsin : Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B
    hB/2)=s:=least_elliptic_actual_sin_half B hB hl
  have htr : |Matrix.trace B.val|=2*c:=by
    have he:=hl.squaredTrace_order
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace] at he
    have he' : (Matrix.trace B.val)^2=4*c^2:=Complex.ofReal_injective he
    apply (sq_eq_sq₀ (abs_nonneg _) (by positivity : 0≤2*c)).mp
    nlinarith only [he',sq_abs (Matrix.trace B.val)]
  have hcoef:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nontriangle_translation_elliptic_coefficient P hnt t ht hT B hB hBH
  rw [htr,abs_mul] at hcoef
  have hheight : 2*(1+c)*v≤ s:=by
    have hh:=mul_le_mul_of_nonneg_right hcoef u.im_pos.le
    have he:=elliptic_actual_angle_height B hB
    rw [hsin] at he
    change s= |B 1 0| *u.im at he
    rw [mul_assoc,←he] at hh
    change 2*(1+c)*(u.im/|t|)≤ s
    rw [←mul_div_assoc]
    apply (div_le_iff₀ htpos).mpr
    nlinarith only [hh,he]
  have hM:=translation_elliptic_displacementM_square B hB t ht
  dsimp only at hM
  rw [hsin] at hM
  have hM' : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2=
      s/(4*v*(s*v+1)):=by
    rw [hM]
    change s*t^2/(4*u.im*(s*u.im+|t|))=s/(4*(u.im/|t|)*(s*(u.im/|t|)+1))
    rw [←sq_abs t]
    have hsum : s*u.im+|t|≠0:=ne_of_gt (by positivity)
    field_simp [htpos.ne',u.im_ne_zero,hsum]
  have hbound:=parabolic_radial_height_order_scalar s (1+c) v hs (by positivity) hv hheight
  have he : s^2+2*(1+c)=(3-c)*(1+c):=by nlinarith [Real.sin_sq_add_cos_sq θ]
  have heq : (1+c)^2/((3-c)*(1+c))=(1+c)/(3-c):=by
    field_simp
  rw [he,heq,←hM'] at hbound
  exact Real.sqrt_le_iff.mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _,hbound⟩

/-- The bound uses the original elliptic order, without a primitive-angle hypothesis. -/
theorem HalfPlaneFuchsianGroup.nontriangle_translation_elliptic_order_bound
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (hnt : ¬IsMobiusTriangleGroup H) (t : ℝ) (ht : t≠0)
    (hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H) (hq : 3≤orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    Real.sqrt ((1+Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)))/
      (3-Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))))≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  obtain ⟨C,hC,hCH,hlC,haC,hcenter,_hstab,hpow,horder⟩:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_exists_native_positive_replacement P B hB hBH
  have hCq : 3≤orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C):=hq.trans horder
  have hC2 : 2≤orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C):=by omega
  have hB2 : 2≤orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by omega
  have hsmall : Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)∈Ioc 0 (Real.pi/2):=by
    have hnR : (2:ℝ)≤orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C):=by exact_mod_cast hC2
    have hn0 : (0:ℝ)<orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C):=by linarith
    exact ⟨div_pos Real.pi_pos hn0,
      div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR⟩
  have hsC : Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle C hC/2)≤
      Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2):=by
    rw [least_elliptic_actual_sin_half C hC hlC]
    exact elliptic_sin_half_lower_of_trace_bound B hB hsmall
      (least_elliptic_nonidentity_power_trace_bound C B hC hlC hB.1 hpow)
  have hM : _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C)≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B):=by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_lower_bound _ _ _).mpr
    intro z
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_le _ _ z).trans
    apply max_le_max le_rfl
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_actual_angle_radial C
      hC,_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_actual_angle_radial B hB,hcenter]
    exact mul_le_mul_of_nonneg_right hsC (Real.sinh_nonneg_iff.mpr dist_nonneg)
  have hcos : Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))≤
      Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)):=by
    simpa only [triangleOrderAngle_nat] using
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleOrderCos_monotone_of_two_le
        (p := (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):ℕ∞)) (q := (orderOf
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C):ℕ∞))
        (by exact_mod_cast hB2) (by exact_mod_cast horder)
  have hratio : (1+Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)))/
      (3-Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)))≤
      (1+Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)))/
      (3-Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C))):=by
    apply (div_le_div_iff₀ (by linarith [Real.cos_le_one (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))])
      (by linarith [Real.cos_le_one (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C))])).mpr
    nlinarith only [hcos]
  exact (Real.sqrt_le_sqrt hratio).trans
    ((_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nontriangle_translation_least_elliptic_bound P hnt t ht hT C hC hCH hlC hCq).trans hM)

/-- The normalized estimate transports to every genuine parabolic real lift. -/
theorem HalfPlaneFuchsianGroup.nontriangle_parabolic_elliptic_order_bound
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (hnt : ¬IsMobiusTriangleGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H) (hBH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hq : 3≤orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    Real.sqrt ((1+Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)))/
      (3-Real.cos (Real.pi/orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))))≤
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  obtain ⟨q,t,ht,hnorm⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H
  have hKd : DiscreteTopology K:=by
    let : DiscreteTopology H:=P.discrete
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H
  let PK : HalfPlaneFuchsianGroup K:=⟨by
    rintro ⟨f,⟨g,hg,rfl⟩⟩
    exact orderBound_real_conjugate_halfPlane g q (P.preserves ⟨g,hg⟩),hKd⟩
  have hntK : ¬IsMobiusTriangleGroup K:=fun h=>hnt (isMobiusTriangleGroup_of_conjugate H _ h)
  have hAq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t):=by
    rcases hnorm with he|he
    · rw [he]
    · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  have hT : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈K:=by
    rw [←hAq,map_mul,map_mul,map_inv]
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hAH,rfl⟩
  have hBK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)∈K:=by
    rw [map_mul,map_mul,map_inv]
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,hBH,rfl⟩
  have hBq : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)):=by
    have h:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hB
    simpa only [map_mul,map_inv] using h
  have horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹))=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by
    have h:=(MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      q)).orderOf_eq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
    change orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      q)⁻¹)=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) at h
    simpa only [map_mul,map_inv] using h
  have hb:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nontriangle_translation_elliptic_order_bound PK hntK t ht hT
    (q*B*q⁻¹) hBq hBK (by rwa [horder])
  rw [horder] at hb
  have hnormI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t):=by
    rcases hnorm with he|he
    · rw [he]
    · rw [he]
      apply IsometryEquiv.ext
      intro z
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_neg_smul _ z
  rw [←hnormI,hSLIsometry_conjugation A q,hSLIsometry_conjugation B
    q,_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_conjugation] at hb
  exact hb

/-- The original-order nontriangle bound on the whole original disc. -/
theorem fuchsian_nontriangle_parabolic_elliptic_order_displacementM_bound
    (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) (hg :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (hnt : ¬IsMobiusTriangleGroup (Subgroup.closure ({f,g}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hq : 3≤orderOf g) :
    Real.sqrt ((1+Real.cos (Real.pi/orderOf g))/(3-Real.cos (Real.pi/orderOf g)))≤
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D ⟨f,Subgroup.subset_closure (by simp)⟩
        ⟨g,Subgroup.subset_closure (by simp)⟩ := by
  let F : Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=⟨f,Subgroup.subset_closure (by simp)⟩
  let G : Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=⟨g,Subgroup.subset_closure (by simp)⟩
  let A:=D.normalizedLift F
  let B:=D.normalizedLift G
  let P : HalfPlaneFuchsianGroup D.normalizedGroup:=
    ⟨fun k=>D.normalizedGroup_preserves_halfPlane k.val k.property,D.normalizedGroup_discrete⟩
  have hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr
      ⟨D.halfPlaneNormalizer,rfl⟩)).mp hf
  have hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation g D.halfPlaneNormalizer).mpr hg
  have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈D.normalizedGroup:=by
    rw [D.normalizedLift_spec]
    exact ⟨f,F.property,rfl⟩
  have hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈D.normalizedGroup:=by
    rw [D.normalizedLift_spec]
    exact ⟨g,G.property,rfl⟩
  have hntn : ¬IsMobiusTriangleGroup D.normalizedGroup:=fun h=>
    hnt (isMobiusTriangleGroup_of_conjugate _ D.halfPlaneNormalizer h)
  have horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=orderOf g:=by
    rw [D.normalizedLift_spec]
    exact (MulAut.conj D.halfPlaneNormalizer).orderOf_eq g
  have hb:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nontriangle_parabolic_elliptic_order_bound P hntn A B hA hB hAH hBH
    (by rwa [horder])
  rw [horder] at hb
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM_eq_native]
  exact hb

/-- The printed order-dependent ratio is at least its universal order-two value. -/
theorem parabolic_elliptic_nontriangle_order_constant_lower (q : ℕ) (hq : 2≤q) :
    1/Real.sqrt 3≤Real.sqrt ((1+Real.cos (Real.pi/(q:ℝ)))/(3-Real.cos (Real.pi/(q:ℝ)))) := by
  have hc : 0≤Real.cos (Real.pi/(q:ℝ)):=sharpEllipticCos_nonneg q hq
  have hd : 0<3-Real.cos (Real.pi/(q:ℝ)):=by linarith [Real.cos_le_one (Real.pi/(q:ℝ))]
  have h : (1:ℝ)/3≤(1+Real.cos (Real.pi/(q:ℝ)))/(3-Real.cos (Real.pi/(q:ℝ))):=by
    apply (div_le_div_iff₀ (by norm_num) hd).mpr
    linarith
  have h':=Real.sqrt_le_sqrt h
  have he : Real.sqrt ((1:ℝ)/3)=1/Real.sqrt 3:=by norm_num
  rwa [he] at h'

/-- The entire nontriangle inequality chain, including the original order-two case. -/
theorem parabolic_elliptic_nontriangle_order_displacement_bound_and_uniform_bound
    (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) (hg :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hnt : ¬IsMobiusTriangleGroup (Subgroup.closure ({f,g}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hq : 2≤orderOf g) :
    1/Real.sqrt 3≤Real.sqrt ((1+Real.cos (Real.pi/orderOf g))/(3-Real.cos (Real.pi/orderOf g))) ∧
    Real.sqrt ((1+Real.cos (Real.pi/orderOf g))/(3-Real.cos (Real.pi/orderOf g)))≤
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D ⟨f,Subgroup.subset_closure (by simp)⟩
        ⟨g,Subgroup.subset_closure (by simp)⟩ := by
  refine ⟨parabolic_elliptic_nontriangle_order_constant_lower _ hq,?_⟩
  by_cases he : orderOf g=2
  · have h:=fuchsian_nontriangle_parabolic_elliptic_displacementM_sqrt_three f g D hf hg hne hnt
    simpa [he] using h
  · exact fuchsian_nontriangle_parabolic_elliptic_order_displacementM_bound f g D hf hg hnt (by omega)

end LowDimensionalTopology.Geometry.Fuchsian
