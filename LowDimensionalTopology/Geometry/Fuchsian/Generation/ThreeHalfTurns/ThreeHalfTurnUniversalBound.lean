/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.ThreeHalfTurnCovering
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.ThreeHalfTurnSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.FuchsianDisplacementInvariants
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Trace.HalfTurnTraces
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalRegions
public import LowDimensionalTopology.Geometry.Fuchsian.Elementary.DihedralNearestOrbits
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.CollinearHalfTurns
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc ENNReal Pointwise MatrixGroups OnePoint ComplexConjugate

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane MatrixGroups OnePoint
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

/-- A genuine triangle cannot acquire a third imaginary-axis vertex when its
first two vertices have been put on that axis by one actual real isometry. -/
theorem halfturn_axis_third_real_ne_zero (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ha : (q • T.a).re=0) (hb : (q • T.b).re=0) : (q • T.c).re≠0 := by
  intro hc
  obtain ⟨L,hL⟩:=(isometry_smul ℍ q⁻¹).halfPlane_image_hLine (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0)
  apply T.noncollinear
  refine ⟨L,?_,?_,?_⟩
  · rw [←hL]
    exact ⟨q • T.a,ha,inv_smul_smul q T.a⟩
  · rw [←hL]
    exact ⟨q • T.b,hb,inv_smul_smul q T.b⟩
  · rw [←hL]
    exact ⟨q • T.c,hc,inv_smul_smul q T.c⟩

/-- An actual determinant-one transformation puts the first two true vertices
on the imaginary axis and the third strictly to its right. -/
theorem halfturn_triangle_right_axis_normalizer (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    ∃q:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (q • T.a).re=0 ∧ (q • T.b).re=0 ∧ 0<(q • T.c).re := by
  obtain ⟨q,ha,hb,_⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_sl2_ordered_imaginary T.a T.b T.a_ne_b
  have hc:=halfturn_axis_third_real_ne_zero T q ha hb
  rcases lt_or_gt_of_ne hc with hneg|hpos
  · refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalNormalizer 0*q,?_,?_,?_⟩
    · rw [mul_smul]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalNormalizer_zero_re ha
    · rw [mul_smul]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalNormalizer_zero_re hb
    · rw [mul_smul,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalNormalizer_re]
      exact div_pos (by linarith only [hneg]) (by positivity)
  · exact ⟨q,ha,hb,hpos⟩

/-- The three actual centers admit the radial half-turn quadrilateral
normalization. The first two labels may be interchanged, but the third is the
same original center under the same actual determinant-one map. -/
theorem halfturn_triangle_radial_axis_centers (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    ∃(q:Matrix.SpecialLinearGroup (Fin 2) ℝ)(u v:ℝ)(hu:0<u)(hv:0<v)(w:ℍ),
      u<v ∧ 0<w.re ∧ w.re^2+w.im^2=(v/u)^2 ∧ q • T.c=w ∧
      ((q • T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 u hu ∧ q • T.b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 v hv) ∨
        (q • T.b=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 u hu ∧ q • T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 v hv)) := by
  obtain ⟨q₀,ha,hb,hc⟩:=halfturn_triangle_right_axis_normalizer T
  let a:ℝ:=(q₀ • T.a).im
  let b:ℝ:=(q₀ • T.b).im
  have ha0:0<a:=(q₀ • T.a).im_pos
  have hb0:0<b:=(q₀ • T.b).im_pos
  have hab:a≠b:=by
    intro he
    apply T.a_ne_b
    apply MulAction.injective q₀
    exact UpperHalfPlane.ext_re_im (ha.trans hb.symm) he
  let u₀:=min a b
  let v₀:=max a b
  have hu₀:0<u₀:=lt_min ha0 hb0
  have hv₀:0<v₀:=lt_of_lt_of_le ha0 (le_max_left _ _)
  have huv₀:u₀<v₀:=min_lt_max.mpr hab
  let k:=v₀/u₀
  have hk:0<k:=div_pos hv₀ hu₀
  let ρ:=k/‖((q₀ • T.c:ℍ):ℂ)‖
  have hρ:0<ρ:=div_pos hk (norm_pos_iff.mpr (q₀ • T.c).ne_zero)
  let d:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL ρ hρ
  let q:=d*q₀
  let u:=ρ*u₀
  let v:=ρ*v₀
  let w:ℍ:=d • (q₀ • T.c)
  have hu:0<u:=mul_pos hρ hu₀
  have hv:0<v:=mul_pos hρ hv₀
  have hratio:v/u=k:=by
    dsimp only [v,u,k]
    exact mul_div_mul_left _ _ hρ.ne'
  have hnorm:‖(w:ℂ)‖=k:=by
    dsimp only [w,d]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ]
    exact div_mul_cancel₀ _ (norm_pos_iff.mpr (q₀ • T.c).ne_zero).ne'
  have hpoint (z:ℍ) (hz:(q₀ • z).re=0) :
      q • z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (ρ*(q₀ • z).im) (mul_pos hρ (q₀ • z).im_pos) := by
    apply UpperHalfPlane.ext_re_im
    · change (q • z).re=0
      dsimp only [q,d]
      rw [mul_smul,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,hz,mul_zero]
    · change (q • z).im=ρ*(q₀ • z).im
      dsimp only [q,d]
      rw [mul_smul,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_im]
  refine ⟨q,u,v,hu,hv,w,mul_lt_mul_of_pos_left huv₀ hρ,?_,?_,mul_smul d q₀ T.c,?_⟩
  · change 0<(d • (q₀ • T.c)).re
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re]
    exact mul_pos hρ hc
  · rw [hratio,←hnorm,Complex.sq_norm,Complex.normSq_apply]
    simp only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,pow_two]
  · rcases lt_or_gt_of_ne hab with hab|hba
    · left
      constructor
      · simpa only [u,u₀,min_eq_left hab.le,a] using hpoint T.a ha
      · simpa only [v,v₀,max_eq_right hab.le,b] using hpoint T.b hb
    · right
      constructor
      · simpa only [u,u₀,min_eq_right hba.le,b] using hpoint T.b hb
      · simpa only [v,v₀,max_eq_left hba.le,a] using hpoint T.a ha

/-- The actual three-generator subgroup conjugates with its three actual
projective representatives; signs of determinant-one lifts are immaterial. -/
theorem halfturn_axis_conjugate_generated_group
    (q A B C U V W : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius U)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius V)
    (hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*C*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set Mobius.complexMobiusGroup))=
        Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius U,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius V,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W}:Set Mobius.complexMobiusGroup) := by
  change (Subgroup.closure _).map (MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).toMonoidHom=_
  rw [MonoidHom.map_closure,Set.image_insert_eq,Set.image_insert_eq,Set.image_singleton]
  change Subgroup.closure
    {_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹}=_
  simp only [map_mul,map_inv] at hA hB hC
  rw [hA,hB,hC]

/-- Absolute triple trace is preserved by the same genuine simultaneous
projective conjugation, without choosing signs for individual real lifts. -/
theorem halfturn_axis_conjugated_triple_abs_trace
    (q A B C U V W : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius U)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius V)
    (hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*C*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W) :
    |Matrix.trace (U*V*W).val|=|Matrix.trace (A*B*C).val| := by
  have he:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (U*V*W)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*(A*B*C)*q⁻¹):=by
    simp only [map_mul,map_inv] at hA hB hC ⊢
    rw [←hA,←hB,←hC]
    group
  calc
    _=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (U*V*W)):=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_traceAbs _).symm
    _=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*(A*B*C)*q⁻¹)):=congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs he
    _=_:=by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_traceAbs,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]

/-- Every genuine three-center half-turn triangle has one actual real
normalizer giving the radial axis model of its same original generated group.
Its actual absolute triple trace remains exactly twice the original invariant. -/
theorem three_halfturn_actual_radial_axis_normalization
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt A T.a)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt B T.b)
    (hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt C T.c) :
    ∃(q:Matrix.SpecialLinearGroup (Fin 2) ℝ)(u v:ℝ)(hu:0<u)(hv:0<v)(w:ℍ),
      u<v ∧ 0<w.re ∧ w.re^2+w.im^2=(v/u)^2 ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
        (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set Mobius.complexMobiusGroup))=
          Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu),
            _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)}:Set Mobius.complexMobiusGroup) ∧
      |Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val|=
        2*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T := by
  obtain ⟨q,u,v,hu,hv,w,huv,hwr,hwn,hcw,hpair⟩:=halfturn_triangle_radial_axis_centers T
  have hCq:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*C*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w):=by
    have hc:=hC.conjugate q
    rw [hcw] at hc
    exact hc.unique (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at w)
  refine ⟨q,u,v,hu,hv,w,huv,hwr,hwn,?_⟩
  rcases hpair with ⟨ha,hb⟩|⟨hb,ha⟩
  · have hAq:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu):=by
      have hc:=hA.conjugate q
      rw [ha] at hc
      exact hc.unique (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at u hu)
    have hBq:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv):=by
      have hc:=hB.conjugate q
      rw [hb] at hc
      exact hc.unique (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at v hv)
    constructor
    · exact halfturn_axis_conjugate_generated_group q A B C _ _ _ hAq hBq hCq
    · exact (halfturn_axis_conjugated_triple_abs_trace q A B C _ _ _ hAq hBq hCq).trans
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurn_triple_abs_trace T A B C hA hB hC)
  · have hAq:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv):=by
      have hc:=hA.conjugate q
      rw [ha] at hc
      exact hc.unique (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at v hv)
    have hBq:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu):=by
      have hc:=hB.conjugate q
      rw [hb] at hc
      exact hc.unique (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at u hu)
    constructor
    · have hset:({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set Mobius.complexMobiusGroup)=
          {_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:=Set.insert_comm _ _ _
      rw [hset]
      exact halfturn_axis_conjugate_generated_group q B A C _ _ _ hBq hAq hCq
    · exact (halfturn_axis_conjugated_triple_abs_trace q B A C _ _ _ hBq hAq hCq).trans
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurn_six_product_orders_abs_trace_eq_twice_triangleInvariant T A B C hA hB hC).2.2.2.2.2

end LowDimensionalTopology.Geometry.Fuchsian


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane MatrixGroups OnePoint
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

/-- Common positive scaling of two actual axis centers preserves the literal
ordered determinant-one two-half-turn product. -/
theorem axisHalfTurn_scaled_pair_product (u v r:ℝ) (hu:0<u) (hv:0<v) (hr:0<r) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*r) (mul_pos hu hr)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (v*r) (mul_pos hv hr)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL]
    <;> field_simp [hu.ne',hv.ne',hr.ne']


/-- The actual ordered pair product is the genuine positive dilation by the
square of the true height ratio. -/
theorem axisHalfTurn_pair_positive_dilation (u v:ℝ) (hu:0<u) (hv:0<v) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu)=
      fuchsianPositiveDilation ((v/u)^2) (sq_pos_of_pos (div_pos hv hu)) := by
  rw [←map_mul,fuchsianPositiveDilation,
    ←realSLMobius_verticalDilation ((v/u)^2) (sq_pos_of_pos (div_pos hv hu))]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_ext_action
  intro z
  apply UpperHalfPlane.ext
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurns_product_coe,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe]
  push_cast
  rfl

/-- A genuine integer dilation power followed by a true half-turn is precisely
the half-turn at the correspondingly shifted actual axis center. -/
theorem axisHalfTurn_positive_dilation_shift (a t:ℝ) (ha:0<a) (ht:0<t) (n:ℤ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (a*t^n) (mul_pos ha (zpow_pos ht n)))=
      fuchsianPositiveDilation (t^2) (sq_pos_of_pos ht)^n*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL a ha) := by
  have he:(t^2)^n=(t^n)^2:=by rw [pow_two,mul_zpow,pow_two]
  calc
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL ((t^2)^n) (zpow_pos (sq_pos_of_pos ht) n)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL a ha):=by
      apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_ext_action
      intro z
      apply UpperHalfPlane.ext
      rw [mul_smul, _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_coe,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_coe, he]
      push_cast
      ring
    _=fuchsianPositiveDilation ((t^2)^n) (zpow_pos (sq_pos_of_pos ht) n)*
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL a ha):=by
      rw [map_mul,realSLMobius_verticalDilation]
      rfl
    _=_:=by rw [fuchsianPositiveDilation_zpow]

/-- Consecutive actual axis half-turn generators can be shifted by any integer
half-period without changing their entire generated pair subgroup. -/
theorem axisHalfTurn_shifted_pair_group (u v:ℝ) (hu:0<u) (hv:0<v) (n:ℤ) :
    Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*(v/u)^n) (mul_pos hu (zpow_pos (div_pos hv hu) n))),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (v*(v/u)^n) (mul_pos hv (zpow_pos (div_pos hv hu) n)))}:
          Set Mobius.complexMobiusGroup)=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)}:
        Set Mobius.complexMobiusGroup) := by
  let t:=v/u
  let r:=t^n
  have ht:0<t:=div_pos hv hu
  have hr:0<r:=zpow_pos ht n
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu)
  let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)
  let F':=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*r) (mul_pos hu hr))
  let G':=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (v*r) (mul_pos hv hr))
  let D:=G*F
  have hD:D=fuchsianPositiveDilation (t^2) (sq_pos_of_pos ht):=
    axisHalfTurn_pair_positive_dilation u v hu hv
  have hF':F'=D^n*F:=by
    rw [hD]
    exact axisHalfTurn_positive_dilation_shift u t hu ht n
  have hG':G'=D^n*G:=by
    rw [hD]
    exact axisHalfTurn_positive_dilation_shift v t hv ht n
  have hD':D=G'*F':=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (v*r) (mul_pos hv hr))*
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*r) (mul_pos hu hr))
    rw [←map_mul,←map_mul,axisHalfTurn_scaled_pair_product v u r hv hu hr]
  change Subgroup.closure ({F',G'}:Set Mobius.complexMobiusGroup)=Subgroup.closure ({F,G}:Set Mobius.complexMobiusGroup)
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro f hf
    have hF:F∈Subgroup.closure ({F,G}:Set Mobius.complexMobiusGroup):=Subgroup.subset_closure (by simp)
    have hG:G∈Subgroup.closure ({F,G}:Set Mobius.complexMobiusGroup):=Subgroup.subset_closure (by simp)
    have hd:D∈Subgroup.closure ({F,G}:Set Mobius.complexMobiusGroup):=Subgroup.mul_mem _ hG hF
    rcases hf with rfl|rfl
    · rw [hF']
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hd n) hF
    · rw [hG']
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hd n) hG
  · apply (Subgroup.closure_le _).mpr
    intro f hf
    have hF:F'∈Subgroup.closure ({F',G'}:Set Mobius.complexMobiusGroup):=Subgroup.subset_closure (by simp)
    have hG:G'∈Subgroup.closure ({F',G'}:Set Mobius.complexMobiusGroup):=Subgroup.subset_closure (by simp)
    have hd:D∈Subgroup.closure ({F',G'}:Set Mobius.complexMobiusGroup):=by
      rw [hD']
      exact Subgroup.mul_mem _ hG hF
    have hbackF:F=D^(-n)*F':=by rw [hF',←mul_assoc,←zpow_add];simp
    have hbackG:G=D^(-n)*G':=by rw [hG',←mul_assoc,←zpow_add];simp
    rcases hf with rfl|rfl
    · rw [hbackF]
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hd (-n)) hF
    · rw [hbackG]
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hd (-n)) hG

/-- A true positive radial center has an actual integer half-period translate
in the first half-open multiplicative period. -/
theorem positive_axis_halfperiod_representative (u t:ℝ) (hu:0<u) (ht:1<t) :
    ∃n:ℤ,1≤u*t^n ∧ u*t^n<t := by
  let n:ℤ:=-⌊Real.log u/Real.log t⌋
  have htp:0<t:=zero_lt_one.trans ht
  have htl:0<Real.log t:=Real.log_pos ht
  have hp:0<u*t^n:=mul_pos hu (zpow_pos htp n)
  have he:Real.log (u*t^n)=Real.log u+(n:ℝ)*Real.log t:=by
    rw [Real.log_mul hu.ne' (zpow_pos htp n).ne',Real.log_zpow]
  have h0:=Int.sub_floor_div_mul_nonneg (Real.log u) htl
  have h1:=Int.sub_floor_div_mul_lt (Real.log u) htl
  have hl:0≤Real.log (u*t^n) ∧ Real.log (u*t^n)<Real.log t:=by
    rw [he]
    dsimp [n]
    push_cast
    constructor <;> linarith
  exact ⟨n,(Real.log_nonneg_iff hp).mp hl.1,(Real.log_lt_log_iff hp htp).mp hl.2⟩

/-- Keeping the genuine third half-turn fixed, the same integer shift
preserves the whole actual three-generator subgroup. -/
theorem axisHalfTurn_shifted_triple_group (u v:ℝ) (hu:0<u) (hv:0<v) (n:ℤ) (w:ℍ) :
    Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*(v/u)^n) (mul_pos hu (zpow_pos (div_pos hv hu) n))),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (v*(v/u)^n) (mul_pos hv (zpow_pos (div_pos hv hu) n))),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)}:Set Mobius.complexMobiusGroup)=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)}:Set Mobius.complexMobiusGroup) := by
  have hset (a b c:Mobius.complexMobiusGroup):({a,b,c}:Set Mobius.complexMobiusGroup)={a,b}∪{c}:=by
    ext x
    simp only [mem_insert_iff,mem_singleton_iff,mem_union]
    exact or_assoc.symm
  rw [hset,hset,Subgroup.closure_union,Subgroup.closure_union,axisHalfTurn_shifted_pair_group]

/-- The determinant-one triple product trace itself is unchanged under the
same actual pair replacement; the third center remains the original point. -/
theorem axisHalfTurn_shifted_triple_trace (u v:ℝ) (hu:0<u) (hv:0<v) (n:ℤ) (w:ℍ) :
    Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*(v/u)^n) (mul_pos hu (zpow_pos (div_pos hv hu) n))*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (v*(v/u)^n) (mul_pos hv (zpow_pos (div_pos hv hu) n))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val=
      Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val := by
  rw [axisHalfTurn_scaled_pair_product u v ((v/u)^n) hu hv (zpow_pos (div_pos hv hu) n)]

/-- The actual first axis center can be moved into one half-period by a
proved integer Nielsen replacement. The third center and the whole actual
generated group stay fixed, and the literal triple trace is unchanged. -/
theorem three_halfturn_axis_halfperiod_reduction (u v:ℝ) (hu:0<u) (huv:u<v) (w:ℍ) :
    ∃(n:ℤ)(u' v':ℝ)(hu':0<u')(hv':0<v'),
      u'=u*(v/u)^n ∧ v'=u'*(v/u) ∧ 1≤u' ∧ u'<v/u ∧ u'<v' ∧
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u' hu'),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v' hv'),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)}:Set Mobius.complexMobiusGroup)=
        Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v (hu.trans huv)),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)}:
            Set Mobius.complexMobiusGroup) ∧
      Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u' hu'*_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v' hv'*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val=
        Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v (hu.trans huv)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu)∈Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u' hu'),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v' hv')}:Set Mobius.complexMobiusGroup) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v (hu.trans huv))∈Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u' hu'),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v' hv')}:Set Mobius.complexMobiusGroup) := by
  let t:=v/u
  have ht:1<t:=(one_lt_div hu).mpr huv
  have htp:0<t:=zero_lt_one.trans ht
  have hv:0<v:=hu.trans huv
  obtain ⟨n,hn0,hn1⟩:=positive_axis_halfperiod_representative u t hu ht
  let r:=t^n
  have hr:0<r:=zpow_pos htp n
  let u':=u*r
  let v':=v*r
  have hu':0<u':=mul_pos hu hr
  have hv':0<v':=mul_pos hv hr
  have hratio:v'=u'*t:=by
    dsimp only [v',u',t]
    field_simp
  have horder:u'<v':=by
    rw [hratio]
    simpa only [mul_one] using mul_lt_mul_of_pos_left ht hu'
  refine ⟨n,u',v',hu',hv',rfl,hratio,hn0,hn1,horder,?_,?_,?_,?_⟩
  · exact axisHalfTurn_shifted_triple_group u v hu hv n w
  · exact axisHalfTurn_shifted_triple_trace u v hu hv n w
  · rw [axisHalfTurn_shifted_pair_group u v hu hv n]
    exact Subgroup.subset_closure (by simp)
  · rw [axisHalfTurn_shifted_pair_group u v hu hv n]
    exact Subgroup.subset_closure (by simp)

end LowDimensionalTopology.Geometry.Fuchsian


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
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

/-- An actual order-two real matrix action has its actual unique elliptic center. -/
theorem threeHalfTurn_order_two_center (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ho : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=2) : ∃p : ℍ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt A p := by
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1:=by
    intro he
    rw [he,orderOf_one] at ho
    norm_num at ho
  have ht : (Matrix.trace A.val)^2<4:=by
    rw [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_order_two_iff_trace_zero A hn).mp ho]
    norm_num
  exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ht,ho,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A ht _).mpr rfl⟩

/-- Three actual half-turns with one common center generate an elementary group. -/
theorem threeHalfTurn_common_center_elementary
    (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p : ℍ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt A p)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt B p)
    (hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt C p) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup)) := by
  let G:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup)
  have hs : G≤MulAction.stabilizer Mobius.complexMobiusGroup ((p : ℂ) : Mobius.ExtendedComplex):=by
    apply (Subgroup.closure_le _).mpr
    rintro f (rfl|rfl|rfl)
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (p : ℂ)=(p : ℂ)
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,hA.2]
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val (p : ℂ)=(p : ℂ)
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,hB.2]
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C).val (p : ℂ)=(p : ℂ)
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,hC.2]
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isElementary_of_boundary_fixed G ((p : ℂ) : Mobius.ExtendedComplex) (fun g=>hs g.property)

/-- The original order-two and non-elementarity hypotheses construct the actual
three-center hyperbolic triangle, with the unchanged original ordered generators. -/
theorem threeHalfTurn_original_centers_triangle
    (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=2)
    (hB : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=2)
    (hC : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)=2)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup))) :
    ∃T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle,_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt A T.a ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt B T.b ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt C T.c := by
  obtain ⟨p,hp⟩:=threeHalfTurn_order_two_center A hA
  obtain ⟨q,hq⟩:=threeHalfTurn_order_two_center B hB
  obtain ⟨r,hr⟩:=threeHalfTurn_order_two_center C hC
  have hnc : ¬∃L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,p∈L.carrier ∧ q∈L.carrier ∧ r∈L.carrier:=by
    rintro ⟨L,hLp,hLq,hLr⟩
    by_cases hpq : p=q
    · subst q
      by_cases hpr : p=r
      · subst r
        exact hNE (threeHalfTurn_common_center_elementary A B C p hp hq hr)
      · have he:=collinear_halfTurns_elementary L p r p hpr hLp hLr hLp A C B hp hr hq
        exact hNE (by simpa only [Set.pair_comm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)] using he)
    · exact hNE (collinear_halfTurns_elementary L p q r hpq hLp hLq hLr A B C hp hq hr)
  exact ⟨⟨p,q,r,hnc⟩,hp,hq,hr⟩

end LowDimensionalTopology.Geometry.Fuchsian


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane MatrixGroups OnePoint
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

/-- Genuine conjugation and an actual integer Nielsen replacement put the same
three-half-turn group into its first radial half-period and preserve its true trace. -/
theorem threeHalfTurn_actual_halfperiod_model (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt A T.a)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt B T.b)
    (hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt C T.c)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup))) :
    ∃(u t : ℝ)(hu : 0<u)(ht : 1<t)(w : ℍ),1≤u ∧ u<t ∧ 0<w.re ∧
      w.re^2+w.im^2=t^2 ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans ht))),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)} : Set Mobius.complexMobiusGroup)) ∧
      |Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans ht))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val|=
        |Matrix.trace (A*B*C).val| := by
  obtain ⟨q,u,v,hu,hv,w,huv,hw,hn,hG,htr⟩:=
    three_halfturn_actual_radial_axis_normalization T A B C hA hB hC
  have ht : 1<v/u:=(one_lt_div hu).mpr huv
  let : DiscreteTopology (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup)):=hd
  have hdc:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
    (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup))
  change DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
    (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup))) at hdc
  rw [hG] at hdc
  obtain ⟨n,a,b,ha,hb,_hae,hbe,ha1,hat,_hab,hGrp,hTrace,_hFm,_hGm⟩:=
    three_halfturn_axis_halfperiod_reduction u v hu huv w
  subst b
  refine ⟨a,v/u,ha,ht,w,ha1,hat,hw,hn,?_,?_⟩
  · rw [hGrp]
    exact hdc
  · calc
      _=|Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val|:=
        congrArg abs hTrace
      _=2*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T:=htr
      _=|Matrix.trace (A*B*C).val|:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurn_triple_abs_trace T A B C hA hB hC).symm

/-- The true trace bound for every original three-center half-turn triangle.
Compact side geometry is derived from smallness of the actual trace. -/
theorem threeHalfTurn_triangle_trace_bound (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt A T.a)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt B T.b)
    (hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt C T.c)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup))) :
    2*Real.cos (3*Real.pi/7)≤|Matrix.trace (A*B*C).val| := by
  by_cases hbig : 2≤|Matrix.trace (A*B*C).val|
  · have htwo : 2*Real.cos (3*Real.pi/7)≤2:=by
      have hh:=mul_le_mul_of_nonneg_left (Real.cos_le_one (3*Real.pi/7)) (by norm_num : (0 : ℝ)≤2)
      simpa only [mul_one] using hh
    exact htwo.trans hbig
  obtain ⟨u,t,hu,ht,w,hu1,hut,hw,hn,hdisc,htrace⟩:=
    threeHalfTurn_actual_halfperiod_model T A B C hA hB hC hd
  have hsmall : |Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans ht))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val|<2:=by
    rw [htrace]
    exact lt_of_not_ge hbig
  rw [axisHalfTurns_point_triple_trace] at hsmall
  have hratio : (u*t)/u-u/(u*t)=t-1/t:=by
    field_simp
  rw [hratio] at hsmall
  have hscalar:=halfTurn_small_trace_compact_scalar t w.re w.im ht hw w.im_pos hn
    ((le_abs_self _).trans_lt hsmall)
  have hc : t^2+1<2*(t^2/w.re):=by
    have hh: t^2+1<(2*t^2)/w.re:=(lt_div_iff₀ hw).mpr hscalar
    simpa only [mul_div_assoc] using hh
  have hh:=halfTurnCanonical_compact_trace_bound u t hu1 hut w hw hn hc hdisc
  rwa [htrace] at hh

/-- The original order-two and non-elementarity hypotheses construct all centers
and every normalization needed for the real-matrix form of the sharp bound. -/
theorem threeHalfTurn_realSL_trace_bound (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=2)
    (hB : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=2)
    (hC : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)=2)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup)))
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup))) :
    2*Real.cos (3*Real.pi/7)≤|Matrix.trace (A*B*C).val| := by
  obtain ⟨T,hAt,hBt,hCt⟩:=threeHalfTurn_original_centers_triangle A B C hA hB hC hNE
  exact threeHalfTurn_triangle_trace_bound T A B C hAt hBt hCt hd

/-- The bound applies on every actual original invariant disc. Real lifts and
all conjugations are constructed from that disc, rather than supplied as hypotheses. -/
theorem threeHalfTurn_original_disc_trace_bound
    (f g h : Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g,h} : Set Mobius.complexMobiusGroup)))
    (hf : orderOf f=2) (hg : orderOf g=2) (hh : orderOf h=2)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g,h} : Set Mobius.complexMobiusGroup))) :
    2*Real.cos (3*Real.pi/7)≤_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h) := by
  let H:=Subgroup.closure ({f,g,h} : Set Mobius.complexMobiusGroup)
  let F : H:=⟨f,Subgroup.subset_closure (by simp)⟩
  let G : H:=⟨g,Subgroup.subset_closure (by simp)⟩
  let K : H:=⟨h,Subgroup.subset_closure (by simp)⟩
  let A:=D.normalizedLift F
  let B:=D.normalizedLift G
  let C:=D.normalizedLift K
  let q:=D.halfPlaneNormalizer
  have hA : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=2:=by
    rw [D.normalizedLift_spec]
    exact ((MulAut.conj q).orderOf_eq f).trans hf
  have hB : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=2:=by
    rw [D.normalizedLift_spec]
    exact ((MulAut.conj q).orderOf_eq g).trans hg
  have hC : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)=2:=by
    rw [D.normalizedLift_spec]
    exact ((MulAut.conj q).orderOf_eq h).trans hh
  have hgroup : D.normalizedGroup=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup):=by
    change (Subgroup.closure ({f,g,h} : Set Mobius.complexMobiusGroup)).map (MulAut.conj q).toMonoidHom=_
    rw [MonoidHom.map_closure,Set.image_insert_eq,Set.image_insert_eq,Set.image_singleton]
    change Subgroup.closure {q*f*q⁻¹,q*g*q⁻¹,q*h*q⁻¹}=_
    rw [←D.normalizedLift_spec F,←D.normalizedLift_spec G,←D.normalizedLift_spec K]
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup)):=by
    rw [←hgroup]
    exact D.normalizedGroup_discrete
  have hNE' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set Mobius.complexMobiusGroup)):=by
    rw [←hgroup]
    exact hNE.conjugation q
  have hbnd:=threeHalfTurn_realSL_trace_bound A B C hA hB hC hd hNE'
  have hprod : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B*C)=q*(f*g*h)*q⁻¹:=by
    dsimp only [A,B,C]
    rw [map_mul,map_mul,D.normalizedLift_spec,D.normalizedLift_spec,D.normalizedLift_spec]
    change (q*f*q⁻¹)*(q*g*q⁻¹)*(q*h*q⁻¹)=q*(f*g*h)*q⁻¹
    group
  have habs : |Matrix.trace (A*B*C).val|=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_traceAbs, hprod,
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs,
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_conjugation]
    rfl
  rwa [habs] at hbnd

/--
The universal original-disc bound together with genuine
attainment by the actual (2,3,7) example.
-/
theorem threeHalfTurn_universal_trace_bound_sharp :
    (∀f g h : Mobius.complexMobiusGroup,orderOf f=2→ orderOf g=2→ orderOf h=2→
      Nonempty (FuchsianDisc (Subgroup.closure ({f,g,h} : Set Mobius.complexMobiusGroup)))→
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g,h} : Set Mobius.complexMobiusGroup))→
      2*Real.cos (3*Real.pi/7)≤_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h)) ∧
    (∃f g h : Mobius.complexMobiusGroup,orderOf f=2 ∧ orderOf g=2 ∧ orderOf h=2 ∧
      Nonempty (FuchsianDisc (Subgroup.closure ({f,g,h} : Set Mobius.complexMobiusGroup))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g,h} : Set Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h)=2*Real.cos (3*Real.pi/7)) := by
  refine ⟨?_,exists_trace_attaining_three_halfturns⟩
  intro f g h hf hg hh hD hNE
  obtain ⟨D⟩:=hD
  exact threeHalfTurn_original_disc_trace_bound f g h D hf hg hh hNE

end LowDimensionalTopology.Geometry.Fuchsian
