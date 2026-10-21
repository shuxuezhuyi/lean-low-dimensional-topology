/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.ThreeHalfTurnSharpness
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticMinimizers
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.EllipticProducts
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Every actual elliptic element of exact order three has squared lift trace one. -/
theorem realSL_order_three_trace_sq (B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (horder:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=3) : (Matrix.trace B.val)^2=1 := by
  have hne:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1:=by intro h;rw [h,orderOf_one] at horder;omega
  have hfin:IsOfFinOrder (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=orderOf_pos_iff.mp (by rw [horder];omega)
  obtain ⟨r,m,hr,_hr2,hm0,hmr,_hcop,ht⟩:=realSL_finite_order_trace_cosine B hne hfin
  rw [horder] at hr
  subst r
  interval_cases m <;> norm_num at hm0 hmr
  · norm_num [Real.cos_pi_div_three] at ht ⊢
    exact ht
  · norm_num only [Nat.cast_ofNat] at ht
    have he:Real.pi*(2:ℝ)/3=Real.pi-Real.pi/3:=by ring
    rw [he,Real.cos_pi_sub,Real.cos_pi_div_three] at ht
    norm_num at ht ⊢
    exact ht

/-- The exact actual elliptic-pair infimum is determined by these genuine lift traces. -/
theorem elliptic_order_two_three_displacementM_square
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A)) (hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (htA:Matrix.trace A.val=0) (htB:(Matrix.trace B.val)^2=1)
    (c:ℝ) (hc:0≤c) (htAB:(Matrix.trace (A*B⁻¹).val)^2=4*c^2) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2=(4*c^2-3)/(8*c+7) := by
  let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let v:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  let θ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA/2
  let φ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB/2
  let s:=Real.sin θ
  let t:=Real.sin φ
  let D:=Real.cosh (dist u v)
  have hs:0<s:=Real.sin_pos_of_pos_of_lt_pi (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA).1
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA).2
  have htp:0<t:=Real.sin_pos_of_pos_of_lt_pi (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo B hB).1
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo B hB).2
  have hcos:Real.cos θ=0:=by
    have hh:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).2.2.2
    rw [htA] at hh
    change (0:ℝ)^2=4*(Real.cos θ)^2 at hh
    nlinarith only [hh,sq_nonneg (Real.cos θ)]
  have hs2:s^2=1:=by
    have hh:=Real.sin_sq_add_cos_sq θ
    rw [hcos] at hh
    simpa only [zero_pow (by norm_num:2≠0),add_zero] using hh
  have ht2:t^2=(3:ℝ)/4:=by
    have hh:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec B hB).2.2.2
    rw [htB] at hh
    change (1:ℝ)=4*(Real.cos φ)^2 at hh
    nlinarith only [hh,Real.sin_sq_add_cos_sq φ]
  have hsum:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_product_add_inverse A B
  rw [htA,zero_mul] at hsum
  have hsq:(Matrix.trace (A*B).val)^2=4*c^2:=by
    have he:Matrix.trace (A*B).val= -Matrix.trace (A*B⁻¹).val:=by linarith only [hsum]
    rw [he,neg_sq,htAB]
  have habs:|Matrix.trace (A*B).val|/2=c:=by
    nlinarith only [hsq,sq_abs (Matrix.trace (A*B).val),abs_nonneg (Matrix.trace (A*B).val),hc]
  have hprod:D*s*t=c:=by
    have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_abs_trace A B hA hB
    change |Matrix.trace (A*B).val|/2=|D*s*t-Real.cos θ*Real.cos φ| at hh
    have hp:0<D*s*t:=mul_pos (mul_pos (Real.cosh_pos _) hs) htp
    rw [hcos,zero_mul,sub_zero,abs_of_pos hp,habs] at hh
    exact hh.symm
  have hst:(s*t)^2=(3:ℝ)/4:=by rw [mul_pow,hs2,ht2,one_mul]
  have hnum:(s*t)^2*(D^2-1)=c^2-3/4:=by
    calc (s*t)^2*(D^2-1)=(D*s*t)^2-(s*t)^2:=by ring
         _=c^2-3/4:=by rw [hprod,hst]
  have hden:s^2+t^2+2*s*t*D=(7:ℝ)/4+2*c:=by
    rw [hs2,ht2]
    nlinarith only [hprod]
  have hm:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_pair_displacementM_square A B hA hB
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2=
    (s*t)^2*(D^2-1)/(s^2+t^2+2*s*t*D) at hm
  rw [hm,hnum,hden]
  field_simp
  ring

/-- Every genuine (2,3,7) conformal triangle group has actual order-two/order-three
elliptic generators attaining the exact source maximum-displacement constant. -/
theorem triangle_two_three_seven_displacementM_sharp (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hα:T.alpha=Real.pi/7) (hβ:T.beta=Real.pi/3) (hγ:T.gamma=Real.pi/2) :
    ∃A B:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        A)=2 ∧ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=3 ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∧
      Subgroup.closure ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B}:Set (ℍ≃ᵢℍ))=triangleConformalGroup T ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
        ({
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
        ({
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)=
        Real.sqrt ((4*(Real.cos (Real.pi/7))^2-3)/(8*Real.cos (Real.pi/7)+7)) := by
  obtain ⟨A,B,htA,horderA,horderB,_horderAB,hG,hd,hNE,htAB⟩:=
    triangle_two_three_seven_real_pair T hα hβ hγ
  have hneA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1:=by intro h;rw [h,orderOf_one] at horderA;omega
  have hneB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1:=by intro h;rw [h,orderOf_one] at horderB;omega
  have hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=_root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic _ hneA
    (orderOf_pos_iff.mp (by rw [horderA];omega))
  have hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=_root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic _ hneB
    (orderOf_pos_iff.mp (by rw [horderB];omega))
  have hc:0≤Real.cos (Real.pi/7):=(Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩).le
  have hM:=elliptic_order_two_three_displacementM_square A B hA hB htA
    (realSL_order_three_trace_sq B horderB) _ hc htAB
  refine ⟨A,B,horderA,horderB,hA,hB,hG,hd,hNE,?_⟩
  rw [←hM,Real.sqrt_sq_eq_abs,abs_of_nonneg (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _
    _)]

/--
Elliptic generators of the discrete non-elementary (2,3,7) triangle group
attain the sharp displacement constant.
-/
theorem exists_elliptic_two_three_seven_displacementM_sharp :
    ∃T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle,∃A B:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      T.alpha=Real.pi/7 ∧ T.beta=Real.pi/3 ∧ T.gamma=Real.pi/2 ∧
      orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        A)=2 ∧ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=3 ∧
      Subgroup.closure ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B}:Set (ℍ≃ᵢℍ))=triangleConformalGroup T ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
        ({
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
        ({
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)=
        Real.sqrt ((4*(Real.cos (Real.pi/7))^2-3)/(8*Real.cos (Real.pi/7)+7)) := by
  obtain ⟨U,ha,hb,hc⟩:=exists_finite_triangle_with_angles (Real.pi/7) (Real.pi/3) (Real.pi/2)
    (by positivity) (by positivity) (by positivity) (by linarith [Real.pi_pos])
  let T:=U.toClosedHTriangle
  have hα:T.alpha=Real.pi/7:=U.closed_angles.1.trans ha
  have hβ:T.beta=Real.pi/3:=U.closed_angles.2.1.trans hb
  have hγ:T.gamma=Real.pi/2:=U.closed_angles.2.2.trans hc
  obtain ⟨A,B,hA,hB,_hEA,_hEB,hG,hd,hNE,hM⟩:=triangle_two_three_seven_displacementM_sharp T hα hβ hγ
  exact ⟨T,A,B,hα,hβ,hγ,hA,hB,hG,hd,hNE,hM⟩

end LowDimensionalTopology.Geometry.Fuchsian
