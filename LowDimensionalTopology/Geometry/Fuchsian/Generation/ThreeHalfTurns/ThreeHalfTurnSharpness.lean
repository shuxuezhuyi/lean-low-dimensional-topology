/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.ThreeHalfTurnTriangleGroups
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.OneParabolicUnitNormalForms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
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

theorem realSL_cube_trace (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (A^3).val=(Matrix.trace A.val)^3-3*Matrix.trace A.val := by
  have hd:A 0 0*A 1 1-A 0 1*A 1 0=1:=by
    simpa only [Matrix.det_fin_two] using A.det_coe
  rw [show A^3=A*A*A by simp only [pow_succ,pow_zero,one_mul]]
  norm_num [Matrix.trace_fin_two,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  linear_combination -3*(A 0 0+A 1 1)*hd

theorem realSL_cube_squared_trace_cosine (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (θ : ℝ)
    (ht:(Matrix.trace A.val)^2=4*(Real.cos θ)^2) :
    (Matrix.trace (A^3).val)^2=4*(Real.cos (3*θ))^2 := by
  rw [realSL_cube_trace]
  have he:=Real.cos_three_mul θ
  calc
    ((Matrix.trace A.val)^3-3*Matrix.trace A.val)^2=
      (Matrix.trace A.val)^2*((Matrix.trace A.val)^2-3)^2:=by ring
    _=4*(Real.cos θ)^2*(4*(Real.cos θ)^2-3)^2:=by rw [ht]
    _=4*(Real.cos (3*θ))^2:=by rw [he];ring

theorem conjugate_triple_product_of_cube_one {G : Type*} [Group G] (x r : G) (hr:r^3=1) :
    x*(r⁻¹*x*r)*(r*x*r⁻¹)=(x*r⁻¹)^3 := by
  have hr2:r*r=r⁻¹:=by
    apply eq_inv_iff_mul_eq_one.mpr
    calc (r*r)*r=r^3:=by simp only [pow_succ,pow_zero,one_mul,mul_assoc]
         _=1:=hr
  calc x*(r⁻¹*x*r)*(r*x*r⁻¹)=x*r⁻¹*x*(r*r)*x*r⁻¹:=by group
       _=(x*r⁻¹)^3:=by rw [hr2];simp only [pow_succ,pow_zero,one_mul,mul_assoc]

theorem realSL_three_conjugates_traceAbs (X R : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hR:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)=3) (θ:ℝ)
    (ht:(Matrix.trace (X*R⁻¹).val)^2=4*(Real.cos θ)^2) (hc:0≤Real.cos (3*θ)) :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (R⁻¹*X*R)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (R*X*R⁻¹))=
      2*Real.cos (3*θ) := by
  have hr:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)^3=1:=by simpa only [hR] using pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)
  have he:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (R⁻¹*X*R)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (R*X*R⁻¹)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius ((X*R⁻¹)^3):=by
    simp only [map_mul,map_inv,map_pow]
    exact conjugate_triple_product_of_cube_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R) hr
  rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_traceAbs]
  have ht3:=realSL_cube_squared_trace_cosine (X*R⁻¹) θ ht
  apply (sq_eq_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) hc)).mp
  rw [sq_abs]
  nlinarith only [ht3]

theorem triangle_two_three_seven_real_pair (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hα:T.alpha=Real.pi/7) (hβ:T.beta=Real.pi/3) (hγ:T.gamma=Real.pi/2) :
    ∃X R:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      Matrix.trace X.val=0 ∧ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X)=2 ∧ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)=3 ∧
      orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (X*R⁻¹))=7 ∧
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R}:Set (ℍ≃ᵢℍ))=triangleConformalGroup T ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R}:Set Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R}:Set Mobius.complexMobiusGroup)) ∧
      (Matrix.trace (X*R⁻¹).val)^2=4*(Real.cos (Real.pi/7))^2 := by
  let X:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB
  let R:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineC
  let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineB T.sideLineC
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB
  let c:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC
  have hxN:orderOf (a*b)=2:=triangle_first_generator_order_of_integral_angle T 2 (by omega) hγ
  have hrN:orderOf (a*c)=3:=triangle_second_alternative_generator_order T 3 (by omega) hβ
  have hx:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X)=2:=by
    rw [realSLMobius_order_eq_native]
    rw [show _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X=a*b from (reflectionProductSL_native _ _).symm]
    exact hxN
  have hr:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)=3:=by
    rw [realSLMobius_order_eq_native]
    rw [show _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R=a*c from (reflectionProductSL_native _ _).symm]
    exact hrN
  have hxn:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X≠1:=by intro h;rw [h,orderOf_one] at hx;omega
  have htX:Matrix.trace X.val=0:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_order_two_iff_trace_zero X hxn).mp hx
  have hxi:(a*b)⁻¹=a*b:=by
    apply inv_eq_of_mul_eq_one_right
    have h:=pow_orderOf_eq_one (a*b)
    simpa only [hxN,pow_two] using h
  have hbi:b⁻¹=b:=halfPlaneLineReflectionIsometry_inv _
  have hprod:(a*b)*(a*c)=b*c:=by
    calc (a*b)*(a*c)=(a*b)⁻¹*(a*c):=by rw [hxi]
         _=b*c:=by rw [mul_inv_rev,hbi];group
  have hnative:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (X*R)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (X*R)=_
    rw [map_mul]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W
    rw [show _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X=a*b from (reflectionProductSL_native _ _).symm,
      show _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R=a*c from (reflectionProductSL_native _ _).symm,
      show _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W=b*c from (reflectionProductSL_native _ _).symm,hprod]
  have hmob:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (X*R)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W:=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_ext_action _ _ (fun z=>congrArg (fun F:ℍ≃ᵢℍ=>F z) hnative)
  have hsq:(Matrix.trace (X*R).val)^2=(Matrix.trace W.val)^2:=by
    have h:=congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace hmob
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace] at h
    exact Complex.ofReal_injective h
  have hθ:T.cycle.gamma=Real.pi/7:=(closedHTriangle_cycle_angles T).2.2.trans hα
  have htW:(Matrix.trace W.val)^2=4*(Real.cos (Real.pi/7))^2:=by
    have h:=triangle_first_generator_trace T.cycle
    change (Matrix.trace W.val)^2=4*(Real.cos T.cycle.gamma)^2 at h
    rwa [hθ] at h
  have htU:(Matrix.trace (X*R⁻¹).val)^2=4*(Real.cos (Real.pi/7))^2:=by
    have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_product_add_inverse X R
    rw [htX,zero_mul] at h
    have he:Matrix.trace (X*R⁻¹).val= -Matrix.trace (X*R).val:=by linarith only [h]
    rw [he,neg_sq,hsq]
    exact htW
  have hs:0<Real.sin (Real.pi/7):=Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hUn:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (X*R⁻¹)≠1:=by
    intro h
    have he:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_sq_of_projection_one (X*R⁻¹) h
    nlinarith [he,htU,Real.sin_sq_add_cos_sq (Real.pi/7)]
  have hu:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (X*R⁻¹))=7:=
    realSL_order_of_reciprocal_cosine_trace (X*R⁻¹) hUn 7 (by omega) htU
  have hN:Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R}:Set (ℍ≃ᵢℍ))=triangleConformalGroup T:=by
    dsimp only [X,R]
    rw [←reflectionProductSL_native,←reflectionProductSL_native]
    exact (triangle_alternative_generators T).symm
  have hConf:Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R}:Set (ℍ≃ᵢℍ))≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup:=by
    rw [hN]
    exact inf_le_right
  have hdiscT:DiscreteTopology (triangleConformalGroup T):=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_integral_angles T (Or.inr ⟨7,by omega,hα⟩)
      (Or.inr ⟨3,by omega,hβ⟩) (Or.inr ⟨2,by omega,hγ⟩)
  let : DiscreteTopology (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R}:Set (ℍ≃ᵢℍ))):=by rwa [hN]
  have P:=nativeConformalSubgroup_halfPlaneData _ hConf
  have hG:=native_matrix_pair_mobius_image X R hConf
  have hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R}:Set Mobius.complexMobiusGroup)):=by
    have h:=P.discrete
    rwa [hG] at h
  have hNE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R}:Set Mobius.complexMobiusGroup)):=by
    apply fuchsian_orders_two_three_seven_nonElementary _ (realSL_pair_halfPlaneData X R hd).asFuchsianDisc
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R) (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hx hr
    simpa only [map_mul,map_inv] using hu
  exact ⟨X,R,htX,hx,hr,hu,hN,hd,hNE,htU⟩

theorem triangle_two_three_seven_trace_attaining_halfturns
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hα:T.alpha=Real.pi/7) (hβ:T.beta=Real.pi/3) (hγ:T.gamma=Real.pi/2) :
    ∃X Y Z:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X)=2 ∧ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y)=2 ∧ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z)=2 ∧
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry Y,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry Z}:Set (ℍ≃ᵢℍ))=triangleConformalGroup T ∧
      Nonempty (FuchsianDisc (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z}:Set Mobius.complexMobiusGroup))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z}:Set Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z)=2*Real.cos (3*Real.pi/7) := by
  obtain ⟨X,R,_htX,hx,hr,hu,hN,hd,hNE,htU⟩:=triangle_two_three_seven_real_pair T hα hβ hγ
  let Y:=R⁻¹*X*R
  let Z:=R*X*R⁻¹
  have hr3:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)^3=1:=by simpa only [hr] using pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)
  have hu7:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)⁻¹)^7=1:=by
    have h:=pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (X*R⁻¹))
    rw [hu] at h
    simpa only [map_mul,map_inv] using h
  have hG:Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z}:Set Mobius.complexMobiusGroup)=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R}:Set Mobius.complexMobiusGroup):=by
    dsimp only [Y,Z]
    simp only [map_mul,map_inv]
    exact three_conjugate_halfturns_seven_product (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R) hr3 hu7
  have hy:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y)=2:=by
    dsimp only [Y]
    simp only [map_mul,map_inv]
    have h:orderOf ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X*((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)⁻¹)⁻¹)=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X):=
      (MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)⁻¹).orderOf_eq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X)
    simpa only [inv_inv,hx] using h
  have hz:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z)=2:=by
    dsimp only [Z]
    simp only [map_mul,map_inv]
    exact ((MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)).orderOf_eq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X)).trans hx
  have hrN:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R)=3:=by rwa [←realSLMobius_order_eq_native]
  have huN:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (X*R⁻¹))=7:=by rwa [←realSLMobius_order_eq_native]
  have hrN3:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R)^3=1:=by simpa only [hrN] using pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R)
  have huN7:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R)⁻¹)^7=1:=by
    have h:=pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (X*R⁻¹))
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (X*R⁻¹))^orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (X*R⁻¹))=1 at h
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom X*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom R)⁻¹)^7=1
    simpa only [huN,map_mul,map_inv] using h
  have hNative:Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry Y,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry Z}:Set (ℍ≃ᵢℍ))=triangleConformalGroup T:=by
    change Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom X,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (R⁻¹*X*R),_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (R*X*R⁻¹)}:Set (ℍ≃ᵢℍ))=_
    simp only [map_mul,map_inv]
    exact (three_conjugate_halfturns_seven_product (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R) hrN3 huN7).trans hN
  have hD:Nonempty (FuchsianDisc (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z}:Set Mobius.complexMobiusGroup))):=by
    rw [hG]
    exact ⟨(realSL_pair_halfPlaneData X R hd).asFuchsianDisc⟩
  have hcos:0≤Real.cos (3*(Real.pi/7)):=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩).le
  refine ⟨X,Y,Z,hx,hy,hz,hNative,hD,?_,?_⟩
  · rwa [hG]
  · have h:=realSL_three_conjugates_traceAbs X R hr (Real.pi/7) htU hcos
    simpa only [show 3*(Real.pi/7)=3*Real.pi/7 by ring] using h

theorem exists_trace_attaining_three_halfturns :
    ∃f g h:Mobius.complexMobiusGroup, orderOf f=2 ∧ orderOf g=2 ∧ orderOf h=2 ∧
      Nonempty (FuchsianDisc (Subgroup.closure ({f,g,h}:Set Mobius.complexMobiusGroup))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g,h}:Set Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h)=2*Real.cos (3*Real.pi/7) := by
  obtain ⟨U,ha,hb,hc⟩:=exists_finite_triangle_with_angles (Real.pi/7) (Real.pi/3) (Real.pi/2)
    (by positivity) (by positivity) (by positivity) (by linarith [Real.pi_pos])
  let T:=U.toClosedHTriangle
  have hα:T.alpha=Real.pi/7:=U.closed_angles.1.trans ha
  have hβ:T.beta=Real.pi/3:=U.closed_angles.2.1.trans hb
  have hγ:T.gamma=Real.pi/2:=U.closed_angles.2.2.trans hc
  obtain ⟨X,Y,Z,hx,hy,hz,_hN,hD,hNE,ht⟩:=triangle_two_three_seven_trace_attaining_halfturns T hα hβ hγ
  exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z,hx,hy,hz,hD,hNE,ht⟩

end LowDimensionalTopology.Geometry.Fuchsian
