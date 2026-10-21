/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicHeckeModels
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleIntegralDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.WeakDisplacementGap
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

theorem three_halfturn_generators_odd_product {G : Type*} [Group G] (x r : G)
    (hodd : Odd (orderOf (x*r))) :
    Subgroup.closure ({x,r^2,r⁻¹*x*r} : Set G)=Subgroup.closure ({x,r} : Set G) := by
  let H:=Subgroup.closure ({x,r^2,r⁻¹*x*r} : Set G)
  have hx:x∈H:=Subgroup.subset_closure (by simp)
  have hr2:r^2∈H:=Subgroup.subset_closure (by simp)
  have hz:r⁻¹*x*r∈H:=Subgroup.subset_closure (by simp)
  have hsq:(x*r)^2∈H:=by
    rw [show (x*r)^2=x*r^2*(r⁻¹*x*r) by simp only [pow_two];group]
    exact H.mul_mem (H.mul_mem hx hr2) hz
  have hxr:x*r∈H:=odd_order_mem_of_square_mem H (x*r) hodd hsq
  have hr:r∈H:=by
    have h:=H.mul_mem (H.inv_mem hx) hxr
    rw [show x⁻¹*(x*r)=r by group] at h
    exact h
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with hz|hz|hz
    · rw [hz];exact Subgroup.subset_closure (by simp)
    · rw [hz];exact (Subgroup.closure ({x,r} : Set G)).pow_mem (Subgroup.subset_closure (by simp)) 2
    · rw [hz]
      exact (Subgroup.closure ({x,r} : Set G)).mul_mem
        ((Subgroup.closure ({x,r} : Set G)).mul_mem
          ((Subgroup.closure ({x,r} : Set G)).inv_mem (Subgroup.subset_closure (by simp)))
          (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
  · apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with hz|hz
    · rw [hz];exact hx
    · rw [hz];exact hr

theorem three_conjugate_halfturns_seven_product {G : Type*} [Group G] (x r : G)
    (hr : r^3=1) (hu : (x*r⁻¹)^7=1) :
    Subgroup.closure ({x,r⁻¹*x*r,r*x*r⁻¹} : Set G)=Subgroup.closure ({x,r} : Set G) := by
  let H:=Subgroup.closure ({x,r⁻¹*x*r,r*x*r⁻¹} : Set G)
  have hx:x∈H:=Subgroup.subset_closure (by simp)
  have hy:r⁻¹*x*r∈H:=Subgroup.subset_closure (by simp)
  have hz:r*x*r⁻¹∈H:=Subgroup.subset_closure (by simp)
  have hr2:r*r=r⁻¹:=by
    apply eq_inv_iff_mul_eq_one.mpr
    calc (r*r)*r=r^3:=by simp only [pow_succ,pow_zero,one_mul,mul_assoc]
         _=1:=hr
  have hc:(x*r⁻¹)^3∈H:=by
    have he:x*(r⁻¹*x*r)*(r*x*r⁻¹)=(x*r⁻¹)^3:=by
      calc x*(r⁻¹*x*r)*(r*x*r⁻¹)=x*r⁻¹*x*(r*r)*x*r⁻¹:=by group
           _=(x*r⁻¹)^3:=by rw [hr2];simp only [pow_succ,pow_zero,one_mul,mul_assoc]
    rw [←he]
    exact H.mul_mem (H.mul_mem hx hy) hz
  have hxr:x*r⁻¹∈H:=by
    have hp:=H.pow_mem hc 5
    have he:((x*r⁻¹)^3)^5=x*r⁻¹:=by
      rw [←pow_mul,show 3*5=7*2+1 by norm_num,pow_add,pow_mul,hu,one_pow,one_mul,pow_one]
    rwa [he] at hp
  have hrH:r∈H:=by
    have hp:=H.mul_mem (H.inv_mem hx) hxr
    rw [show x⁻¹*(x*r⁻¹)=r⁻¹ by group] at hp
    simpa only [inv_inv] using H.inv_mem hp
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with hz|hz|hz
    · rw [hz];exact Subgroup.subset_closure (by simp)
    · rw [hz]
      exact (Subgroup.closure ({x,r} : Set G)).mul_mem
        ((Subgroup.closure ({x,r} : Set G)).mul_mem
          ((Subgroup.closure ({x,r} : Set G)).inv_mem (Subgroup.subset_closure (by simp)))
          (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
    · rw [hz]
      exact (Subgroup.closure ({x,r} : Set G)).mul_mem
        ((Subgroup.closure ({x,r} : Set G)).mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
        ((Subgroup.closure ({x,r} : Set G)).inv_mem (Subgroup.subset_closure (by simp)))
  · apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with hz|hz
    · rw [hz];exact hx
    · rw [hz];exact hrH

theorem realSL_order_of_reciprocal_cosine_trace (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (n : ℕ) (hn : 3≤n)
    (ht : (Matrix.trace A.val)^2=4*(Real.cos (Real.pi/(n:ℝ)))^2) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=n := by
  let B:=standardHeckeCornerSL n
  have hb:Matrix.trace B.val=2*Real.cos (Real.pi/(n:ℝ)):=by
    norm_num [B,standardHeckeCornerSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
  have he:_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace]
    have h:(Matrix.trace A.val)^2=(Matrix.trace B.val)^2:=by rw [hb];nlinarith only [ht]
    exact_mod_cast h
  have hc:IsConj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_isConj_iff_squaredTrace_eq _ _ hne (standardHeckeCornerSL_elliptic n hn).1).mpr he
  obtain ⟨q,hq⟩:=isConj_iff.mp hc
  have ho:orderOf (q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*q⁻¹)=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=
    (MulAut.conj q).orderOf_eq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
  rw [hq] at ho
  exact ho.symm.trans (standardHeckeMobiusProduct_order n hn)

theorem triangle_first_generator_order_of_integral_angle
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (n : ℕ) (hn : 2≤n) (ht : T.gamma=Real.pi/(n:ℝ)) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB)=n := by
  have hnR:(0:ℝ)<n:=by exact_mod_cast (by omega:0<n)
  have hγ:0<T.gamma:=by rw [ht];exact div_pos Real.pi_pos hnR
  let A:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB
  have hE:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=triangle_first_generator_elliptic_of_gamma_pos T hγ
  have htrace:(Matrix.trace A.val)^2=4*(Real.cos (Real.pi/(n:ℝ)))^2:=by
    simpa only [ht] using triangle_first_generator_trace T
  rw [reflectionProductSL_native,←realSLMobius_order_eq_native]
  by_cases hn2:n=2
  · subst n
    have hzero:Matrix.trace A.val=0:=by
      norm_num only [Nat.cast_ofNat,Real.cos_pi_div_two,zero_pow,OfNat.ofNat_ne_zero,mul_zero] at htrace
      nlinarith only [htrace]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_order_two_iff_trace_zero A hE.1).mpr hzero
  · exact realSL_order_of_reciprocal_cosine_trace A hE.1 n (by omega) htrace

theorem triangle_alternative_generators (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    triangleConformalGroup T=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA*_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA*_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC}
        :Set (ℍ≃ᵢℍ)) := by
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB
  let c:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC
  have hci:c⁻¹=c:=halfPlaneLineReflectionIsometry_inv _
  rw [triangleConformalGroup_eq_pairProductGroup]
  change Subgroup.closure ({a*b,c*b}:Set (ℍ≃ᵢℍ))=Subgroup.closure ({a*b,a*c}:Set (ℍ≃ᵢℍ))
  have hcb:c*b=(a*c)⁻¹*(a*b):=by rw [mul_inv_rev,hci];group
  have hac:a*c=(a*b)*(c*b)⁻¹:=by rw [mul_inv_rev,hci];group
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with hz|hz
    · rw [hz];exact Subgroup.subset_closure (by simp)
    · rw [hz,hcb]
      exact (Subgroup.closure ({a*b,a*c}:Set (ℍ≃ᵢℍ))).mul_mem
        ((Subgroup.closure ({a*b,a*c}:Set (ℍ≃ᵢℍ))).inv_mem (Subgroup.subset_closure (by simp)))
        (Subgroup.subset_closure (by simp))
  · apply (Subgroup.closure_le _).mpr
    intro z hz
    simp only [mem_insert_iff,mem_singleton_iff] at hz
    rcases hz with hz|hz
    · rw [hz];exact Subgroup.subset_closure (by simp)
    · rw [hz,hac]
      exact (Subgroup.closure ({a*b,c*b}:Set (ℍ≃ᵢℍ))).mul_mem
        (Subgroup.subset_closure (by simp))
        ((Subgroup.closure ({a*b,c*b}:Set (ℍ≃ᵢℍ))).inv_mem (Subgroup.subset_closure (by simp)))

theorem triangle_second_alternative_generator_order
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (n : ℕ) (hn : 2≤n) (ht : T.beta=Real.pi/(n:ℝ)) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC)=n := by
  have hcy:=closedHTriangle_cycle_angles T
  have hcy2:=closedHTriangle_cycle_angles T.cycle
  have hθ:T.cycle.cycle.gamma=Real.pi/(n:ℝ):=hcy2.2.2.trans (hcy.1.trans ht)
  have h:=triangle_first_generator_order_of_integral_angle T.cycle.cycle n hn hθ
  change orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC*
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA)=n at h
  have he:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC)⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA:=by
    rw [mul_inv_rev,halfPlaneLineReflectionIsometry_inv,halfPlaneLineReflectionIsometry_inv]
  rwa [←he,orderOf_inv] at h

theorem triangle_two_four_odd_halfturn_generators
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (q : ℕ) (hq : 3≤q) (hqOdd : Odd q)
    (hα : T.alpha=Real.pi/(q:ℝ)) (hβ : T.beta=Real.pi/4) (hγ : T.gamma=Real.pi/2) :
    ∃x y z : ℍ≃ᵢℍ,orderOf x=2 ∧ orderOf y=2 ∧ orderOf z=2 ∧
      Subgroup.closure ({x,y,z}:Set (ℍ≃ᵢℍ))=triangleConformalGroup T := by
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB
  let c:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC
  let x:=a*b
  let r:=a*c
  have hbi:b⁻¹=b:=halfPlaneLineReflectionIsometry_inv _
  have hx:orderOf x=2:=triangle_first_generator_order_of_integral_angle T 2 (by omega) hγ
  have hr:orderOf r=4:=triangle_second_alternative_generator_order T 4 (by omega) hβ
  have hxi:x⁻¹=x:=by
    apply inv_eq_of_mul_eq_one_right
    have h:=pow_orderOf_eq_one x
    simpa only [hx,pow_two] using h
  have hprod:x*r=b*c:=by
    calc x*r=x⁻¹*r:=by rw [hxi]
         _=b*c:=by dsimp only [x,r];rw [mul_inv_rev,hbi];group
  have hθ:T.cycle.gamma=Real.pi/(q:ℝ):=(closedHTriangle_cycle_angles T).2.2.trans hα
  have hbc:orderOf (b*c)=q:=triangle_first_generator_order_of_integral_angle T.cycle q (by omega) hθ
  have ho:Odd (orderOf (x*r)):=by rw [hprod,hbc];exact hqOdd
  have hy:orderOf (r^2)=2:=by rw [orderOf_pow' r (by norm_num),hr];norm_num
  have hz:orderOf (r⁻¹*x*r)=2:=by
    have h:orderOf (r⁻¹*x*(r⁻¹)⁻¹)=orderOf x:=(MulAut.conj r⁻¹).orderOf_eq x
    simpa only [inv_inv,hx] using h
  refine ⟨x,r^2,r⁻¹*x*r,hx,hy,hz,?_⟩
  exact (three_halfturn_generators_odd_product x r ho).trans (triangle_alternative_generators T).symm

theorem triangle_two_three_seven_halfturn_generators
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hα : T.alpha=Real.pi/7) (hβ : T.beta=Real.pi/3) (hγ : T.gamma=Real.pi/2) :
    ∃x y z : ℍ≃ᵢℍ,orderOf x=2 ∧ orderOf y=2 ∧ orderOf z=2 ∧
      Subgroup.closure ({x,y,z}:Set (ℍ≃ᵢℍ))=triangleConformalGroup T := by
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB
  let c:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC
  let x:=a*b
  let r:=a*c
  have hai:a⁻¹=a:=halfPlaneLineReflectionIsometry_inv _
  have hci:c⁻¹=c:=halfPlaneLineReflectionIsometry_inv _
  have hx:orderOf x=2:=triangle_first_generator_order_of_integral_angle T 2 (by omega) hγ
  have hr:orderOf r=3:=triangle_second_alternative_generator_order T 3 (by omega) hβ
  have hθ:T.cycle.gamma=Real.pi/7:=(closedHTriangle_cycle_angles T).2.2.trans hα
  have hbc:orderOf (b*c)=7:=triangle_first_generator_order_of_integral_angle T.cycle 7 (by omega) hθ
  have he:x*r⁻¹=(MulAut.conj a) (b*c):=by
    change (a*b)*(a*c)⁻¹=a*(b*c)*a⁻¹
    rw [mul_inv_rev,hci,hai]
    group
  have hu:(x*r⁻¹)^7=1:=by
    rw [he,←map_pow]
    have h:(b*c)^7=1:=by simpa only [hbc] using pow_orderOf_eq_one (b*c)
    rw [h,map_one]
  have hr3:r^3=1:=by simpa only [hr] using pow_orderOf_eq_one r
  have hy:orderOf (r⁻¹*x*r)=2:=by
    have h:orderOf (r⁻¹*x*(r⁻¹)⁻¹)=orderOf x:=(MulAut.conj r⁻¹).orderOf_eq x
    simpa only [inv_inv,hx] using h
  have hz:orderOf (r*x*r⁻¹)=2:=by
    exact ((MulAut.conj r).orderOf_eq x).trans hx
  refine ⟨x,r⁻¹*x*r,r*x*r⁻¹,hx,hy,hz,?_⟩
  exact (three_conjugate_halfturns_seven_product x r hr3 hu).trans
    (triangle_alternative_generators T).symm

theorem fuchsian_orders_two_three_seven_nonElementary
    (H : Subgroup Mobius.complexMobiusGroup)
    (D : FuchsianDisc H) (f g : Mobius.complexMobiusGroup) (hf : f∈H) (hg : g∈H)
    (hf2 : orderOf f=2) (hg3 : orderOf g=3) (hfg : orderOf (f*g⁻¹)=7) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H := by
  intro he
  have hgn:g≠1:=by intro h;rw [h,orderOf_one] at hg3;omega
  have hfin:IsOfFinOrder g:=orderOf_pos_iff.mp (by rw [hg3];omega)
  have hEll:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g:=_root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic g hgn hfin
  let : Finite H:=elementary_elliptic_noninvolution_finite D he g hg hEll (by omega)
  let : IsCyclic H:=finiteMobius_preserves_disc_isCyclic H D.isDisc D.image_eq
  let : CommGroup H:=IsCyclic.commGroup
  have hcomm:Commute f g:=by
    change f*g=g*f
    exact congrArg Subtype.val (mul_comm (⟨f,hf⟩:H) (⟨g,hg⟩:H))
  have hfP:f^2=1:=by simpa only [hf2] using pow_orderOf_eq_one f
  have hgP:g^3=1:=by simpa only [hg3] using pow_orderOf_eq_one g
  have hf6:f^6=1:=by rw [show 6=2*3 by norm_num,pow_mul,hfP,one_pow]
  have hg6:(g⁻¹)^6=1:=by rw [inv_pow,show 6=3*2 by norm_num,pow_mul,hgP,one_pow,inv_one]
  have hp:(f*g⁻¹)^6=1:=by rw [hcomm.inv_right.mul_pow,hf6,hg6,mul_one]
  have hd:=orderOf_dvd_of_pow_eq_one hp
  rw [hfg] at hd
  norm_num at hd

theorem exists_two_four_odd_halfturn_triangle (q : ℕ) (hq : 5≤q) (hqOdd : Odd q) :
    ∃T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle,∃x y z : ℍ≃ᵢℍ,
      T.alpha=Real.pi/(q:ℝ) ∧ T.beta=Real.pi/4 ∧ T.gamma=Real.pi/2 ∧
      orderOf x=2 ∧ orderOf y=2 ∧ orderOf z=2 ∧
      Subgroup.closure ({x,y,z}:Set (ℍ≃ᵢℍ))=triangleConformalGroup T ∧
      DiscreteTopology (triangleConformalGroup T) := by
  have hqR:(5:ℝ)≤q:=by exact_mod_cast hq
  have hangle:Real.pi/(q:ℝ)≤Real.pi/5:=div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hqR
  obtain ⟨U,ha,hb,hc⟩:=exists_finite_triangle_with_angles (Real.pi/(q:ℝ)) (Real.pi/4) (Real.pi/2)
    (by positivity) (by positivity) (by positivity) (by linarith [Real.pi_pos])
  let T:=U.toClosedHTriangle
  have hα:T.alpha=Real.pi/(q:ℝ):=U.closed_angles.1.trans ha
  have hβ:T.beta=Real.pi/4:=U.closed_angles.2.1.trans hb
  have hγ:T.gamma=Real.pi/2:=U.closed_angles.2.2.trans hc
  obtain ⟨x,y,z,hx,hy,hz,hG⟩:=triangle_two_four_odd_halfturn_generators T q (by omega) hqOdd hα hβ hγ
  refine ⟨T,x,y,z,hα,hβ,hγ,hx,hy,hz,hG,?_⟩
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_integral_angles T (Or.inr ⟨q,by omega,hα⟩)
    (Or.inr ⟨4,by omega,hβ⟩) (Or.inr ⟨2,by omega,hγ⟩)

theorem exists_two_three_seven_halfturn_triangle :
    ∃T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle,∃x y z : ℍ≃ᵢℍ,
      T.alpha=Real.pi/7 ∧ T.beta=Real.pi/3 ∧ T.gamma=Real.pi/2 ∧
      orderOf x=2 ∧ orderOf y=2 ∧ orderOf z=2 ∧
      Subgroup.closure ({x,y,z}:Set (ℍ≃ᵢℍ))=triangleConformalGroup T ∧
      DiscreteTopology (triangleConformalGroup T) := by
  obtain ⟨U,ha,hb,hc⟩:=exists_finite_triangle_with_angles (Real.pi/7) (Real.pi/3) (Real.pi/2)
    (by positivity) (by positivity) (by positivity) (by linarith [Real.pi_pos])
  let T:=U.toClosedHTriangle
  have hα:T.alpha=Real.pi/7:=U.closed_angles.1.trans ha
  have hβ:T.beta=Real.pi/3:=U.closed_angles.2.1.trans hb
  have hγ:T.gamma=Real.pi/2:=U.closed_angles.2.2.trans hc
  obtain ⟨x,y,z,hx,hy,hz,hG⟩:=triangle_two_three_seven_halfturn_generators T hα hβ hγ
  refine ⟨T,x,y,z,hα,hβ,hγ,hx,hy,hz,hG,?_⟩
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_integral_angles T (Or.inr ⟨7,by omega,hα⟩)
    (Or.inr ⟨3,by omega,hβ⟩) (Or.inr ⟨2,by omega,hγ⟩)

end LowDimensionalTopology.Geometry.Fuchsian
