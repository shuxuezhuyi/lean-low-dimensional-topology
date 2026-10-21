/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.ThreeHalfTurnSharpness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
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

/-- Genuine matrix generators of an actual integral right triangle, retaining
its geometric angle and induced discrete subgroup without assuming its type. -/
theorem cosine_triangle_real_pair (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (m q : ℕ)
    (hm : 2 ≤ m) (hq : 3 ≤ q)
    (hα : T.alpha = Real.pi / (q : ℝ))
    (hβ : T.beta = Real.pi / (m : ℝ)) (hγ : T.gamma = Real.pi / 2) :
    ∃ X R : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X) = 2 ∧ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R) = m ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R} : Set Mobius.complexMobiusGroup)) ∧
      (Matrix.trace (X * R⁻¹).val) ^ 2 = 4 * (Real.cos (Real.pi / (q : ℝ))) ^ 2 := by
  let X:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB
  let R:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineC
  let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineB T.sideLineC
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB
  let c:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC
  have hxN:orderOf (a*b)=2:=triangle_first_generator_order_of_integral_angle T 2 (by omega) hγ
  have hrN:orderOf (a*c)=m:=triangle_second_alternative_generator_order T m hm hβ
  have hx:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X)=2:=by
    rw [realSLMobius_order_eq_native]
    rw [show _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X=a*b from (reflectionProductSL_native _ _).symm]
    exact hxN
  have hr:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)=m:=by
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
  have hθ:T.cycle.gamma=Real.pi/(q:ℝ):=(closedHTriangle_cycle_angles T).2.2.trans hα
  have htW:(Matrix.trace W.val)^2=4*(Real.cos (Real.pi/(q:ℝ)))^2:=by
    have h:=triangle_first_generator_trace T.cycle
    change (Matrix.trace W.val)^2=4*(Real.cos T.cycle.gamma)^2 at h
    rwa [hθ] at h
  have htU:(Matrix.trace (X*R⁻¹).val)^2=4*(Real.cos (Real.pi/(q:ℝ)))^2:=by
    have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_product_add_inverse X R
    rw [htX,zero_mul] at h
    have he:Matrix.trace (X*R⁻¹).val= -Matrix.trace (X*R).val:=by linarith only [h]
    rw [he,neg_sq,hsq]
    exact htW
  have hN:Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R}:Set (ℍ≃ᵢℍ))=triangleConformalGroup T:=by
    dsimp only [X,R]
    rw [←reflectionProductSL_native,←reflectionProductSL_native]
    exact (triangle_alternative_generators T).symm
  have hConf:Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R}:Set (ℍ≃ᵢℍ))≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup:=by
    rw [hN]
    exact inf_le_right
  have hdiscT:DiscreteTopology (triangleConformalGroup T):=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_integral_angles T (Or.inr ⟨q,by omega,hα⟩)
      (Or.inr ⟨m,by omega,hβ⟩) (Or.inr ⟨2,by omega,hγ⟩)
  let : DiscreteTopology (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry R}:Set (ℍ≃ᵢℍ))):=by rwa [hN]
  have P:=nativeConformalSubgroup_halfPlaneData _ hConf
  have hG:=native_matrix_pair_mobius_image X R hConf
  have hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R}:Set Mobius.complexMobiusGroup)):=by
    have h:=P.discrete
    rwa [hG] at h
  exact ⟨X, R, hx, hr, hd, htU⟩

/-- An actual three-half-turn Fuchsian group with a genuinely elliptic,
noninvolutive product is non-elementary. -/
theorem cosine_three_halfturns_nonElementary
    (X Y Z : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hx : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X) = 2)
    (hy : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y) = 2)
    (hz : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z) = 2)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z} : Set Mobius.complexMobiusGroup)))
    (hlo : 0 < _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z))
    (hhi : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z) < 2) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z} : Set Mobius.complexMobiusGroup)) := by
  let H := Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z} : Set Mobius.complexMobiusGroup)
  have hreal : H ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range := by
    apply (Subgroup.closure_le _).mpr
    rintro f (rfl | rfl | rfl)
    · exact ⟨X, rfl⟩
    · exact ⟨Y, rfl⟩
    · exact ⟨Z, rfl⟩
  let P : HalfPlaneFuchsianGroup H := ⟨by
    intro f
    obtain ⟨A, hA⟩ := hreal f.property
    rw [← hA]
    exact realSLMobius_image_openHalfPlane A, hd⟩
  let W := X * Y * Z
  have htr : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z) =
      |Matrix.trace W.val| := by
    rw [← map_mul, ← map_mul, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_traceAbs]
  have htr0 : 0 < |Matrix.trace W.val| := by rwa [htr] at hlo
  have htr2 : |Matrix.trace W.val| < 2 := by rwa [htr] at hhi
  have hsq : (Matrix.trace W.val) ^ 2 < 4 := by
    nlinarith [sq_abs (Matrix.trace W.val), abs_nonneg (Matrix.trace W.val)]
  have hWn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W ≠ 1 := by
    intro he
    have hh := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_sq_of_projection_one W he
    linarith
  have hWe : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W) := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff W hWn).mpr hsq
  have hWo : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W) ≠ 2 := by
    intro he
    have hh := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_order_two_iff_trace_zero W hWn).mp he
    simp only [hh, abs_zero] at htr0
    exact lt_irrefl _ htr0
  have hX : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X ∈ H := Subgroup.subset_closure (by simp)
  have hY : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y ∈ H := Subgroup.subset_closure (by simp)
  have hZ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z ∈ H := Subgroup.subset_closure (by simp)
  have hW : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W ∈ H := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (X * Y * Z) ∈ H
    rw [map_mul, map_mul]
    exact H.mul_mem (H.mul_mem hX hY) hZ
  intro hE
  let : Finite H := elementary_elliptic_noninvolution_finite P.asFuchsianDisc hE _ hW hWe hWo
  let : IsCyclic H := finiteMobius_preserves_disc_isCyclic H P.asFuchsianDisc.isDisc P.asFuchsianDisc.image_eq
  let : CommGroup H := IsCyclic.commGroup
  let x : H := ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, hX⟩
  let y : H := ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y, hY⟩
  let z : H := ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z, hZ⟩
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X) ^ 2 = 1
    simpa only [hx] using pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X)
  have hy2 : y ^ 2 = 1 := by
    apply Subtype.ext
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y) ^ 2 = 1
    simpa only [hy] using pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y)
  have hz2 : z ^ 2 = 1 := by
    apply Subtype.ext
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z) ^ 2 = 1
    simpa only [hz] using pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z)
  have hp : (x * y * z) ^ 2 = 1 := by rw [mul_pow, mul_pow, hx2, hy2, hz2]; simp
  have hP : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W) ^ 2 = 1 := by
    have hh := congrArg Subtype.val hp
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z) ^ 2 = 1 at hh
    simpa only [W, map_mul] using hh
  have hdv : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W) ∣ 2 := orderOf_dvd_of_pow_eq_one hP
  have hh : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W) = 1 ∨ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W) = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hdv
  exact hh.elim (fun h => hWn (orderOf_eq_one_iff.mp h)) hWo

/-- Actual geometric realization of a scalar by three half-turns in their
own discrete non-elementary Fuchsian subgroup. -/
def HasThreeHalfTurnCosineRealization (lam : ℝ) : Prop :=
  ∃ f g h : Mobius.complexMobiusGroup, orderOf f = 2 ∧ orderOf g = 2 ∧ orderOf h = 2 ∧
    Nonempty (FuchsianDisc (Subgroup.closure ({f, g, h} : Set Mobius.complexMobiusGroup))) ∧
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f, g, h} : Set Mobius.complexMobiusGroup)) ∧
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f * g * h) / 2 = lam

theorem cosine_realSL_triple_realization
    (X Y Z : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hx : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X) = 2)
    (hy : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y) = 2)
    (hz : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z) = 2)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z} : Set Mobius.complexMobiusGroup)))
    (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam < 1)
    (ht : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z) = 2 * lam) :
    HasThreeHalfTurnCosineRealization lam := by
  let H := Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z} : Set Mobius.complexMobiusGroup)
  have hreal : H ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range := by
    apply (Subgroup.closure_le _).mpr
    rintro f (rfl | rfl | rfl)
    · exact ⟨X, rfl⟩
    · exact ⟨Y, rfl⟩
    · exact ⟨Z, rfl⟩
  let P : HalfPlaneFuchsianGroup H := ⟨by
    intro f
    obtain ⟨A, hA⟩ := hreal f.property
    rw [← hA]
    exact realSLMobius_image_openHalfPlane A, hd⟩
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z, hx, hy, hz,
    ⟨P.asFuchsianDisc⟩, ?_, ?_⟩
  · exact cosine_three_halfturns_nonElementary X Y Z hx hy hz hd (by rw [ht]; linarith)
      (by rw [ht]; linarith)
  · rw [ht]
    ring

theorem cosine_realSL_square_trace (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (A ^ 2).val = (Matrix.trace A.val) ^ 2 - 2 := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.det_coe
  rw [pow_two]
  norm_num [Matrix.trace_fin_two, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination -2 * hd

theorem cosine_realSL_square_trace_formula (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (θ : ℝ)
    (ht : (Matrix.trace A.val) ^ 2 = 4 * (Real.cos θ) ^ 2) :
    (Matrix.trace (A ^ 2).val) ^ 2 = 4 * (Real.cos (2 * θ)) ^ 2 := by
  rw [cosine_realSL_square_trace, ht, Real.cos_two_mul]
  ring

theorem cosine_three_words_of_four_one {G : Type*} [Group G] (x r : G) (hr : r ^ 4 = 1) :
    x * r ^ 2 * (r * x * r⁻¹) = (x * r⁻¹) ^ 2 := by
  have hr3 : r ^ 3 = r⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    simpa only [← pow_succ] using hr
  calc
    x * r ^ 2 * (r * x * r⁻¹) = x * r ^ 3 * x * r⁻¹ := by group
    _ = (x * r⁻¹) ^ 2 := by rw [hr3, pow_two]; group

theorem cosine_square_three_halfturns (X R : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hx : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X) = 2)
    (hr : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R) = 4)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R} : Set Mobius.complexMobiusGroup)))
    (θ : ℝ) (ht : (Matrix.trace (X * R⁻¹).val) ^ 2 = 4 * (Real.cos θ) ^ 2)
    (hc : 0 < Real.cos (2 * θ)) (hc1 : Real.cos (2 * θ) < 1) :
    HasThreeHalfTurnCosineRealization (Real.cos (2 * θ)) := by
  let Y := R ^ 2
  let Z := R * X * R⁻¹
  have hy : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y) = 2 := by
    rw [show _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R) ^ 2 by exact map_pow _ _ _]
    rw [orderOf_pow' _ (by norm_num), hr]
    norm_num
  have hz : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z) = 2 := by
    dsimp only [Z]
    simp only [map_mul, map_inv]
    exact ((MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)).orderOf_eq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X)).trans hx
  let K := Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R} : Set Mobius.complexMobiusGroup)
  have hX : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X ∈ K := Subgroup.subset_closure (by simp)
  have hR : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R ∈ K := Subgroup.subset_closure (by simp)
  have hY : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y ∈ K := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (R ^ 2) ∈ K
    rw [map_pow]
    exact K.pow_mem hR 2
  have hZ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z ∈ K := by
    dsimp only [Z]
    rw [map_mul, map_mul, map_inv]
    exact K.mul_mem (K.mul_mem hR hX) (K.inv_mem hR)
  have hsub : Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z} : Set Mobius.complexMobiusGroup) ≤ K := by
    apply (Subgroup.closure_le _).mpr
    rintro f (rfl | rfl | rfl)
    · exact hX
    · exact hY
    · exact hZ
  have hd3 := discreteMobius_subgroup_of_le K _ hd hsub
  apply cosine_realSL_triple_realization X Y Z hx hy hz hd3 _ hc hc1
  have hr4 : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R) ^ 4 = 1 := by
    simpa only [hr] using pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z = _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius ((X * R⁻¹) ^ 2) := by
    dsimp only [Y, Z]
    simp only [map_mul, map_inv, map_pow]
    exact cosine_three_words_of_four_one _ _ hr4
  rw [he, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_traceAbs]
  have hsq := cosine_realSL_square_trace_formula (X * R⁻¹) θ ht
  apply (sq_eq_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * Real.cos (2 * θ))).mp
  rw [sq_abs]
  nlinarith only [hsq]

theorem cosine_cube_three_halfturns (X R : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hx : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X) = 2)
    (hr : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R) = 3)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R} : Set Mobius.complexMobiusGroup)))
    (θ : ℝ) (ht : (Matrix.trace (X * R⁻¹).val) ^ 2 = 4 * (Real.cos θ) ^ 2)
    (hc : 0 < Real.cos (3 * θ)) (hc1 : Real.cos (3 * θ) < 1) :
    HasThreeHalfTurnCosineRealization (Real.cos (3 * θ)) := by
  let Y := R⁻¹ * X * R
  let Z := R * X * R⁻¹
  have hy : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y) = 2 := by
    dsimp only [Y]
    simp only [map_mul, map_inv]
    have h : orderOf ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)⁻¹ * _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X * ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)⁻¹)⁻¹) =
        orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X) :=
      (MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)⁻¹).orderOf_eq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X)
    simpa only [inv_inv, hx] using h
  have hz : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z) = 2 := by
    dsimp only [Z]
    simp only [map_mul, map_inv]
    exact ((MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R)).orderOf_eq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X)).trans hx
  let K := Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R} : Set Mobius.complexMobiusGroup)
  have hX : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X ∈ K := Subgroup.subset_closure (by simp)
  have hR : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R ∈ K := Subgroup.subset_closure (by simp)
  have hY : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y ∈ K := by
    dsimp only [Y]
    rw [map_mul, map_mul, map_inv]
    exact K.mul_mem (K.mul_mem (K.inv_mem hR) hX) hR
  have hZ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z ∈ K := by
    dsimp only [Z]
    rw [map_mul, map_mul, map_inv]
    exact K.mul_mem (K.mul_mem hR hX) (K.inv_mem hR)
  have hsub : Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius X, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Y, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Z} : Set Mobius.complexMobiusGroup) ≤ K := by
    apply (Subgroup.closure_le _).mpr
    rintro f (rfl | rfl | rfl)
    · exact hX
    · exact hY
    · exact hZ
  have hd3 := discreteMobius_subgroup_of_le K _ hd hsub
  apply cosine_realSL_triple_realization X Y Z hx hy hz hd3 _ hc hc1
  exact realSL_three_conjugates_traceAbs X R hr θ ht hc.le

/-- The listed parameters lie strictly inside the positive elliptic trace interval. -/
theorem cosine_listed_parameter_bounds (p q : ℕ) (hp : 0 < p) (hpq : 2 * p < q) :
    0 < Real.cos ((p : ℝ) * Real.pi / (q : ℝ)) ∧
      Real.cos ((p : ℝ) * Real.pi / (q : ℝ)) < 1 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpqR : 2 * (p : ℝ) < q := by exact_mod_cast hpq
  have hpos : 0 < (p : ℝ) * Real.pi / (q : ℝ) := by positivity
  have hhalf : (p : ℝ) * Real.pi / (q : ℝ) < Real.pi / 2 := by
    apply (div_lt_iff₀ hq).mpr
    nlinarith [Real.pi_pos]
  refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hhalf⟩, ?_⟩
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num)
    (show (p : ℝ) * Real.pi / (q : ℝ) ≤ Real.pi by linarith [Real.pi_pos]) hpos
  simpa only [Real.cos_zero] using h

/-- Every second-family value is realized, including even denominators, by
three actual half-turn words in the genuine (2,4,q) triangle group. -/
theorem three_halfturn_cosine_two_realizable (q : ℕ) (hq : 5 ≤ q) :
    HasThreeHalfTurnCosineRealization (Real.cos (2 * Real.pi / (q : ℝ))) := by
  have hqR : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have hangle : Real.pi / (q : ℝ) ≤ Real.pi / 5 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hqR
  obtain ⟨U, ha, hb, hc⟩ := exists_finite_triangle_with_angles
    (Real.pi / (q : ℝ)) (Real.pi / 4) (Real.pi / 2)
    (by positivity) (by positivity) (by positivity) (by linarith [Real.pi_pos])
  let T := U.toClosedHTriangle
  have hα : T.alpha = Real.pi / (q : ℝ) := U.closed_angles.1.trans ha
  have hβ : T.beta = Real.pi / 4 := U.closed_angles.2.1.trans hb
  have hγ : T.gamma = Real.pi / 2 := U.closed_angles.2.2.trans hc
  obtain ⟨X, R, hx, hr, hd, ht⟩ := cosine_triangle_real_pair T 4 q (by omega) (by omega) hα hβ hγ
  obtain ⟨hcos, hcos1⟩ := cosine_listed_parameter_bounds 2 q (by omega) (by omega)
  have hcos' : 0 < Real.cos (2 * (Real.pi / (q : ℝ))) := by
    simpa only [Nat.cast_ofNat, mul_div_assoc] using hcos
  have hcos1' : Real.cos (2 * (Real.pi / (q : ℝ))) < 1 := by
    simpa only [Nat.cast_ofNat, mul_div_assoc] using hcos1
  simpa only [mul_div_assoc] using cosine_square_three_halfturns X R hx hr hd
    (Real.pi / (q : ℝ)) ht hcos' hcos1'

/-- Every first-family value is obtained from the square construction in
an actual (2,4,2q) triangle group. -/
theorem three_halfturn_cosine_one_realizable (q : ℕ) (hq : 3 ≤ q) :
    HasThreeHalfTurnCosineRealization (Real.cos (Real.pi / (q : ℝ))) := by
  have h := three_halfturn_cosine_two_realizable (2 * q) (by omega)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have he : 2 * Real.pi / ((2 * q : ℕ) : ℝ) = Real.pi / (q : ℝ) := by
    push_cast
    field_simp
  simpa only [he] using h

/-- Every third-family value is realized by three conjugates in the genuine
(2,3,q) triangle group; no coprimality or equality with that ambient group is needed. -/
theorem three_halfturn_cosine_three_realizable (q : ℕ) (hq : 7 ≤ q) :
    HasThreeHalfTurnCosineRealization (Real.cos (3 * Real.pi / (q : ℝ))) := by
  have hqR : (7 : ℝ) ≤ q := by exact_mod_cast hq
  have hangle : Real.pi / (q : ℝ) ≤ Real.pi / 7 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hqR
  obtain ⟨U, ha, hb, hc⟩ := exists_finite_triangle_with_angles
    (Real.pi / (q : ℝ)) (Real.pi / 3) (Real.pi / 2)
    (by positivity) (by positivity) (by positivity) (by linarith [Real.pi_pos])
  let T := U.toClosedHTriangle
  have hα : T.alpha = Real.pi / (q : ℝ) := U.closed_angles.1.trans ha
  have hβ : T.beta = Real.pi / 3 := U.closed_angles.2.1.trans hb
  have hγ : T.gamma = Real.pi / 2 := U.closed_angles.2.2.trans hc
  obtain ⟨X, R, hx, hr, hd, ht⟩ := cosine_triangle_real_pair T 3 q (by omega) (by omega) hα hβ hγ
  obtain ⟨hcos, hcos1⟩ := cosine_listed_parameter_bounds 3 q (by omega) (by omega)
  have hcos' : 0 < Real.cos (3 * (Real.pi / (q : ℝ))) := by
    simpa only [Nat.cast_ofNat, mul_div_assoc] using hcos
  have hcos1' : Real.cos (3 * (Real.pi / (q : ℝ))) < 1 := by
    simpa only [Nat.cast_ofNat, mul_div_assoc] using hcos1
  simpa only [mul_div_assoc] using cosine_cube_three_halfturns X R hx hr hd
    (Real.pi / (q : ℝ)) ht hcos' hcos1'

/--
The realization assertion following: every scalar
in each of the three listed families occurs for actual discrete non-elementary
three-half-turn generators. This asserts no signature-by-parameter cross product.
-/
theorem three_halfturn_all_listed_cosines_realizable (p q : ℕ)
    (h : (p = 1 ∧ 3 ≤ q) ∨ (p = 2 ∧ 5 ≤ q) ∨ (p = 3 ∧ 7 ≤ q)) :
    ∃ f g h : Mobius.complexMobiusGroup, orderOf f = 2 ∧ orderOf g = 2 ∧ orderOf h = 2 ∧
      Nonempty (FuchsianDisc (Subgroup.closure ({f, g, h} : Set Mobius.complexMobiusGroup))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f, g, h} : Set Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f * g * h) / 2 = Real.cos ((p : ℝ) * Real.pi / (q : ℝ)) := by
  change HasThreeHalfTurnCosineRealization (Real.cos ((p : ℝ) * Real.pi / (q : ℝ)))
  rcases h with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩
  · simpa only [Nat.cast_one, one_mul] using three_halfturn_cosine_one_realizable q hq
  · exact three_halfturn_cosine_two_realizable q hq
  · exact three_halfturn_cosine_three_realizable q hq

/-- The same complete realization statement with induced discreteness
spelled out for its original three-generator subgroup. -/
theorem three_halfturn_all_listed_cosines_discrete_realizable (p q : ℕ)
    (hpq : (p = 1 ∧ 3 ≤ q) ∨ (p = 2 ∧ 5 ≤ q) ∨ (p = 3 ∧ 7 ≤ q)) :
    ∃ f g h : Mobius.complexMobiusGroup, orderOf f = 2 ∧ orderOf g = 2 ∧ orderOf h = 2 ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, g, h} : Set Mobius.complexMobiusGroup)) ∧
      Nonempty (FuchsianDisc (Subgroup.closure ({f, g, h} : Set Mobius.complexMobiusGroup))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f, g, h} : Set Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f * g * h) / 2 = Real.cos ((p : ℝ) * Real.pi / (q : ℝ)) := by
  obtain ⟨f, g, h, hf, hg, hh, hD, hNE, ht⟩ := three_halfturn_all_listed_cosines_realizable p q hpq
  let D := Classical.choice hD
  exact ⟨f, g, h, hf, hg, hh, D.discrete, hD, hNE, ht⟩

end LowDimensionalTopology.Geometry.Fuchsian
