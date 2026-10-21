/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleReflectionGroups
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeDihedralChambers
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
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

theorem two_involutions_zpow_normal_form {G:Type*} [Group G] (a b:G)
    (ha:a*a=1) (hb:b*b=1) (g:G) (hg:g∈Subgroup.closure ({a,b}:Set G)) :
    ∃k:ℤ,g=(a*b)^k ∨g=(a*b)^k*a := by
  have hai:a⁻¹=a:=inv_eq_of_mul_eq_one_right ha
  have hbi:b⁻¹=b:=inv_eq_of_mul_eq_one_right hb
  have step (x:G) (hx:∃k:ℤ,x=(a*b)^k ∨x=(a*b)^k*a) (y:G) (hy:y∈({a,b}:Set G)) :
      ∃k:ℤ,x*y=(a*b)^k ∨x*y=(a*b)^k*a:=by
    obtain ⟨k,hk|hk⟩:=hx
    · rcases hy with hy|hy
      · rw [hy,hk];exact ⟨k,Or.inr rfl⟩
      · rw [mem_singleton_iff] at hy
        rw [hy,hk]
        refine ⟨k-1,Or.inr ?_⟩
        rw [zpow_sub,zpow_one,mul_assoc]
        congr 1
        rw [mul_inv_rev,hbi]
        group
    · rcases hy with hy|hy
      · rw [hy,hk,mul_assoc,ha,mul_one];exact ⟨k,Or.inl rfl⟩
      · rw [mem_singleton_iff] at hy
        rw [hy,hk]
        refine ⟨k+1,Or.inl ?_⟩
        rw [zpow_add,zpow_one]
        group
  apply Subgroup.closure_induction_right (p:=fun x _=>∃k:ℤ,x=(a*b)^k ∨x=(a*b)^k*a) _ _ _ hg
  · exact ⟨0,Or.inl (by simp only [zpow_zero])⟩
  · intro x hx y hy ih
    exact step x ih y hy
  · intro x hx y hy ih
    have hyi:y⁻¹=y:=by
      rcases hy with hy|hy
      · rw [hy];exact hai
      · rw [mem_singleton_iff] at hy;rw [hy];exact hbi
    rw [hyi]
    exact step x ih y hy

theorem two_mirrors_conformal_subgroup (L M:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry M}:Set (ℍ≃ᵢℍ)) ⊓_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup=
      Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L*_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry M) := by
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry M
  let K:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup
  let J:=Subgroup.closure ({a,b}:Set (ℍ≃ᵢℍ))
  have ha:a*a=1:=by simpa only [pow_two] using halfPlaneLineReflectionIsometry_sq L
  have hb:b*b=1:=by simpa only [pow_two] using halfPlaneLineReflectionIsometry_sq M
  have hr:a*b∈K:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L M,(reflectionProductSL_native L M).symm⟩
  apply le_antisymm
  · intro g hg
    obtain ⟨k,hk|hk⟩:=two_involutions_zpow_normal_form a b ha hb g hg.1
    · rw [hk];exact Subgroup.zpow_mem_zpowers _ _
    · have hConf:=hg.2
      rw [hk] at hConf
      have h:=K.mul_mem (K.inv_mem (K.zpow_mem hr k)) hConf
      rw [show ((a*b)^k)⁻¹*((a*b)^k*a)=a by group] at h
      exact False.elim (halfPlaneLineReflectionIsometry_not_conformal L h)
  · apply Subgroup.zpowers_le.mpr
    exact ⟨J.mul_mem (Subgroup.subset_closure (Or.inl rfl)) (Subgroup.subset_closure (Or.inr rfl)),hr⟩

local instance twoMirrorDiscHyperbolicMetric : MetricSpace 𝔻:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric

def circleDiscRotationHom : Circle→*(𝔻≃ᵢ𝔻) where
  toFun u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalIsometry (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap u false)
  map_one':=by rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_one,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalIsometry_one]
  map_mul' u v:=by rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalIsometry_mul,_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_mul];rfl

theorem circleDiscRotationHom_apply (u:Circle) (z:𝔻) :
    (circleDiscRotationHom u z:ℂ)=(u:ℂ)*(z:ℂ) := by
  change _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap u false (z:ℂ)=_
  simpa using _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply u false (z:ℂ)

theorem circleDiscRotationHom_injective : Function.Injective circleDiscRotationHom := by
  intro u v huv
  let z:𝔻:=Complex.UnitDisc.mk (1/2:ℂ) (by norm_num)
  have h:=congrArg (fun f:𝔻≃ᵢ𝔻=>(f z:ℂ)) huv
  rw [circleDiscRotationHom_apply,circleDiscRotationHom_apply] at h
  change (u:ℂ)*(1/2)=(v:ℂ)*(1/2) at h
  apply Circle.coe_injective
  linear_combination 2*h

theorem circleDiscRotationHom_finite_generator_order (n:ℕ) (hn:0<n) :
    orderOf (circleDiscRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n))=n := by
  rw [orderOf_injective circleDiscRotationHom circleDiscRotationHom_injective]
  exact (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator_isPrimitiveRoot n hn.ne').eq_orderOf.symm

/-- The actual product of the original two finite-angle mirrors has exactly the reciprocal-angle order. -/
theorem native_reflection_product_order_of_angle {p:ℍ} (R Q:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt p)
    (hne:R.supportLine≠Q.supportLine) (n:ℕ) (hn:2≤n)
    (hθ:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R Q=Real.pi/(n:ℝ)) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry R.supportLine*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry Q.supportLine)=n := by
  obtain ⟨e,_he,_hc,_hG,hPair⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertex_group_chart R Q hne n hn hθ
  have hp:({_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation e (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry R.supportLine),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation e (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry Q.supportLine)} : Set (𝔻≃ᵢ𝔻)) =
      {_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalIsometry (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap 1 true),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalIsometry (_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n) true)}:=by
    simpa only [image_pair,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry] using hPair
  have ho:=orderOf_injective (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation e) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation_injective e)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry R.supportLine*_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry Q.supportLine)
  rw [map_mul] at ho
  rcases Set.pair_eq_pair_iff.mp hp with ⟨hR,hQ⟩|⟨hR,hQ⟩
  · rw [hR,hQ,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalIsometry_mul,_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_mul] at ho
    simp only [ite_true,Bool.xor_self,one_mul] at ho
    change orderOf (circleDiscRotationHom ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n)⁻¹))=_ at ho
    rw [map_inv,orderOf_inv] at ho
    exact ho.symm.trans (circleDiscRotationHom_finite_generator_order n (by omega))
  · rw [hR,hQ,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalIsometry_mul,_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_mul] at ho
    simp only [ite_true,Bool.xor_self,inv_one,mul_one] at ho
    change orderOf (circleDiscRotationHom (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n))=_ at ho
    exact ho.symm.trans (circleDiscRotationHom_finite_generator_order n (by omega))

end LowDimensionalTopology.Geometry.Fuchsian
