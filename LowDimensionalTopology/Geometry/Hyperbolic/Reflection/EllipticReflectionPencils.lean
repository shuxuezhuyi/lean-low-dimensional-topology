/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.GeodesicReflections
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A reflection is determined by its actual action on the native half-plane. -/
theorem HalfPlaneLine.reflection_injective : Function.Injective HalfPlaneLine.reflection := by
  intro L M he
  apply HalfPlaneLine.carrier_injective
  ext z
  rw [← L.reflection_fixed_iff,← M.reflection_fixed_iff,he]

/-- Any chosen geodesic through an actual fixed point can be the first reflection factor. -/
theorem realSL_fixed_point_reflection_factor (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (v : ℍ) (hv : f • v = v) (L : HalfPlaneLine) (hL : v ∈ L.carrier) :
    ∃ M : HalfPlaneLine, v ∈ M.carrier ∧
      (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection := by
  let C := Matrix.SpecialLinearGroup.mapGL ℝ f * L.reflectionMatrix
  have hd : C.val.det < 0 := by
    change Matrix.det (f.val * L.reflectionMatrix.val) < 0
    rw [Matrix.det_mul,f.det_coe,one_mul]
    exact L.reflectionMatrix_det_neg
  have hc : C • v = v := by
    dsimp only [C]
    rw [mul_smul,L.reflectionMatrix_action,(L.reflection_fixed_iff v).mpr hL]
    change f • v = v
    exact hv
  have ht : Matrix.trace C.val = 0 :=
    (UpperHalfPlane.exists_gl_smul_eq_self_iff_trace_eq_zero hd).mp ⟨v,hc⟩
  obtain ⟨M,hM⟩ := realGL_trace_zero_is_reflection C hd ht
  refine ⟨M,?_,?_⟩
  · exact (M.reflection_fixed_iff v).mp ((congrFun hM v).symm.trans hc)
  · funext z
    have he := congrFun hM (L.reflection z)
    simp only [C,mul_smul,L.reflectionMatrix_action,L.reflection_involutive z] at he
    change f • z = M.reflection (L.reflection z) at he
    exact he

/-- The second genuine reflection factor is uniquely determined by the first one and the action. -/
theorem realSL_reflection_factor_unique (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (L M N : HalfPlaneLine)
    (hM : (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection)
    (hN : (f • · : ℍ → ℍ) = N.reflection ∘ L.reflection) : M = N := by
  apply HalfPlaneLine.reflection_injective
  funext z
  have he := congrFun (hM.symm.trans hN) (L.reflection z)
  simpa only [Function.comp_apply,L.reflection_involutive z] using he

/-- Every line through the genuine elliptic center is a freely chosen reflection factor. -/
theorem realSL_elliptic_reflection_factor (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusElliptic (realSLMobius f)) (L : HalfPlaneLine)
    (hL : hEllipticCenter f ((realSLMobius_elliptic_iff f hf.1).mp hf) ∈ L.carrier) :
    ∃! M : HalfPlaneLine,
      hEllipticCenter f ((realSLMobius_elliptic_iff f hf.1).mp hf) ∈ M.carrier ∧
      (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection := by
  let ht := (realSLMobius_elliptic_iff f hf.1).mp hf
  let v := hEllipticCenter f ht
  have hv : f • v = v := (hSL_elliptic_fixed_iff f ht v).mpr rfl
  obtain ⟨M,hMv,hM⟩ := realSL_fixed_point_reflection_factor f v hv L hL
  exact ⟨M,⟨hMv,hM⟩,fun N hN => realSL_reflection_factor_unique f L N M hN.2 hM⟩

/-- An actual nonidentity real action fixing a point of the native plane is elliptic. -/
theorem realSLMobius_elliptic_of_fixed (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (v : ℍ) (hv : f • v = v) :
    Mobius.MobiusElliptic (realSLMobius f) := by
  apply (realSLMobius_elliptic_iff f hf).mpr
  by_contra ht
  have hfix : (realSLMobius f).val ((v : ℂ) : Mobius.ExtendedComplex) = (v : ℂ) := by
    rw [realSLMobius_action,hv]
  have hbound : ((v : ℂ) : Mobius.ExtendedComplex) ∈ halfPlaneIdealBoundary := by
    rcases eq_or_lt_of_le (le_of_not_gt ht) with he | he
    · exact realSLMobius_parabolic_fixed_boundary f ((realSLMobius_parabolic_iff f hf).mpr he.symm) _ hfix
    · exact realSLMobius_hyperbolic_fixed_boundary f he _ hfix
  have hi := (coe_mem_halfPlaneIdealBoundary (v : ℂ)).mp hbound
  exact v.im_ne_zero hi

/-- The geometric intersecting-line criterion uses genuine native reflection actions. -/
theorem realSL_reflection_intersection_elliptic (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (L M : HalfPlaneLine) (v : ℍ)
    (hL : v ∈ L.carrier) (hM : v ∈ M.carrier)
    (he : (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection) :
    Mobius.MobiusElliptic (realSLMobius f) := by
  apply realSLMobius_elliptic_of_fixed f hf v
  have h := congrFun he v
  simpa only [Function.comp_apply,(L.reflection_fixed_iff v).mpr hL,
    (M.reflection_fixed_iff v).mpr hM] using h

/-- The elliptic factors are genuinely distinct geodesics. -/
theorem realSL_elliptic_reflection_factors_ne (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusElliptic (realSLMobius f)) (L M : HalfPlaneLine)
    (he : (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection) : L ≠ M := by
  intro hLM
  subst M
  let ht := (realSLMobius_elliptic_iff f hf.1).mp hf
  obtain ⟨z,hz⟩ := exists_ne (hEllipticCenter f ht)
  have hfix : f • z = z := by
    rw [congrFun he z,Function.comp_apply,L.reflection_involutive z]
  exact hz ((hSL_elliptic_fixed_iff f ht z).mp hfix)

/-- A nonidentity real action is elliptic exactly when it is the product of reflections
in distinct geodesics in an actual elliptic pencil. -/
theorem realSL_elliptic_iff_intersecting_reflections (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) :
    Mobius.MobiusElliptic (realSLMobius f) ↔
      ∃ L M : HalfPlaneLine, L ≠ M ∧ ∃ v : ℍ, v ∈ L.carrier ∧ v ∈ M.carrier ∧
        (f • · : ℍ → ℍ) = M.reflection ∘ L.reflection := by
  constructor
  · intro hE
    let ht := (realSLMobius_elliptic_iff f hE.1).mp hE
    let v := hEllipticCenter f ht
    let L := HalfPlaneLine.vertical v.re
    have hL : v ∈ L.carrier := rfl
    obtain ⟨M,hM,_⟩ := realSL_elliptic_reflection_factor f hE L hL
    exact ⟨L,M,realSL_elliptic_reflection_factors_ne f hE L M hM.2,v,hL,hM.1,hM.2⟩
  · rintro ⟨L,M,_,v,hL,hM,he⟩
    exact realSL_reflection_intersection_elliptic f hf L M v hL hM he

/-- A prescribed line through an actual fixed point can also be the second factor. -/
theorem realSL_fixed_point_reflection_factor_right (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (v : ℍ) (hv : f • v = v) (L : HalfPlaneLine) (hL : v ∈ L.carrier) :
    ∃ M : HalfPlaneLine, v ∈ M.carrier ∧
      (f • · : ℍ → ℍ) = L.reflection ∘ M.reflection := by
  let C := L.reflectionMatrix * Matrix.SpecialLinearGroup.mapGL ℝ f
  have hd : C.val.det < 0 := by
    change Matrix.det (L.reflectionMatrix.val * f.val) < 0
    rw [Matrix.det_mul,f.det_coe,mul_one]
    exact L.reflectionMatrix_det_neg
  have hc : C • v = v := by
    dsimp only [C]
    rw [mul_smul]
    change L.reflectionMatrix • (f • v) = v
    rw [hv,L.reflectionMatrix_action,(L.reflection_fixed_iff v).mpr hL]
  have ht : Matrix.trace C.val = 0 :=
    (UpperHalfPlane.exists_gl_smul_eq_self_iff_trace_eq_zero hd).mp ⟨v,hc⟩
  obtain ⟨M,hM⟩ := realGL_trace_zero_is_reflection C hd ht
  refine ⟨M,?_,?_⟩
  · exact (M.reflection_fixed_iff v).mp ((congrFun hM v).symm.trans hc)
  · funext z
    have he := congrFun hM z
    simp only [C,mul_smul,L.reflectionMatrix_action] at he
    change L.reflection (f • z) = M.reflection z at he
    have hh := congrArg L.reflection he
    simpa only [L.reflection_involutive (f • z),Function.comp_apply] using hh

/-- Either factor line can be prescribed freely in the genuine elliptic pencil. -/
theorem realSL_elliptic_reflection_factor_right (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : Mobius.MobiusElliptic (realSLMobius f)) (L : HalfPlaneLine)
    (hL : hEllipticCenter f ((realSLMobius_elliptic_iff f hf.1).mp hf) ∈ L.carrier) :
    ∃! M : HalfPlaneLine,
      hEllipticCenter f ((realSLMobius_elliptic_iff f hf.1).mp hf) ∈ M.carrier ∧
      (f • · : ℍ → ℍ) = L.reflection ∘ M.reflection := by
  let ht := (realSLMobius_elliptic_iff f hf.1).mp hf
  let v := hEllipticCenter f ht
  have hv : f • v = v := (hSL_elliptic_fixed_iff f ht v).mpr rfl
  obtain ⟨M,hMv,hM⟩ := realSL_fixed_point_reflection_factor_right f v hv L hL
  refine ⟨M,⟨hMv,hM⟩,?_⟩
  intro N hN
  apply HalfPlaneLine.reflection_injective
  funext z
  have he := congrArg L.reflection (congrFun (hN.2.symm.trans hM) z)
  simpa only [Function.comp_apply,L.reflection_involutive (N.reflection z),
    L.reflection_involutive (M.reflection z)] using he

end LowDimensionalTopology.Geometry.Hyperbolic
