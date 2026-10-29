module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneNativeRealForm
public import LowDimensionalTopology.Geometry.Teichmuller.SmoothFormInterior
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.LinearAlgebra.Determinant

/-! # Smoothness of the original native period tensor and fundamental form -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces
variable (τ₀ : ℍ) (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀)
local notation "RI" => 𝓘(ℝ, ℂ)
local notation "C" => nativePeriodChartedSpace τ₀ hperiod
local notation "Gm" => ℂ →L[ℝ] ℂ →L[ℝ] ℝ
local notation "Am" => ℂ [⋀^Fin 2]→L[ℝ] ℝ

/-- Both original native fibre families are smooth sections in the same period atlas. -/
theorem contMDiff_nativePeriodRealTensor_and_fundamentalForm :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :=
      (nativePeriodChart τ₀ hperiod).isManifold_singleton
      (nativePeriodChart_source τ₀ hperiod)
    ContMDiff RI (ModelWithCorners.prod RI 𝓘(ℝ, Gm)) ∞
      (fun q : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) =>
        TotalSpace.mk' Gm q (nativePeriodRealTensor τ₀ hperiod q)) ∧
    ContMDiff RI (ModelWithCorners.prod RI 𝓘(ℝ, Am)) ∞
      (fun q : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) =>
        TotalSpace.mk' Am q (nativePeriodFundamentalForm τ₀ hperiod q)) := by
  let := C
  let T := TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)
  let : IsManifold RI ω T := (nativePeriodChart τ₀ hperiod).isManifold_singleton
    (nativePeriodChart_source τ₀ hperiod)
  let E : ℍ ≃ₜ T := Classical.choose hperiod
  let K (q : T) : TangentSpace RI q ≃L[ℝ] ℂ :=
    ((mdifferentiable_chart (I := RI) q).mfderiv (mem_chart_source ℂ q)).trans
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (nativePeriodChart τ₀ hperiod q))
  have hchart : ContMDiff RI RI ∞ (((↑) : ℍ → ℂ) ∘ E.symm) := by
    intro q
    change ContMDiffAt RI RI ∞ (extChartAt RI q) q
    exact contMDiffAt_extChartAt
  have hp : ContMDiff RI RI ∞ E.symm :=
    hchart.of_comp_isOpenEmbedding UpperHalfPlane.isOpenEmbedding_coe
  have hG : ContMDiff RI 𝓘(ℝ, Gm) ∞ (fun q : T => parameterTensor (E.symm q)) := by
    simpa only [parameterTensor, Pi.smul_def', Function.comp_def] using
      (contMDiff_const (c := (1 / 2 : ℝ))).smul (I := 𝓘(ℝ))
        (Hyperbolic.contMDiff_halfPlanePoincareTensor.comp hp)
  let ε : Am :=
    { Complex.basisOneI.det with
      cont := by
        change Continuous (fun v : Fin 2 → ℂ => Complex.basisOneI.det v)
        have hc : Continuous (fun v : Fin 2 → ℂ =>
            (v 0).re * (v 1).im - (v 1).re * (v 0).im) :=
          ((Complex.continuous_re.comp (continuous_apply (0 : Fin 2))).mul
            (Complex.continuous_im.comp (continuous_apply (1 : Fin 2)))).sub
            ((Complex.continuous_re.comp (continuous_apply (1 : Fin 2))).mul
              (Complex.continuous_im.comp (continuous_apply (0 : Fin 2))))
        simpa only [Module.Basis.det_apply, Matrix.det_fin_two, Module.Basis.toMatrix_apply,
          Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one] using hc }
  have hε (u v : ℂ) : ε ![u,v] = u.re * v.im - u.im * v.re := by
    change Complex.basisOneI.det ![u,v] = _
    simp only [Module.Basis.det_apply, Matrix.det_fin_two, Module.Basis.toMatrix_apply,
      Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hrot (σ : ℍ) (u v : ℂ) : parameterTensor σ (Complex.I * u) v =
      parameterTensor σ 1 1 * (u.re * v.im - u.im * v.re) := by
    simp only [parameterTensor_apply, pairing_eq, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    ring
  have hA : ContMDiff RI 𝓘(ℝ, Am) ∞
      (fun q : T => parameterTensor (E.symm q) 1 1 • ε) :=
    ((hG.clm_apply contMDiff_const).clm_apply contMDiff_const).smul contMDiff_const
  have hs (a q : T) : (trivializationAt ℂ (TangentSpace RI) a).symmL ℝ q =
      (K q).symm.toContinuousLinearMap := by
    let e := trivializationAt ℂ (TangentSpace RI) a
    have hq : q ∈ e.baseSet := mem_chart_source ℂ q
    have ht : e.continuousLinearMapAt ℝ q = (K q).toContinuousLinearMap := by
      have hd := TangentBundle.continuousLinearMapAt_trivializationAt (I := RI)
        (show q ∈ (chartAt ℂ a).source from mem_chart_source ℂ q)
      apply ContinuousLinearMap.ext
      intro v
      exact congrArg (fun L : TangentSpace RI q →L[ℝ] ℂ => L v) hd
    apply ContinuousLinearMap.ext
    intro v
    apply (K q).injective
    have he : K q (e.symmL ℝ q v) = v :=
      (congrArg (fun L : TangentSpace RI q →L[ℝ] ℂ => L (e.symmL ℝ q v)) ht).symm.trans
        (e.continuousLinearMapAt_symmL hq v)
    exact he.trans ((K q).apply_symm_apply v).symm
  have hg (a q : T) : ((trivializationAt Gm
      (fun y : T => TangentSpace RI y →L[ℝ] TangentSpace RI y →L[ℝ] ℝ) a)
      ⟨q, nativePeriodRealTensor τ₀ hperiod q⟩).2 = parameterTensor (E.symm q) := by
    let e := trivializationAt ℂ (TangentSpace RI) a
    have hq : q ∈ e.baseSet := mem_chart_source ℂ q
    have hv (v : ℂ) : e.symm q v = (K q).symm v :=
      (e.symmL_apply (R := ℝ) hq v).symm.trans
        (congrArg (fun L : ℂ →L[ℝ] TangentSpace RI q => L v) (hs a q))
    rw [hom_trivializationAt_apply]
    ext u v
    change ContinuousLinearMap.inCoordinates ℂ (TangentSpace RI) (ℂ →L[ℝ] ℝ)
      (fun y : T => TangentSpace RI y →L[ℝ] ℝ) a q a q (nativePeriodRealTensor τ₀ hperiod q) u v = _
    rw [inCoordinates_apply_eq₂ hq hq (Set.mem_univ q)]
    simp only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.linearMapAt_trivialization,
      LinearMap.id_apply]
    rw [hv u, hv v]
    change parameterTensor (E.symm q) ((K q) ((K q).symm u)) ((K q) ((K q).symm v)) = _
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  have ha (a q : T) : ((trivializationAt Am
      (fun y : T => TangentSpace RI y [⋀^Fin 2]→L[ℝ] ℝ) a)
      ⟨q, nativePeriodFundamentalForm τ₀ hperiod q⟩).2 = parameterTensor (E.symm q) 1 1 • ε := by
    rw [FormInterior.form_trivialization, hs]
    ext v
    have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
    rw [hv]
    change fderiv ℝ parameterTwist (E.symm q : ℂ) ((K q) ((K q).symm (v 0))) *
        fderiv ℝ parameterLength (E.symm q : ℂ) ((K q) ((K q).symm (v 1))) -
      fderiv ℝ parameterTwist (E.symm q : ℂ) ((K q) ((K q).symm (v 1))) *
        fderiv ℝ parameterLength (E.symm q : ℂ) ((K q) ((K q).symm (v 0))) = _
    simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [← parameterTensor_eq_twist_wedge_length, hrot, hε]
  constructor
  · intro a
    apply (Bundle.contMDiffAt_section a).mpr
    exact (hG a).congr_of_eventuallyEq (Filter.Eventually.of_forall (hg a))
  · intro a
    apply (Bundle.contMDiffAt_section a).mpr
    exact (hA a).congr_of_eventuallyEq (Filter.Eventually.of_forall (ha a))

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
