module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneNativeHermitianCore
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Smooth Hermitian coefficients in the actual native period frame -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Filter
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces

/-- The original Hermitian data have smooth coefficients in the actual complex period frame. -/
theorem contMDiff_nativePeriodHermitianCore_coordinates
    (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀)
    (u v : ℂ) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    letI : IsManifold 𝓘(ℝ, ℂ) ω
        (TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :=
      (nativePeriodChart τ₀ hperiod).isManifold_singleton
        (nativePeriodChart_source τ₀ hperiod)
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (fun q : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) =>
        (nativePeriodHermitianCore τ₀ hperiod q).inner
          ((nativePeriodTangentCoordinateEquiv τ₀ hperiod q).symm v)
          ((nativePeriodTangentCoordinateEquiv τ₀ hperiod q).symm u)) := by
  let := nativePeriodChartedSpace τ₀ hperiod
  let T := TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)
  let RI := 𝓘(ℝ, ℂ)
  let : IsManifold RI ω T := (nativePeriodChart τ₀ hperiod).isManifold_singleton
    (nativePeriodChart_source τ₀ hperiod)
  let E : ℍ ≃ₜ T := Classical.choose hperiod
  have hchart : ContMDiff RI RI ∞ (((↑) : ℍ → ℂ) ∘ E.symm) := by
    intro q
    change ContMDiffAt RI RI ∞ (extChartAt RI q) q
    exact contMDiffAt_extChartAt
  have hp : ContMDiff RI RI ∞ E.symm :=
    hchart.of_comp_isOpenEmbedding UpperHalfPlane.isOpenEmbedding_coe
  have hG : ContMDiff RI 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
      (fun q : T => parameterTensor (E.symm q)) := by
    simpa only [parameterTensor, Pi.smul_def', Function.comp_def] using
      (contMDiff_const (c := (1 / 2 : ℝ))).smul (I := 𝓘(ℝ))
        (Hyperbolic.contMDiff_halfPlanePoincareTensor.comp hp)
  let L : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ (u * conj v)).comp
    (Complex.ofRealCLM.comp ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ))
  have hF : ContMDiff RI RI ∞ (fun q : T => L (parameterTensor (E.symm q) 1 1)) :=
    L.contMDiff.comp ((hG.clm_apply contMDiff_const).clm_apply contMDiff_const)
  have heq (q : T) : (nativePeriodHermitianCore τ₀ hperiod q).inner
      ((nativePeriodTangentCoordinateEquiv τ₀ hperiod q).symm v)
      ((nativePeriodTangentCoordinateEquiv τ₀ hperiod q).symm u) =
        L (parameterTensor (E.symm q) 1 1) := by
    let σ := E.symm q
    let K := nativePeriodTangentCoordinateEquiv τ₀ hperiod q
    change inner ℂ (K (K.symm v) * tangentBeltrami σ)
      (K (K.symm u) * tangentBeltrami σ) = _
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    rw [RCLike.inner_apply, map_mul]
    calc
      _ = (tangentBeltrami σ * conj (tangentBeltrami σ)) * u * conj v := by ring
      _ = _ := by
        rw [tangentBeltrami_mul_conj]
        change ((1 / (4 * σ.im ^ 2) : ℝ) : ℂ) * u * conj v =
          L (parameterTensor σ 1 1)
        simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
          smul_apply, ContinuousLinearMap.id_apply,
          Complex.ofRealCLM_apply, smul_eq_mul, parameterTensor_self, norm_one, one_pow]
        rw [show (1 / 2 : ℝ) * (1 / (2 * σ.im ^ 2)) = 1 / (4 * σ.im ^ 2) by
          field_simp [σ.im_ne_zero]; ring]
        ring
  intro q
  exact (hF q).congr_of_eventuallyEq (Filter.Eventually.of_forall heq)

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
