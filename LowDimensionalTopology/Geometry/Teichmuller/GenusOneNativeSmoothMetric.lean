module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneNativeSmoothSections
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.QuadraticFormMetric
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! # The smooth native period metric and the positive fundamental-form coefficient -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Bornology Set
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces
variable (τ₀ : ℍ) (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀)
local notation "RI" => 𝓘(ℝ, ℂ)
local notation "C" => nativePeriodChartedSpace τ₀ hperiod

/-- The original real tensor is a smooth Riemannian metric in the original fibre topology. -/
theorem exists_nativePeriodSmoothRealMetric :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :=
      (nativePeriodChart τ₀ hperiod).isManifold_singleton
      (nativePeriodChart_source τ₀ hperiod)
    ∃ G : Bundle.ContMDiffRiemannianMetric RI ∞ ℂ
        (fun q : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) => TangentSpace RI q),
      ∀ (q : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) (v w : TangentSpace RI q),
        G.inner q v w = nativePeriodRealTensor τ₀ hperiod q v w := by
  let := C
  let T := TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)
  let : IsManifold RI ω T := (nativePeriodChart τ₀ hperiod).isManifold_singleton
    (nativePeriodChart_source τ₀ hperiod)
  let E : ℍ ≃ₜ T := Classical.choose hperiod
  let K (q : T) : TangentSpace RI q ≃L[ℝ] ℂ :=
    ((mdifferentiable_chart (I := RI) q).mfderiv (mem_chart_source ℂ q)).trans
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (nativePeriodChart τ₀ hperiod q))
  refine ⟨{ inner := nativePeriodRealTensor τ₀ hperiod
            symm := ?_, pos := ?_, isVonNBounded := ?_
            contMDiff := (contMDiff_nativePeriodRealTensor_and_fundamentalForm τ₀ hperiod).1 },
    fun _ _ _ => rfl⟩
  · intro q v w
    change (1 / 2 : ℝ) * Hyperbolic.halfPlanePoincareTensor (E.symm q) (K q v) (K q w) =
      (1 / 2 : ℝ) * Hyperbolic.halfPlanePoincareTensor (E.symm q) (K q w) (K q v)
    rw [Hyperbolic.halfPlanePoincareTensor_symmetric]
  · intro q v hv
    change 0 < parameterTensor (E.symm q) (K q v) (K q v)
    exact parameterTensor_pos _ ((K q).toLinearEquiv.map_ne_zero_iff.mpr hv)
  · intro q
    have hB := Auxiliary.Analysis.quadraticForm_isVonNBounded (parameterTensor (E.symm q))
      (fun v hv => parameterTensor_pos _ hv)
    apply (hB.image (K q).symm.toContinuousLinearMap).subset
    intro v hv
    refine ⟨K q v, ?_, (K q).symm_apply_apply v⟩
    exact hv

/-- The original real fundamental form has the positive complex-coordinate coefficient. -/
theorem nativePeriodFundamentalForm_complex_coefficient (τ : ℍ) :
    letI := C
    let q₀ := normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))
    let dτ : TangentSpace RI q₀ → ℂ := fun v =>
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (nativePeriodChart τ₀ hperiod q₀))
        (mfderiv RI RI (nativePeriodChart τ₀ hperiod) q₀ v)
    ∀ v w : TangentSpace RI q₀,
      ((nativePeriodFundamentalForm τ₀ hperiod q₀ ![v, w] : ℝ) : ℂ) =
        Complex.I / (4 * (τ.im : ℂ) ^ 2) *
          (dτ v * conj (dτ w) - dτ w * conj (dτ v)) := by
  let := C
  dsimp only
  intro v w
  rw [(nativePeriodRealTensor_form_at_period τ₀ hperiod τ v w).2.2.1,
    parameterTensor_apply, pairing_eq]
  rw [show (4 * (τ.im : ℂ) ^ 2) = ((4 * τ.im ^ 2 : ℝ) : ℂ) by push_cast; rfl]
  apply Complex.ext <;>
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, Complex.sub_re,
      Complex.sub_im, Complex.div_ofReal_re, Complex.div_ofReal_im] <;>
    field_simp [τ.im_ne_zero] <;> ring

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
