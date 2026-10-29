module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCrossKernelCovariance
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSesquilinearAbsolute
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The actual absolute diagonal mass has inverse squared-height scaling

The two-variable integral is absolutely convergent by the proved mixed-kernel
estimate applied to the actual L-infinity class of the constant one function.
The existing hyperbolic density converts its squared-height kernel to the
same flat-area integral. Actual special-linear measure preservation and the
canonical map taking i to the given point determine its exact scaling.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open GammaMeasurableBeltrami

private def diagonalAbsoluteDensity (ζ : ℍ) (p : ℍ × ℍ) : ℝ :=
  p.1.im ^ 2 * p.2.im ^ 2 * diagonalCrossAbsolute ζ p.1 p.2

private theorem diagonalAbsoluteDensity_integral (ζ : ℍ) :
    (∫ p : ℍ × ℍ, diagonalAbsoluteDensity ζ p ∂((volume : Measure ℍ).prod volume)) =
      ∫ p : ℍ × ℍ, diagonalCrossAbsolute ζ p.1 p.2 ∂(flatArea.prod flatArea) := by
  let ρ : ℍ × ℍ → ℝ≥0∞ := fun p => hyperbolicDensity p.1 * hyperbolicDensity p.2
  have hρ : Measurable ρ :=
    (measurable_hyperbolicDensity.comp measurable_fst).mul
      (measurable_hyperbolicDensity.comp measurable_snd)
  have hρfin (p : ℍ × ℍ) : ρ p < ⊤ := by
    exact ENNReal.mul_lt_top (by simp [hyperbolicDensity]) (by simp [hyperbolicDensity])
  have hvol : (volume : Measure ℍ).prod volume = (flatArea.prod flatArea).withDensity ρ := by
    change (flatArea.withDensity hyperbolicDensity).prod (flatArea.withDensity hyperbolicDensity) = _
    exact MeasureTheory.prod_withDensity measurable_hyperbolicDensity measurable_hyperbolicDensity
  rw [hvol, integral_withDensity_eq_integral_toReal_smul hρ (Eventually.of_forall hρfin)]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    simp only [ρ, ENNReal.toReal_mul, hyperbolicDensity, ENNReal.coe_toReal,
      NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk,
      smul_eq_mul, diagonalAbsoluteDensity]
    field_simp [p.1.im_ne_zero, p.2.im_ne_zero]

private theorem diagonalAbsoluteDensity_mass_smul (γ : Deck) (ζ : ℍ) :
    (γ • ζ : ℍ).im ^ 2 *
        (∫ p : ℍ × ℍ, diagonalAbsoluteDensity (γ • ζ) p
          ∂((volume : Measure ℍ).prod volume)) =
      ζ.im ^ 2 * ∫ p : ℍ × ℍ, diagonalAbsoluteDensity ζ p
        ∂((volume : Measure ℍ).prod volume) := by
  have hmp : MeasurePreserving (fun p : ℍ × ℍ => γ • p)
      ((volume : Measure ℍ).prod volume) ((volume : Measure ℍ).prod volume) :=
    (measurePreserving_deck γ).prod (measurePreserving_deck γ)
  calc
    _ = ∫ p : ℍ × ℍ, (γ • ζ : ℍ).im ^ 2 * diagonalAbsoluteDensity (γ • ζ) p
        ∂((volume : Measure ℍ).prod volume) := (integral_const_mul _ _).symm
    _ = ∫ p : ℍ × ℍ, (γ • ζ : ℍ).im ^ 2 * diagonalAbsoluteDensity (γ • ζ) (γ • p)
        ∂((volume : Measure ℍ).prod volume) :=
      (hmp.integral_comp (measurableEmbedding_const_smul γ) _).symm
    _ = ∫ p : ℍ × ℍ, ζ.im ^ 2 * diagonalAbsoluteDensity ζ p
        ∂((volume : Measure ℍ).prod volume) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        simpa only [diagonalAbsoluteDensity, Prod.smul_fst, Prod.smul_snd, mul_assoc] using
          diagonalCrossAbsolute_density_smul γ ζ p.1 p.2
    _ = _ := integral_const_mul _ _

/-- The actual diagonal triple cross-kernel has a finite absolute product
integral at every upper point, and its mass is exactly its mass at i divided
by the squared height of that same point. -/
theorem diagonalCrossAbsolute_integrable_and_mass (ζ : ℍ) :
    Integrable (fun p : ℍ × ℍ => diagonalCrossAbsolute ζ p.1 p.2)
      (flatArea.prod flatArea) ∧
    (∫ p : ℍ × ℍ, diagonalCrossAbsolute ζ p.1 p.2 ∂(flatArea.prod flatArea)) =
      (∫ p : ℍ × ℍ, diagonalCrossAbsolute UpperHalfPlane.I p.1 p.2
        ∂(flatArea.prod flatArea)) / ζ.im ^ 2 := by
  have hi : Integrable (fun p : ℍ × ℍ => diagonalCrossAbsolute ζ p.1 p.2)
      (flatArea.prod flatArea) := by
    let b : Ambient := (memLp_top_const (1 : ℂ)).toLp (fun _ : ℍ => (1 : ℂ))
    have hb : (fun η : ℍ => b η) =ᵐ[flatArea] fun _ => (1 : ℂ) :=
      ae_hyperbolic_iff.mp (memLp_top_const (1 : ℂ)).coeFn_toLp
    have he : (fun p : ℍ × ℍ => sesquilinearIntegrand
        (fun η => b η) (fun ξ => b ξ) ζ ζ p.1 p.2) =ᵐ[flatArea.prod flatArea]
        fun p => cauchySquare (conj (p.1 : ℂ)) ζ *
          cauchySquare (conj (p.1 : ℂ)) p.2 * cauchySquare p.2 (conj (ζ : ℂ)) := by
      filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := flatArea) (ν := flatArea)).ae hb,
        (Measure.quasiMeasurePreserving_fst (μ := flatArea) (ν := flatArea)).ae hb]
        with p hp hq
      simp only [sesquilinearIntegrand, hp, hq, map_one, mul_one]
    exact ((sesquilinear_joint_integrable b b ζ ζ).congr he).norm
  refine ⟨hi, ?_⟩
  have hs := diagonalAbsoluteDensity_mass_smul ζ.toSL2R UpperHalfPlane.I
  simp only [UpperHalfPlane.toSL2R_smul_I, UpperHalfPlane.I_im, one_pow, one_mul] at hs
  rw [diagonalAbsoluteDensity_integral, diagonalAbsoluteDensity_integral] at hs
  apply (eq_div_iff (pow_ne_zero 2 ζ.im_ne_zero)).2
  simpa only [mul_comm] using hs

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
