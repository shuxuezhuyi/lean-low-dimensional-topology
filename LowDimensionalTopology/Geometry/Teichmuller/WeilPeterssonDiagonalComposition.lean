module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCauchySquareComposition
public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicBeltrami
public import Mathlib.Tactic.FieldSimp

/-!
# The actual diagonal composition followed by quadratic reproduction

The first ordinary upper integral is the same proved Cauchy-square
composition, after its even-kernel symmetry. The remaining integral is
exactly the existing upper-half-plane quadratic reproducing formula for
the actual original differential, with its full normalization retained.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open Surfaces GammaMeasurableBeltrami QuadraticBergman

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (p : ℍ → X) {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

private theorem cauchySquare_symm (z w : ℂ) : cauchySquare z w = cauchySquare w z := by
  unfold cauchySquare
  congr 1
  ring

private theorem diagonal_inner_composition
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) (ξ η : ℍ) :
    (∫ ζ : ℍ, sesquilinearIntegrand (NativeHarmonicBeltrami.coefficient R p q)
      (NativeHarmonicBeltrami.coefficient R p r) ζ ζ ξ η ∂flatArea) =
      -(Real.pi : ℂ) * NativeHarmonicBeltrami.coefficient R p q η *
        (cauchySquare (conj (ξ : ℂ)) η ^ 2 *
          conj (NativeHarmonicBeltrami.coefficient R p r ξ)) := by
  have hc := (cauchySquare_composition η ξ).2
  rw [← GammaMeasurableBeltrami.map_flat_coe,
    UpperHalfPlane.measurableEmbedding_coe.integral_map] at hc
  have he (ζ : ℍ) : sesquilinearIntegrand (NativeHarmonicBeltrami.coefficient R p q)
      (NativeHarmonicBeltrami.coefficient R p r) ζ ζ ξ η =
      (cauchySquare (conj (ξ : ℂ)) η * NativeHarmonicBeltrami.coefficient R p q η *
        conj (NativeHarmonicBeltrami.coefficient R p r ξ)) *
        (cauchySquare (conj (ζ : ℂ)) η * cauchySquare ζ (conj (ξ : ℂ))) := by
    unfold sesquilinearIntegrand
    rw [cauchySquare_symm (conj (ξ : ℂ)) ζ, cauchySquare_symm η (conj (ζ : ℂ))]
    ring
  rw [integral_congr_ae (Eventually.of_forall he), integral_const_mul, hc,
    cauchySquare_symm (η : ℂ) (conj (ξ : ℂ))]
  ring

include hp in
private theorem diagonal_quadratic_reproduction
    (r : HolomorphicQuadraticDifferential R.toRiemannAtlas) (η : ℍ) :
    Integrable (fun ξ : ℍ => cauchySquare (conj (ξ : ℂ)) η ^ 2 *
      conj (NativeHarmonicBeltrami.coefficient R p r ξ)) flatArea ∧
    (∫ ξ : ℍ, cauchySquare (conj (ξ : ℂ)) η ^ 2 *
      conj (NativeHarmonicBeltrami.coefficient R p r ξ) ∂flatArea) =
        (Real.pi / 12 : ℂ) * uniformizedQuadratic R p r (η : ℂ) := by
  have h := uniformizedQuadratic_reproducing R p hp r (η : ℂ) η.im_pos
  have hiPlane := h.1
  have hrep := h.2
  change Integrable _ ((volume : Measure ℂ).restrict LiZhongQC.upperHalf) at hiPlane
  rw [← GammaMeasurableBeltrami.map_flat_coe] at hiPlane hrep
  have hiFlat := UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mp hiPlane
  rw [UpperHalfPlane.measurableEmbedding_coe.integral_map] at hrep
  have hi : Integrable (fun ξ : ℍ =>
      (ξ.im : ℂ) ^ 2 * uniformizedQuadratic R p r (ξ : ℂ) /
        (conj (ξ : ℂ) - (η : ℂ)) ^ 4) flatArea := by
    simpa only [Function.comp_def, UpperHalfPlane.coe_im,
      GammaMeasurableBeltrami.flatMeasure, WeilPetersson.flatArea] using hiFlat
  have he (ξ : ℍ) : cauchySquare (conj (ξ : ℂ)) η ^ 2 *
      conj (NativeHarmonicBeltrami.coefficient R p r ξ) =
      (ξ.im : ℂ) ^ 2 * uniformizedQuadratic R p r (ξ : ℂ) /
        (conj (ξ : ℂ) - (η : ℂ)) ^ 4 := by
    rw [NativeHarmonicBeltrami.coefficient_eq_uniformized]
    simp only [map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj, cauchySquare]
    field_simp [LiZhongQC.h36p_c_conj_sub_ne ξ.im_pos η.im_pos]
  have hkernel : Integrable (fun ξ : ℍ => cauchySquare (conj (ξ : ℂ)) η ^ 2 *
      conj (NativeHarmonicBeltrami.coefficient R p r ξ)) flatArea :=
    hi.congr (Eventually.of_forall fun ξ => (he ξ).symm)
  refine ⟨hkernel, ?_⟩
  have hj : uniformizedQuadratic R p r (η : ℂ) = (12 / Real.pi : ℂ) *
      ∫ ξ : ℍ, cauchySquare (conj (ξ : ℂ)) η ^ 2 *
        conj (NativeHarmonicBeltrami.coefficient R p r ξ) ∂flatArea := by
    rw [integral_congr_ae (Eventually.of_forall he)]
    simpa only [Function.comp_apply, UpperHalfPlane.coe_im] using hrep
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  calc
    _ = (Real.pi / 12 : ℂ) * ((12 / Real.pi : ℂ) *
        ∫ ξ : ℍ, cauchySquare (conj (ξ : ℂ)) η ^ 2 *
          conj (NativeHarmonicBeltrami.coefficient R p r ξ) ∂flatArea) := by
      field_simp [hπ]
    _ = _ := by rw [← hj]

include hp in
/-- The two actual ordinary integrals give the original quadratic
coefficient with the exact negative squared-pi normalization. -/
theorem harmonic_diagonal_composed_integral
    (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) (η : ℍ) :
    Integrable (fun ξ : ℍ => ∫ ζ : ℍ,
      sesquilinearIntegrand (NativeHarmonicBeltrami.coefficient R p q)
        (NativeHarmonicBeltrami.coefficient R p r) ζ ζ ξ η ∂flatArea) flatArea ∧
    (∫ ξ : ℍ, ∫ ζ : ℍ,
      sesquilinearIntegrand (NativeHarmonicBeltrami.coefficient R p q)
        (NativeHarmonicBeltrami.coefficient R p r) ζ ζ ξ η ∂flatArea ∂flatArea) =
      (-(Real.pi ^ 2 / 12) : ℂ) * NativeHarmonicBeltrami.coefficient R p q η *
        uniformizedQuadratic R p r (η : ℂ) := by
  have h := diagonal_quadratic_reproduction R p hp r η
  constructor
  · exact (h.1.const_mul (-(Real.pi : ℂ) * NativeHarmonicBeltrami.coefficient R p q η)).congr
      (Eventually.of_forall fun ξ => (diagonal_inner_composition R p q r ξ η).symm)
  · simp_rw [diagonal_inner_composition R p q r]
    rw [integral_const_mul, h.2]
    ring

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
