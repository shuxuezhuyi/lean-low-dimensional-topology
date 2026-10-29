module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCauchySquareComposition
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# The ordinary inner integral of the actual mixed WP kernel

The actual source directions are the existing chosen L-infinity harmonic
representatives. Their own norms give Euclidean a.e. bounds. The proved
cross-half-plane composition supplies the absolute kernel integral; bounded
multiplication gives the full ordinary inner integral at every upper point.
No PV, outer convergence, diagonal trace or second-variation premise occurs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped ComplexConjugate UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

private theorem cauchySquare_opposite_conj (ξ η : ℍ) :
    cauchySquare (conj (ξ : ℂ)) η = conj (cauchySquare (conj (η : ℂ)) ξ) := by
  simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
  congr 1
  ring

private theorem cross_kernel_integrable_flat (ξ z : ℍ) :
    Integrable (fun η : ℍ => cauchySquare (conj (η : ℂ)) ξ *
      cauchySquare η (conj (z : ℂ))) flatArea := by
  have h := (cauchySquare_composition ξ z).1
  change Integrable _ ((volume : Measure ℂ).restrict LiZhongQC.upperHalf) at h
  rw [← GammaMeasurableBeltrami.map_flat_coe] at h
  exact UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mp h

private theorem sesquilinear_inner_integrable_of_ae_bound
    (μ ν : ℍ → ℂ) (hμ : AEStronglyMeasurable μ flatArea)
    (M : ℝ) (hM : ∀ᵐ η ∂flatArea, ‖μ η‖ ≤ M) (ζ z ξ : ℍ) :
    Integrable (sesquilinearIntegrand μ ν ζ z ξ) flatArea := by
  have hk : Measurable (fun η : ℍ => cauchySquare (conj (ξ : ℂ)) η *
      cauchySquare η (conj (z : ℂ))) := by
    unfold cauchySquare
    fun_prop
  have hi : Integrable (fun η : ℍ =>
      cauchySquare (conj (ξ : ℂ)) η * cauchySquare η (conj (z : ℂ)) * μ η) flatArea := by
    refine ((cross_kernel_integrable_flat ξ z).norm.const_mul M).mono'
      (hk.aestronglyMeasurable.mul hμ) ?_
    filter_upwards [hM] with η hη
    calc
      ‖cauchySquare (conj (ξ : ℂ)) η * cauchySquare η (conj (z : ℂ)) * μ η‖ =
          ‖μ η‖ * ‖cauchySquare (conj (η : ℂ)) ξ * cauchySquare η (conj (z : ℂ))‖ := by
        rw [cauchySquare_opposite_conj, norm_mul, norm_mul, norm_mul, Complex.norm_conj]
        ring
      _ ≤ M * ‖cauchySquare (conj (η : ℂ)) ξ * cauchySquare η (conj (z : ℂ))‖ :=
        mul_le_mul_of_nonneg_right hη (norm_nonneg _)
  have he : sesquilinearIntegrand μ ν ζ z ξ = fun η : ℍ =>
      (cauchySquare (conj (ξ : ℂ)) ζ * conj (ν ξ)) *
        (cauchySquare (conj (ξ : ℂ)) η * cauchySquare η (conj (z : ℂ)) * μ η) := by
    funext η
    unfold sesquilinearIntegrand
    ring
  rw [he]
  exact hi.const_mul _

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth

/-- The mixed source kernel has its ordinary absolutely convergent inner
integral for the SAME actual native directions at every original upper point. -/
theorem nativeWeilPetersson_sesquilinear_inner_integrable
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (u v : E) (ζ z ξ : ℍ) :
    Integrable (SourceKernel.sesquilinearIntegrand
      (μ ν P F hF u) (μ ν P F hF v) ζ z ξ) flatArea := by
  let := C
  let b : Ambient := (TH ν P F hF hsmooth ((K (β ν.val)).symm u)).val.val
  have hb : AEStronglyMeasurable (fun η : ℍ => b η) flatArea :=
    (Lp.aestronglyMeasurable b).mono_ac flat_absolutelyContinuous_hyperbolic
  have hbound : ∀ᵐ η ∂flatArea, ‖b η‖ ≤ ‖b‖ :=
    ae_hyperbolic_iff.mp (lpInfinity_norm_ae_le b)
  exact SourceKernel.sesquilinear_inner_integrable_of_ae_bound
    (fun η => b η) (μ ν P F hF v) hb ‖b‖ hbound ζ z ξ

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
