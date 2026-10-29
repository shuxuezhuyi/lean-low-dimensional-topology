module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSesquilinearAbsolute
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Continuity in the second original mixed-kernel point

On a fixed small neighbourhood of an actual upper point, its Cauchy-square
factor is bounded by four times the same factor at the centre. The already
proved product absolute integral gives a literal integrable dominator.
Dominated convergence therefore applies to the original ordinary integral.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

private theorem opposite_difference_ne_zero (η z : ℍ) :
    (η : ℂ) - conj (z : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im, UpperHalfPlane.coe_im] at hi
  linarith [η.im_pos, z.im_pos]

private theorem crossKernel_continuous (η : ℍ) :
    Continuous (fun z : ℍ => cauchySquare η (conj (z : ℂ))) := by
  unfold cauchySquare
  exact continuous_const.div
    ((continuous_const.sub (Complex.continuous_conj.comp UpperHalfPlane.continuous_coe)).pow 2)
    (fun z => pow_ne_zero 2 (opposite_difference_ne_zero η z))

private theorem crossKernel_local_bound (η z₀ z : ℍ)
    (hz : ‖(z : ℂ) - (z₀ : ℂ)‖ < z₀.im / 2) :
    ‖cauchySquare η (conj (z : ℂ))‖ ≤
      4 * ‖cauchySquare η (conj (z₀ : ℂ))‖ := by
  have hlow : z₀.im ≤ ‖(η : ℂ) - conj (z₀ : ℂ)‖ := by
    have hi := Complex.im_le_norm ((η : ℂ) - conj (z₀ : ℂ))
    simp only [Complex.sub_im, Complex.conj_im, UpperHalfPlane.coe_im] at hi
    linarith [η.im_pos]
  have ht := norm_add_le ((η : ℂ) - conj (z : ℂ))
    (conj (z : ℂ) - conj (z₀ : ℂ))
  have he : ((η : ℂ) - conj (z : ℂ)) + (conj (z : ℂ) - conj (z₀ : ℂ)) =
      (η : ℂ) - conj (z₀ : ℂ) := by ring
  have hd : ‖conj (z : ℂ) - conj (z₀ : ℂ)‖ = ‖(z : ℂ) - (z₀ : ℂ)‖ := by
    rw [← map_sub, Complex.norm_conj]
  rw [he, hd] at ht
  have hn : ‖(η : ℂ) - conj (z₀ : ℂ)‖ ≤ 2 * ‖(η : ℂ) - conj (z : ℂ)‖ := by
    linarith
  have hs : ‖(η : ℂ) - conj (z₀ : ℂ)‖ ^ 2 ≤
      4 * ‖(η : ℂ) - conj (z : ℂ)‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith only [h]
  have hp := norm_pos_iff.mpr (opposite_difference_ne_zero η z)
  have hp₀ := norm_pos_iff.mpr (opposite_difference_ne_zero η z₀)
  have hrat : 1 / ‖(η : ℂ) - conj (z : ℂ)‖ ^ 2 ≤
      4 / ‖(η : ℂ) - conj (z₀ : ℂ)‖ ^ 2 :=
    (div_le_div_iff₀ (sq_pos_of_pos hp) (sq_pos_of_pos hp₀)).2 (by simpa using hs)
  simpa only [cauchySquare, norm_div, norm_one, norm_inv, norm_pow, div_eq_mul_inv, one_mul] using hrat

/-- The second upper argument of the unchanged mixed integral is continuous
for the actual chosen L-infinity representatives. -/
theorem sesquilinear_continuous_right
    (b c : GammaMeasurableBeltrami.Ambient) (ζ : ℍ) :
    Continuous (fun z : ℍ => sesquilinear (fun η => b η) (fun ξ => c ξ) ζ z) := by
  let : SigmaFinite flatArea := by
    apply SigmaFinite.of_map flatArea UpperHalfPlane.measurableEmbedding_coe.measurable.aemeasurable
    rw [GammaMeasurableBeltrami.map_flat_coe]
    infer_instance
  have heq : (fun z : ℍ => sesquilinear (fun η => b η) (fun ξ => c ξ) ζ z) =
      fun z => ∫ p : ℍ × ℍ,
        sesquilinearIntegrand (fun η => b η) (fun ξ => c ξ) ζ z p.1 p.2
          ∂(flatArea.prod flatArea) := by
    funext z
    exact (integral_prod _ (sesquilinear_joint_integrable b c ζ z)).symm
  rw [heq]
  apply continuous_iff_continuousAt.2
  intro z₀
  have hnear : ∀ᶠ z : ℍ in 𝓝 z₀, ‖(z : ℂ) - (z₀ : ℂ)‖ < z₀.im / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      (UpperHalfPlane.continuous_coe.tendsto z₀).eventually
        (Metric.ball_mem_nhds (z₀ : ℂ) (half_pos z₀.im_pos))
  apply continuousAt_of_dominated
    (bound := fun p : ℍ × ℍ =>
      4 * ‖sesquilinearIntegrand (fun η => b η) (fun ξ => c ξ) ζ z₀ p.1 p.2‖)
  · exact Eventually.of_forall fun z => (sesquilinear_joint_integrable b c ζ z).aestronglyMeasurable
  · filter_upwards [hnear] with z hz
    exact Eventually.of_forall fun p => by
      have hk := crossKernel_local_bound p.2 z₀ z hz
      have hn : 0 ≤ ‖cauchySquare (conj (p.1 : ℂ)) ζ‖ *
          ‖cauchySquare (conj (p.1 : ℂ)) p.2‖ * ‖b p.2‖ * ‖c p.1‖ := by positivity
      simp only [sesquilinearIntegrand, norm_mul, Complex.norm_conj]
      nlinarith only [mul_le_mul_of_nonneg_left hk hn]
  · exact (sesquilinear_joint_integrable b c ζ z₀).norm.const_mul 4
  · exact Eventually.of_forall fun p => by
      unfold sesquilinearIntegrand
      exact (((continuous_const.mul (crossKernel_continuous p.2)).mul continuous_const).mul
        continuous_const).continuousAt

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

/-- The original native harmonic mixed kernels have the genuine point
continuity used by the diagonal argument, with every source direction fixed. -/
theorem nativeWeilPetersson_sesquilinear_continuous_right
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (u v : E) (ζ : ℍ) :
    Continuous (fun z : ℍ => SourceKernel.sesquilinear (μ ν P F hF u) (μ ν P F hF v) ζ z) := by
  let := C
  let b : Ambient := (TH ν P F hF hsmooth ((K (β ν.val)).symm u)).val.val
  let c : Ambient := (TH ν P F hF hsmooth ((K (β ν.val)).symm v)).val.val
  exact SourceKernel.sesquilinear_continuous_right b c ζ

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
