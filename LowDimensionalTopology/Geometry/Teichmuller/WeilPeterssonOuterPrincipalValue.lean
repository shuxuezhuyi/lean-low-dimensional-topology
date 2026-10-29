module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonInnerL2Identification
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Tactic.Linarith

/-!
# The original outer principal value at the lower conjugated point

The actual outer input is in planar L² and is identically zero below the
real axis. A fixed truncation therefore gives an absolutely integrable full
kernel at every lower point. All sufficiently small truncations equal that
ordinary integral, whose limit is the existing Hilbert principal value.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology Metric
open scoped ComplexConjugate UpperHalfPlane Manifold ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open LiZhongQC GammaMeasurableBeltrami Surfaces

private theorem principalValueExists_of_memLp_zero_on_ball
    (f : ℂ → ℂ) (hLp : MemLp f 2 (volume : Measure ℂ)) (ξ : ℂ)
    {ε : ℝ} (hε : 0 < ε) (hzero : ∀ η ∈ ball ξ ε, f η = 0) :
    PrincipalValueExists f ξ := by
  let S : Set ℂ := {η | ε / 2 < ‖η - ξ‖}
  have hS : MeasurableSet S :=
    measurableSet_lt measurable_const (measurable_id.sub_const ξ).norm
  have hcut : IntegrableOn (fun η => f η / (η - ξ) ^ 2) S (volume : Measure ℂ) :=
    integrableOn_truncated_kernel (p := 2) (by norm_num)
      (by simpa only [ofReal_two_eq] using hLp) ξ (by positivity : 0 < ε / 2)
  have heq : S.indicator (fun η => f η / (η - ξ) ^ 2) =
      fun η => f η / (η - ξ) ^ 2 := by
    funext η
    by_cases hη : ε / 2 < ‖η - ξ‖
    · rw [indicator_of_mem (show η ∈ S from hη)]
    · have hn : ‖η - ξ‖ ≤ ε / 2 := not_lt.mp hη
      have hball : η ∈ ball ξ ε := by
        rw [mem_ball, dist_eq_norm]
        linarith
      rw [indicator_of_notMem (show η ∉ S from hη), hzero η hball, zero_div]
  have hfull : Integrable (fun η => f η / (η - ξ) ^ 2) (volume : Measure ℂ) := by
    simpa only [heq] using hcut.integrable_indicator hS
  refine ⟨fun _ _ => hfull.integrableOn, ?_⟩
  have hlim : Tendsto (fun r : ℝ => -(1 / (Real.pi : ℂ)) *
      ∫ η in {η : ℂ | r < ‖η - ξ‖}, f η / (η - ξ) ^ 2)
      (𝓝[>] 0) (𝓝 (-(1 / (Real.pi : ℂ)) * ∫ η, f η / (η - ξ) ^ 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr
    congr 1
    have he := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (f := fun η => f η / (η - ξ) ^ 2) (μ := (volume : Measure ℂ))
      MeasurableSet.univ (subset_univ {η : ℂ | r < ‖η - ξ‖}) (fun η hη => by
        have hn : ‖η - ξ‖ ≤ r := not_lt.mp hη.2
        rw [hzero η (by rw [mem_ball, dist_eq_norm]; exact hn.trans_lt hr.2), zero_div])
    simpa only [setIntegral_univ] using he
  have he : hilbertHSmooth f ξ =
      -(1 / (Real.pi : ℂ)) * ∫ η, f η / (η - ξ) ^ 2 := hlim.limUnder_eq
  rwa [he]

/-- The same harmonic outer input has its complete principal-value limit at
every original lower conjugated point, with all punctured integrals absolute. -/
theorem outerInput_ofQuadratic_principalValueExists
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (b : GammaMeasurableBeltrami.Ambient)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z ζ : ℍ) :
    PrincipalValueExists
      (outerInput (fun ξ => b ξ)
        (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z)
      (conj (ζ : ℂ)) := by
  let f := outerInput (fun ξ => b ξ)
    (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z
  have hLp : MemLp f 2 (volume : Measure ℂ) :=
    outerInput_ofQuadratic_memLp_two R hp b q z
  have hzero : ∀ η ∈ ball (conj (ζ : ℂ)) (ζ.im / 2), f η = 0 := by
    intro η hη
    have hn : ‖η - conj (ζ : ℂ)‖ < ζ.im / 2 := by
      simpa only [mem_ball, dist_eq_norm] using hη
    have hi : η.im + ζ.im ≤ ‖η - conj (ζ : ℂ)‖ := by
      calc
        η.im + ζ.im = (η - conj (ζ : ℂ)).im := by
          simp only [sub_im, conj_im, UpperHalfPlane.coe_im, sub_neg_eq_add]
        _ ≤ |(η - conj (ζ : ℂ)).im| := le_abs_self _
        _ ≤ ‖η - conj (ζ : ℂ)‖ := Complex.abs_im_le_norm _
    have hnot : ¬0 < η.im := by linarith [ζ.im_pos]
    simp only [f, outerInput, upperExtension, hnot, dite_false]
  exact principalValueExists_of_memLp_zero_on_ball f hLp (conj (ζ : ℂ))
    (by positivity : 0 < ζ.im / 2) hzero

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

/-- The actual native source directions have the original lower outer
principal value at every point, with the same coefficient and genuine region. -/
theorem nativeWeilPetersson_outer_principalValueExists
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (u v : E) (z ζ : ℍ) :
    SourceKernel.PrincipalValueExists
      (SourceKernel.outerInput
        (nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth ν P F hF u)
        (nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth ν P F hF v) z)
      (conj (ζ : ℂ)) := by
  let := C
  let bu := TH ν P F hF hsmooth ((K (β ν.val)).symm u)
  let bv := TH ν P F hF hsmooth ((K (β ν.val)).symm v)
  rcases (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic
    (deformedNativeSurface R hgenus hΓ hp ν) P (deformedTargetCover R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) F hF bv.val).mp bv.property with ⟨q, hq⟩
  have h := SourceKernel.outerInput_ofQuadratic_principalValueExists
    (deformedNativeSurface R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) bu.val.val q z ζ
  rw [hq] at h
  exact h

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
