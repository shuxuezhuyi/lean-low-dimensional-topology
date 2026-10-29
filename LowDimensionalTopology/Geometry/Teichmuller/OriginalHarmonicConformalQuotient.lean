module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicBiparameterFamily
public import LowDimensionalTopology.Geometry.Quasiconformal.BeltramiConformal
public import Mathlib.Tactic.Linarith

/-! # Parameter derivatives on the actual harmonic conformal quotient -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

/-- The actual same-coefficient relative map is conformal on its actual
image domain. Its spatial derivatives are holomorphic in the independent
lower-half-plane parameter, with genuine local uniform bounds. -/
theorem canonicalBiparameterFamily_conformal_quotient
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℂ, ‖s‖ < ε →
      let A := canonicalBiparameterFamily R p q s 0
      let D := A '' upperHalf
      let G := fun t => canonicalBiparameterFamily R p q s t ∘
        Function.invFunOn A upperHalf
      (∀ t ∈ ball (0 : ℂ) ε,
        IsConformalOnto (G t) D (canonicalBiparameterFamily R p q s t '' upperHalf)) ∧
      ∀ n : ℕ,
        (∀ w ∈ D, DifferentiableOn ℂ (fun t => iteratedDeriv n (G t) w) (ball 0 ε)) ∧
        (∀ t ∈ ball (0 : ℂ) ε, DifferentiableOn ℂ (iteratedDeriv n (G t)) D) ∧
        (∀ t₀ ∈ ball (0 : ℂ) ε, ∀ w₀ ∈ D, ∃ δ > 0,
          ball t₀ δ ⊆ ball (0 : ℂ) ε ∧ ball w₀ δ ⊆ D ∧
          ∃ M : ℝ, ∀ t ∈ ball t₀ δ, ∀ w ∈ ball w₀ δ,
            ‖iteratedDeriv n (G t) w‖ ≤ M) := by
  obtain ⟨ε, hε, hspec, _, hsecond⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  refine ⟨ε, hε, ?_⟩
  intro s hs
  dsimp only
  let A := canonicalBiparameterFamily R p q s 0
  let D := A '' upperHalf
  let G := fun t => canonicalBiparameterFamily R p q s t ∘
    Function.invFunOn A upperHalf
  have hzero : ‖(0 : ℂ)‖ < ε := by simpa only [norm_zero] using hε
  have hsol (t : ℂ) (ht : ‖t‖ < ε) := (hspec s t hs ht).2
  have hsharp (t : ℂ) (ht : ‖t‖ < ε) :
      IsKQCNormalizedPlane (canonicalBiparameterFamily R p q s t) 3 := by
    obtain ⟨f, _, hK, huniq⟩ := thm13_7_normalized_existence
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      (hspec s t hs ht).1
    have heq := huniq _ (hsol t ht)
    refine ⟨?_, (hsol t ht).2.1, (hsol t ht).2.2.1, (hsol t ht).2.2.2.1⟩
    rw [heq]
    simpa only [show (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) = 3 by norm_num] using hK
  have hA : IsKQC A upperHalf 3 :=
    ac_t_isKQC_restrict (hsharp 0 hzero).1 isOpen_upperHalf (subset_univ _)
  have hD : IsOpen D := isOpen_image_of_isKQC hA
  have hdil (t : ℂ) (ht : ‖t‖ < ε) :
      complexDilatation (canonicalBiparameterFamily R p q s t)
        =ᵐ[volume.restrict upperHalf] fun z => s * harmonicPlane R p q z := by
    filter_upwards [ae_restrict_of_ae (hsol t ht).2.2.2.2,
      ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz hzH
    rw [hz, harmonicBiparameterCoefficient, ite_eq_right (not_lt.mpr (le_of_lt hzH))]
  have hconf (t : ℂ) (ht : t ∈ ball (0 : ℂ) ε) :
      IsConformalOnto (G t) D
        (canonicalBiparameterFamily R p q s t '' upperHalf) :=
    Quasiconformal.common_beltrami_coefficient_relative_conformal hA
      (ac_t_isKQC_restrict (hsharp t (mem_ball_zero_iff.mp ht)).1
        isOpen_upperHalf (subset_univ _)) (hdil 0 hzero) (hdil t (mem_ball_zero_iff.mp ht))
  have ha : ∀ w ∈ D, DifferentiableOn ℂ (fun t => G t w) (ball 0 ε) := by
    intro w _
    exact hsecond s hs (Function.invFunOn A upperHalf w)
  have hb : ∀ t ∈ ball (0 : ℂ) ε, DifferentiableOn ℂ (G t) D :=
    fun t ht => (hconf t ht).1
  have hi : ContinuousOn (Function.invFunOn A upperHalf) D :=
    (thm7_2_inv hA).2.2.1.1
  have hc : ∀ t₀ ∈ ball (0 : ℂ) ε, ∀ w₀ ∈ D, ∃ δ > 0,
      ball t₀ δ ⊆ ball (0 : ℂ) ε ∧ ball w₀ δ ⊆ D ∧
        ∃ M : ℝ, ∀ t ∈ ball t₀ δ, ∀ w ∈ ball w₀ δ, ‖G t w‖ ≤ M := by
    intro t₀ ht₀ w₀ hw₀
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_ball t₀ ht₀
    let x₀ := Function.invFunOn A upperHalf w₀
    have hcont : ContinuousAt (Function.invFunOn A upperHalf) w₀ :=
      hi.continuousAt (hD.mem_nhds hw₀)
    have hnear : (Function.invFunOn A upperHalf) ⁻¹' ball x₀ 1 ∈ 𝓝 w₀ :=
      hcont.preimage_mem_nhds (ball_mem_nhds x₀ zero_lt_one)
    obtain ⟨d, hd, hdsub⟩ := Metric.mem_nhds_iff.mp
      (inter_mem hnear (hD.mem_nhds hw₀))
    refine ⟨min r d, lt_min hr hd,
      (ball_subset_ball (min_le_left _ _)).trans hrsub, ?_,
      lambdaInv (3 * quadLambda (‖x₀‖ + 1)), ?_⟩
    · intro w hw
      exact (hdsub ((ball_subset_ball (min_le_right _ _)) hw)).2
    · intro t ht w hw
      have htε : t ∈ ball (0 : ℂ) ε :=
        hrsub ((ball_subset_ball (min_le_left _ _)) ht)
      have hwx : Function.invFunOn A upperHalf w ∈ ball x₀ 1 :=
        (hdsub ((ball_subset_ball (min_le_right _ _)) hw)).1
      have hn : ‖Function.invFunOn A upperHalf w‖ ≤ ‖x₀‖ + 1 := by
        rw [mem_ball, dist_eq_norm] at hwx
        linarith [norm_sub_norm_le (Function.invFunOn A upperHalf w) x₀]
      exact UniversalTeichmuller.ut2_nb_upper
        (hsharp t (mem_ball_zero_iff.mp htε)) (by positivity) hn
  refine ⟨hconf, ?_⟩
  intro n
  exact bB_h0_iteratedDeriv hD ha hb hc n

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
