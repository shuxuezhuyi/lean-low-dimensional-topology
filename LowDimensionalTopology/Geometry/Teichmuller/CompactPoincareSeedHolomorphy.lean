module

public import LowDimensionalTopology.Geometry.Teichmuller.CompactPoincareSeedTransport
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Holomorphic extension of the actual compact-domain seed

The pole-free integral seed is holomorphic on its larger disc. Its derivative
kernel is continuous on the actual compact product of the closed disc and
integration domain, giving a genuinely integrable uniform bound for complex
parameter differentiation. The original compact cover supplies all domain
data and hence an actual neighborhood of the closed unit disc.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.CompactPoincareSeed

open Surfaces LiZhongQC Hyperbolic WeightedQuadraticBergman

private def kernelDerivative (φ : ℂ → ℂ) (z ζ : ℂ) : ℂ :=
  ((ζ.im : ℂ) ^ 2 * φ ζ) *
    (4 * seedDenominator ζ z ^ 3 * (conj ζ + Complex.I)) /
      (seedDenominator ζ z ^ 4) ^ 2

private theorem kernel_hasDerivAt (φ : ℂ → ℂ) (ζ z : ℂ)
    (hpole : seedDenominator ζ z ≠ 0) :
    HasDerivAt (fun w => (ζ.im : ℂ) ^ 2 * φ ζ / seedDenominator ζ w ^ 4)
      (kernelDerivative φ z ζ) z := by
  have hL : HasDerivAt (fun w => seedDenominator ζ w) (-(conj ζ + Complex.I)) z := by
    simpa only [seedDenominator, mul_one] using
      (((hasDerivAt_id' z).const_mul (conj ζ + Complex.I)).const_sub (conj ζ - Complex.I))
  have hQ := (hasDerivAt_const z ((ζ.im : ℂ) ^ 2 * φ ζ)).div
    (hL.pow 4) (pow_ne_zero 4 hpole)
  convert hQ using 1
  simp only [kernelDerivative, Pi.pow_apply, Nat.reduceSub,
    Nat.cast_ofNat, zero_mul, zero_sub, mul_neg, neg_neg]

/-- The same literal compact-domain seed is holomorphic on every disc whose
entire closed disc has the proved pole-free kernel. -/
theorem extendedSeed_differentiableOn {F : Set ℂ} (hFC : IsCompact F)
    {φ : ℂ → ℂ} (hφ : ContinuousOn φ F) {r : ℝ}
    (hpole : ∀ ζ ∈ F, ∀ z ∈ Metric.closedBall (0 : ℂ) r, seedDenominator ζ z ≠ 0) :
    DifferentiableOn ℂ (extendedSeed F φ) (Metric.ball (0 : ℂ) r) := by
  let K : Set (ℂ × ℂ) := Metric.closedBall (0 : ℂ) r ×ˢ F
  have hKC : IsCompact K := (isCompact_closedBall (0 : ℂ) r).prod hFC
  have hL : Continuous (fun x : ℂ × ℂ => seedDenominator x.2 x.1) := by
    unfold seedDenominator
    exact ((Complex.continuous_conj.comp continuous_snd).sub continuous_const).sub
      (((Complex.continuous_conj.comp continuous_snd).add continuous_const).mul continuous_fst)
  have hN : ContinuousOn (fun x : ℂ × ℂ => (x.2.im : ℂ) ^ 2 * φ x.2) K := by
    refine ((Complex.continuous_ofReal.comp
      (Complex.continuous_im.comp continuous_snd)).pow 2).continuousOn.mul ?_
    exact hφ.comp continuous_snd.continuousOn fun x hx => hx.2
  have hB : Continuous (fun x : ℂ × ℂ => conj x.2 + Complex.I) :=
    (Complex.continuous_conj.comp continuous_snd).add continuous_const
  have hD : ContinuousOn (fun x : ℂ × ℂ => kernelDerivative φ x.1 x.2) K := by
    unfold kernelDerivative
    refine (hN.mul (((continuous_const.mul (hL.pow 3)).mul hB).continuousOn)).div
      (((hL.pow 4).pow 2).continuousOn) ?_
    intro x hx
    exact pow_ne_zero 2 (pow_ne_zero 4 (hpole x.2 hx.2 x.1 hx.1))
  obtain ⟨C, hC⟩ := hKC.exists_bound_of_continuousOn hD
  have hCint : Integrable (fun _ : ℂ => C) (volume.restrict F) :=
    ContinuousOn.integrableOn_compact hFC continuousOn_const
  have hInt (w : ℂ) (hw : w ∈ Metric.ball (0 : ℂ) r) :
      IntegrableOn (fun ζ => (ζ.im : ℂ) ^ 2 * φ ζ / seedDenominator ζ w ^ 4) F :=
    extendedSeed_integrableOn hFC hφ fun ζ hζ =>
      hpole ζ hζ w (Metric.ball_subset_closedBall hw)
  intro z hz
  have hDz : ContinuousOn (kernelDerivative φ z) F := by
    unfold kernelDerivative
    have hNζ : ContinuousOn (fun ζ : ℂ => (ζ.im : ℂ) ^ 2 * φ ζ) F :=
      ((Complex.continuous_ofReal.comp Complex.continuous_im).pow 2).continuousOn.mul hφ
    have hLζ : Continuous (fun ζ : ℂ => seedDenominator ζ z) := by
      unfold seedDenominator
      exact (Complex.continuous_conj.sub continuous_const).sub
        ((Complex.continuous_conj.add continuous_const).mul continuous_const)
    have hBζ : Continuous (fun ζ : ℂ => conj ζ + Complex.I) :=
      Complex.continuous_conj.add continuous_const
    exact (hNζ.mul (((continuous_const.mul (hLζ.pow 3)).mul hBζ).continuousOn)).div
      (((hLζ.pow 4).pow 2).continuousOn) fun ζ hζ =>
        pow_ne_zero 2 (pow_ne_zero 4 (hpole ζ hζ z (Metric.ball_subset_closedBall hz)))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict F)
    (F := fun w ζ => (ζ.im : ℂ) ^ 2 * φ ζ / seedDenominator ζ w ^ 4)
    (F' := fun w ζ => kernelDerivative φ w ζ) (x₀ := z)
    (s := Metric.ball (0 : ℂ) r) (bound := fun _ : ℂ => C)
    (Metric.isOpen_ball.mem_nhds hz)
    ((Metric.isOpen_ball.eventually_mem hz).mono fun w hw => (hInt w hw).aestronglyMeasurable)
    (hInt z hz) (hDz.aestronglyMeasurable hFC.measurableSet)
    (ae_restrict_of_forall_mem hFC.measurableSet fun ζ hζ w hw =>
      hC (w, ζ) ⟨Metric.ball_subset_closedBall hw, hζ⟩)
    hCint
    (ae_restrict_of_forall_mem hFC.measurableSet fun ζ hζ w hw =>
      kernel_hasDerivAt φ ζ w (hpole ζ hζ w (Metric.ball_subset_closedBall hw)))
  exact (key.2.const_mul (-48 / Real.pi : ℂ)).differentiableAt.differentiableWithinAt

/-- The original compact cover supplies a holomorphic extension of its actual
pulled-back kernel seed to an open neighborhood of the entire closed disc. -/
theorem source_holomorphic_seed_extension
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (φ : ℂ → ℂ) (hφ : ContinuousOn φ upperHalf) :
    ∃ F : Set ℂ, IsFundamentalDomainH Γ F ∧ IsCompact F ∧
      ∃ r : ℝ, 1 < r ∧
        Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) r ∧
        DifferentiableOn ℂ (extendedSeed F φ) (Metric.ball (0 : ℂ) r) ∧
        EqOn (extendedSeed F φ) (inverseCayleyPullback (AutomorphicPoincare.seed F φ))
          (Metric.ball (0 : ℂ) 1) := by
  obtain ⟨F, hF, hFC, r, hr, hpole, _hInt, hEq⟩ :=
    source_compact_seed_transport R hΓ hp φ hφ
  refine ⟨F, hF, hFC, r, hr, ?_, extendedSeed_differentiableOn hFC (hφ.mono hF.1) hpole, hEq⟩
  intro z hz
  have hn : ‖z‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  exact mem_ball_zero_iff.mpr (hn.trans_lt hr)

end LowDimensionalTopology.Geometry.Teichmuller.CompactPoincareSeed
