module

public import LowDimensionalTopology.Geometry.Teichmuller.CompactPoincareSeedHolomorphy
public import LowDimensionalTopology.Geometry.Teichmuller.DiskPoincareSeries
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral

/-!
# Every original disc automorphic coefficient has a neighborhood-holomorphic seed

The original disc automorphy equation transports through the actual quadratic
Cayley summand identity. The original compact cover then supplies a compact
fundamental domain and its literal seed, holomorphic near the entire closed
disc. Its genuine L¹ bound and the original whole-group Poincare series give
the original coefficient at every disc point, with absolute and compact-uniform
convergence. No full-disc L¹ premise is placed on the automorphic coefficient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal BigOperators UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.DiskPoincare

open Surfaces LiZhongQC Hyperbolic WeightedQuadraticBergman CompactPoincareSeed

/-- The original full disc-group automorphy equation gives the original matrix
half-plane equation by the actual squared-derivative Cayley identity. -/
theorem cayleyPullback_automorphic
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (φ : ℂ → ℂ)
    (hφΓ : ∀ g : discGroup Γ, ∀ z ∈ Metric.ball (0 : ℂ) 1,
      φ (action Γ g z) * deriv (action Γ g) z ^ 2 = φ z) :
    ∀ A ∈ Γ, ∀ w ∈ upperHalf,
      cayleyPullback φ (((A 0 0 : ℂ) * w + A 0 1) / ((A 1 0 : ℂ) * w + A 1 1)) /
        ((A 1 0 : ℂ) * w + A 1 1) ^ 4 = cayleyPullback φ w := by
  intro A hA w hw
  have hwH : 0 < w.im := by simpa only [upperHalf, Set.mem_ofPred_eq] using hw
  let a : Γ := ⟨A, hA⟩
  have hTw := cayley_mapsTo hwH
  have ht := term_equiv Γ φ (ProjectivePoincare.imageHom Γ a) hTw
  rw [inverseCayley_cayley hwH] at ht
  have ha := hφΓ (cayleyGroupEquiv Γ (ProjectivePoincare.imageHom Γ a)) (cayleyFormula w) hTw
  change term Γ φ (cayleyGroupEquiv Γ (ProjectivePoincare.imageHom Γ a))
    (cayleyFormula w) = φ (cayleyFormula w) at ha
  have hc : ProjectivePoincare.term Γ (cayleyPullback φ) (ProjectivePoincare.imageHom Γ a) w *
      inverseCayleyDerivative (cayleyFormula w) ^ 2 = φ (cayleyFormula w) := ht.symm.trans ha
  have hd := inverseCayleyDerivative_cayley hwH
  have himage : ProjectivePoincare.term Γ (cayleyPullback φ)
      (ProjectivePoincare.imageHom Γ a) w = cayleyPullback φ w := by
    calc
      ProjectivePoincare.term Γ (cayleyPullback φ) (ProjectivePoincare.imageHom Γ a) w =
          ProjectivePoincare.term Γ (cayleyPullback φ) (ProjectivePoincare.imageHom Γ a) w *
            (inverseCayleyDerivative (cayleyFormula w) * cayleyDerivative w) ^ 2 := by
        rw [hd, one_pow, mul_one]
      _ = (ProjectivePoincare.term Γ (cayleyPullback φ) (ProjectivePoincare.imageHom Γ a) w *
          inverseCayleyDerivative (cayleyFormula w) ^ 2) * cayleyDerivative w ^ 2 := by ring
      _ = φ (cayleyFormula w) * cayleyDerivative w ^ 2 :=
        congrArg (fun v : ℂ => v * cayleyDerivative w ^ 2) hc
      _ = _ := rfl
  rw [ProjectivePoincare.term_image Γ (cayleyPullback φ) a hw] at himage
  change cayleyPullback φ (((A 0 0 : ℂ) * w + A 0 1) / ((A 1 0 : ℂ) * w + A 1 1)) /
    ((A 1 0 : ℂ) * w + A 1 1) ^ 4 = cayleyPullback φ w at himage
  exact himage

private theorem seed_regular_of_compact {F : Set ℂ} (hFC : IsCompact F)
    (hFH : F ⊆ upperHalf) {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ upperHalf) :
    DifferentiableOn ℂ (AutomorphicPoincare.seed F ψ) upperHalf ∧
      phiArea (AutomorphicPoincare.seed F ψ) upperHalf < ⊤ := by
  have hi : IntegrableOn ψ F :=
    ContinuousOn.integrableOn_compact hFC (hψ.continuousOn.mono hFH)
  have hL1 : ∫⁻ ζ in F, ENNReal.ofReal ‖ψ ζ‖ < ⊤ :=
    (hasFiniteIntegral_iff_norm ψ).mp hi.hasFiniteIntegral
  refine ⟨(h36p_c_beta_diff hFC.measurableSet hFH hψ.continuousOn hL1).const_mul _, ?_⟩
  have hb := h36p_c_beta_L1 hFC.measurableSet hFH hψ.continuousOn hL1
  unfold phiArea AutomorphicPoincare.seed
  calc
    ∫⁻ w in upperHalf,
        ENNReal.ofReal ‖(12 / Real.pi : ℂ) * ∫ ζ in F, h36p_c_K ψ ζ w‖ =
      ENNReal.ofReal ‖(12 / Real.pi : ℂ)‖ *
        ∫⁻ w in upperHalf, ENNReal.ofReal ‖∫ ζ in F, h36p_c_K ψ ζ w‖ := by
      simp_rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb

/-- Every original holomorphic coefficient automorphic for the whole actual
uniformizing disc group is the literal Poincare series of a seed holomorphic
on an open neighborhood of the closed disc. Only the derived seed has an L¹
condition; the original automorphic coefficient has none. -/
theorem exists_holomorphic_neighborhood_seed
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1))
    (hφΓ : ∀ g : discGroup Γ, ∀ z ∈ Metric.ball (0 : ℂ) 1,
      φ (action Γ g z) * deriv (action Γ g) z ^ 2 = φ z) :
    ∃ r : ℝ, 1 < r ∧ ∃ f : ℂ → ℂ,
      Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) r ∧
      DifferentiableOn ℂ f (Metric.ball (0 : ℂ) r) ∧
      phiArea f (Metric.ball (0 : ℂ) 1) < ⊤ ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, φ z = series Γ f z ∧
        Summable (fun g : discGroup Γ => ‖term Γ f g z‖)) ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball (0 : ℂ) 1 →
        TendstoUniformlyOn
          (fun s : Finset (discGroup Γ) => fun z => ∑ g ∈ s, term Γ f g z)
          φ atTop K := by
  let ψ := cayleyPullback φ
  have hψ : DifferentiableOn ℂ ψ upperHalf := cayleyPullback_holomorphic hφ
  have hψΓ := cayleyPullback_automorphic Γ φ hφΓ
  obtain ⟨F, hF, hFC, r, hr, hnear, hE, hEq⟩ :=
    source_holomorphic_seed_extension R hΓ hp ψ hψ.continuousOn
  let f := extendedSeed F ψ
  obtain ⟨hsH, hsA⟩ := seed_regular_of_compact hFC hF.1 hψ
  have hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) :=
    (inverseCayleyPullback_holomorphic hsH).congr (fun _ hz => hEq hz)
  have hfA : phiArea f (Metric.ball (0 : ℂ) 1) < ⊤ := by
    calc
      phiArea f (Metric.ball (0 : ℂ) 1) =
          phiArea (inverseCayleyPullback (AutomorphicPoincare.seed F ψ))
            (Metric.ball (0 : ℂ) 1) := by
        unfold phiArea
        exact setLIntegral_congr_fun measurableSet_ball fun z hz =>
          congrArg (fun v : ℂ => ENNReal.ofReal ‖v‖) (hEq hz)
      _ = phiArea (AutomorphicPoincare.seed F ψ) upperHalf :=
        QuadraticCayleyL1.inverseCayleyPullback_phiArea _
      _ < ⊤ := hsA
  have hUf : ∀ w ∈ upperHalf, cayleyPullback f w = AutomorphicPoincare.seed F ψ w := by
    intro w hw
    have hwH : 0 < w.im := by simpa only [upperHalf, Set.mem_ofPred_eq] using hw
    change extendedSeed F ψ (cayleyFormula w) * cayleyDerivative w ^ 2 = AutomorphicPoincare.seed F ψ w
    rw [hEq (cayley_mapsTo hwH)]
    exact cayleyPullback_inverseCayleyPullback _ hwH
  have hseries : ∀ w ∈ upperHalf,
      ProjectivePoincare.series Γ (cayleyPullback f) w =
        ProjectivePoincare.series Γ (AutomorphicPoincare.seed F ψ) w := by
    intro w hw
    unfold ProjectivePoincare.series
    apply tsum_congr
    intro g
    unfold ProjectivePoincare.term
    rw [hUf (ProjectivePoincare.action Γ g w) (ProjectivePoincare.action_mem Γ g hw)]
  have hrepH := (AutomorphicPoincare.automorphic_kernel_series R p hΓ hp hF ψ hψ hψΓ).1
  have hrep : ∀ z ∈ Metric.ball (0 : ℂ) 1, φ z = series Γ f z := by
    intro z hz
    have hzH : inverseCayleyFormula z ∈ upperHalf := by
      simpa only [upperHalf] using inverseCayley_mapsTo hz
    calc
      φ z = ψ (inverseCayleyFormula z) * inverseCayleyDerivative z ^ 2 :=
        (inverseCayleyPullback_cayleyPullback φ hz).symm
      _ = ProjectivePoincare.series Γ (AutomorphicPoincare.seed F ψ)
          (inverseCayleyFormula z) * inverseCayleyDerivative z ^ 2 :=
        congrArg (fun v : ℂ => v * inverseCayleyDerivative z ^ 2) (hrepH _ hzH).1
      _ = ProjectivePoincare.series Γ (cayleyPullback f)
          (inverseCayleyFormula z) * inverseCayleyDerivative z ^ 2 :=
        congrArg (fun v : ℂ => v * inverseCayleyDerivative z ^ 2) (hseries _ hzH).symm
      _ = series Γ f z := (series_eq_inverseCayleyPullback Γ f hz).symm
  refine ⟨r, hr, f, hnear, hE, hfA, ?_, ?_⟩
  · intro z hz
    exact ⟨hrep z hz, summable_norm Γ hΓ hf hfA hz⟩
  · intro K hK hKD
    apply (tendstoUniformlyOn Γ hΓ hf hfA hK hKD).congr_right
    intro z hz
    exact (hrep z (hKD hz)).symm

end LowDimensionalTopology.Geometry.Teichmuller.DiskPoincare
