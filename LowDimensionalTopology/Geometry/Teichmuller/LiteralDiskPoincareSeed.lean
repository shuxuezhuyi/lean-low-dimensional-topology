module

public import LowDimensionalTopology.Geometry.Teichmuller.DiskPoincareSeedRepresentation
public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanDiskReproduction

/-! # The literal original disc-domain seed and its actual Cayley image integral -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.DiskPoincare
open Surfaces LiZhongQC Hyperbolic WeightedQuadraticBergman CompactPoincareSeed

/-- The literal seed on any supplied original disc integration set. -/
def literalSeed (F : Set ℂ) (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ ζ in F, (diskWeight ζ : ℂ) * φ ζ * conj (diskQuadraticKernel z ζ)

private theorem literal_integrand_change (ψ : ℂ → ℂ) {z u : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) (hu : u ∈ Metric.ball (0 : ℂ) 1) :
    (diskWeight u : ℂ) * inverseCayleyPullback ψ u * conj (diskQuadraticKernel z u) =
      ‖inverseCayleyDerivative u‖ ^ 2 •
        (((inverseCayleyFormula u).im : ℂ) ^ 2 * ψ (inverseCayleyFormula u) *
          conj (QuadraticBergman.halfPlaneQuadraticKernel
            (inverseCayleyFormula z) (inverseCayleyFormula u)) * inverseCayleyDerivative z ^ 2) := by
  have hw := congrArg (fun r : ℝ => (r : ℂ)) (inverseCayley_weight hu)
  simp only [Complex.ofReal_mul] at hw
  change (((inverseCayleyFormula u).im ^ 2 : ℝ) : ℂ) = _ at hw
  rw [Complex.ofReal_pow] at hw
  have hn : inverseCayleyDerivative u ^ 2 * conj (inverseCayleyDerivative u ^ 2) =
      ((‖inverseCayleyDerivative u‖ ^ 2 : ℝ) : ℂ) ^ 2 := by
    rw [map_pow, ← mul_pow, Complex.mul_conj']
    simp only [Complex.ofReal_pow]
  rw [inverseCayleyPullback, inverseCayley_kernel_covariance hz hu]
  simp only [map_mul, Complex.conj_conj, Complex.real_smul]
  calc
    _ = (diskWeight u : ℂ) * ψ (inverseCayleyFormula u) *
        conj (QuadraticBergman.halfPlaneQuadraticKernel
          (inverseCayleyFormula z) (inverseCayleyFormula u)) * inverseCayleyDerivative z ^ 2 *
        (inverseCayleyDerivative u ^ 2 * conj (inverseCayleyDerivative u ^ 2)) := by ring
    _ = _ := by rw [hn, hw]; ring

/-- The genuine planar Jacobian theorem on this same image integration set. -/
theorem literalSeed_inverseCayley_image (G : Set ℂ) (hG : MeasurableSet G)
    (hGD : G ⊆ Metric.ball (0 : ℂ) 1) (ψ : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    literalSeed G (inverseCayleyPullback ψ) z =
      inverseCayleyPullback (AutomorphicPoincare.seed (inverseCayleyFormula '' G) ψ) z := by
  have hc := integral_image_eq_integral_abs_det_fderiv_smul volume
    (f := inverseCayleyFormula) (f' := inverseCayleyRealFDeriv) hG
    (fun u hu => (hasFDerivAt_inverseCayley_real
      (Complex.UnitDisc.mk u (mem_ball_zero_iff.mp (hGD hu)))).hasFDerivWithinAt)
    (inverseCayley_injOn_disk.mono hGD)
    (fun w => (w.im : ℂ) ^ 2 * ψ w *
      conj (QuadraticBergman.halfPlaneQuadraticKernel (inverseCayleyFormula z) w) *
        inverseCayleyDerivative z ^ 2)
  simp only [inverseCayley_jacobian] at hc
  unfold literalSeed inverseCayleyPullback
  rw [AutomorphicPoincare.seed_eq_kernel, ← integral_mul_const, hc]
  exact setIntegral_congr_fun hG fun u hu => literal_integrand_change ψ hz (hGD hu)

/-- For a compact actual half-plane set, the literal D seed uses its exact
Cayley image and agrees with the proved closed-disc extension on D. -/
theorem literalSeed_cayley_image {F : Set ℂ} (hFC : IsCompact F) (hFH : F ⊆ upperHalf)
    (φ : ℂ → ℂ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    literalSeed (cayleyFormula '' F) φ z = extendedSeed F (cayleyPullback φ) z := by
  have hC : ContinuousOn cayleyFormula F := fun w hw =>
    (hasDerivAt_cayleyFormula (UpperHalfPlane.mk w (hFH hw))).continuousAt.continuousWithinAt
  have hGC := hFC.image_of_continuousOn hC
  have hGD : cayleyFormula '' F ⊆ Metric.ball (0 : ℂ) 1 := by
    rintro _ ⟨w, hw, rfl⟩
    exact cayley_mapsTo (hFH hw)
  have hi : inverseCayleyFormula '' (cayleyFormula '' F) = F := by
    ext w
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      simpa only [inverseCayley_cayley (hFH hv)] using hv
    · intro hw
      exact ⟨cayleyFormula w, ⟨w, hw, rfl⟩, inverseCayley_cayley (hFH hw)⟩
  calc
    literalSeed (cayleyFormula '' F) φ z = literalSeed (cayleyFormula '' F)
        (inverseCayleyPullback (cayleyPullback φ)) z := by
      apply setIntegral_congr_fun hGC.measurableSet
      intro u hu
      dsimp only
      rw [inverseCayleyPullback_cayleyPullback φ (hGD hu)]
    _ = inverseCayleyPullback (AutomorphicPoincare.seed F (cayleyPullback φ)) z := by
      rw [literalSeed_inverseCayley_image _ hGC.measurableSet hGD (cayleyPullback φ) hz, hi]
    _ = _ := (extendedSeed_eq_inverseCayleyPullback F hFC.measurableSet _ hz).symm

/-- The original closed cover supplies an actual compact fundamental domain
whose literal D seed has a holomorphic extension near the entire closed disc. -/
theorem source_literalSeed_extension
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1)) :
    ∃ F : Set ℂ, IsFundamentalDomainH Γ F ∧ IsCompact F ∧
      ∃ r : ℝ, 1 < r ∧ ∃ E : ℂ → ℂ,
        Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) r ∧
        DifferentiableOn ℂ E (Metric.ball (0 : ℂ) r) ∧
        EqOn E (literalSeed (cayleyFormula '' F) φ) (Metric.ball (0 : ℂ) 1) := by
  obtain ⟨F, hF, hFC, r, hr, hnear, hE, _⟩ :=
    source_holomorphic_seed_extension R hΓ hp (cayleyPullback φ)
      (cayleyPullback_holomorphic hφ).continuousOn
  exact ⟨F, hF, hFC, r, hr, extendedSeed F (cayleyPullback φ), hnear, hE,
    fun z hz => (literalSeed_cayley_image hFC hF.1 φ hz).symm⟩

/-- The Poincare series of this literal D-domain integral recovers the SAME
original disc coefficient, using the full actual disc group. -/
theorem literalSeed_recovers
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X) {p : ℍ → X}
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (hFC : IsCompact F)
    (φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1))
    (hφΓ : ∀ g : discGroup Γ, ∀ z ∈ Metric.ball (0 : ℂ) 1,
      φ (action Γ g z) * deriv (action Γ g) z ^ 2 = φ z)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    φ z = series Γ (literalSeed (cayleyFormula '' F) φ) z := by
  have he : EqOn (cayleyPullback (literalSeed (cayleyFormula '' F) φ))
      (AutomorphicPoincare.seed F (cayleyPullback φ)) upperHalf := by
    intro w hw
    change literalSeed (cayleyFormula '' F) φ (cayleyFormula w) * cayleyDerivative w ^ 2 = _
    rw [literalSeed_cayley_image hFC hF.1 φ (cayley_mapsTo hw),
      extendedSeed_eq_inverseCayleyPullback F hFC.measurableSet _ (cayley_mapsTo hw)]
    exact cayleyPullback_inverseCayleyPullback _ hw
  have hzH : inverseCayleyFormula z ∈ upperHalf := inverseCayley_mapsTo hz
  have hs : ProjectivePoincare.series Γ (cayleyPullback (literalSeed (cayleyFormula '' F) φ))
      (inverseCayleyFormula z) =
      ProjectivePoincare.series Γ (AutomorphicPoincare.seed F (cayleyPullback φ))
        (inverseCayleyFormula z) := by
    unfold ProjectivePoincare.series
    apply tsum_congr
    intro g
    unfold ProjectivePoincare.term
    rw [he (ProjectivePoincare.action_mem Γ g hzH)]
  have hrep := (AutomorphicPoincare.automorphic_kernel_series R p hΓ hp hF
    (cayleyPullback φ) (cayleyPullback_holomorphic hφ) (cayleyPullback_automorphic Γ φ hφΓ)).1
      (inverseCayleyFormula z) hzH
  rw [series_eq_inverseCayleyPullback Γ _ hz]
  change φ z = _ * inverseCayleyDerivative z ^ 2
  rw [hs, ← hrep.1]
  exact (inverseCayleyPullback_cayleyPullback φ hz).symm

end LowDimensionalTopology.Geometry.Teichmuller.DiskPoincare
