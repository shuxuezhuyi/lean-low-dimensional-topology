module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanSpaces
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HyperbolicBalls
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Quadratic Cayley pullback in the original weighted spaces

The actual inverse Cayley map carries the full disc onto the upper half-plane.
Its real Jacobian and the original inverse-square density weights prove that
pullback with the square of its complex derivative preserves weighted L²
membership and the original norm. No completeness assumption is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ComplexConjugate ENNReal NNReal UpperHalfPlane Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman

open LowDimensionalTopology.Geometry.Hyperbolic

/-- The explicit derivative of the original half-plane-to-disc Cayley formula. -/
def cayleyDerivative (z : ℂ) : ℂ := (2 * Complex.I) / (z + Complex.I) ^ 2

/-- The explicit derivative of the original inverse Cayley formula. -/
def inverseCayleyDerivative (z : ℂ) : ℂ := (2 * Complex.I) / (1 - z) ^ 2

/-- Quadratic differential pullback includes the square of the actual derivative. -/
def inverseCayleyPullback (ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ψ (inverseCayleyFormula z) * inverseCayleyDerivative z ^ 2

/-- The inverse formula maps every original disc point into the upper half-plane. -/
theorem inverseCayley_mapsTo :
    MapsTo inverseCayleyFormula (Metric.ball (0 : ℂ) 1) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact inverseCayley_im_pos (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz))

/-- Its image is the whole original upper half-plane. -/
theorem inverseCayley_image_disk :
    inverseCayleyFormula '' Metric.ball (0 : ℂ) 1 = {z : ℂ | 0 < z.im} := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact inverseCayley_mapsTo hz
  · intro z hz
    let zH : ℍ := UpperHalfPlane.mk z hz
    refine ⟨cayleyFormula z, mem_ball_zero_iff.mpr (cayley_mem_disc zH), ?_⟩
    exact congrArg ((↑) : ℍ → ℂ) (discToHalfPlane_halfPlaneToDisc zH)

/-- The actual inverse Cayley formula is injective on the full original disc. -/
theorem inverseCayley_injOn_disk :
    InjOn inverseCayleyFormula (Metric.ball (0 : ℂ) 1) := by
  intro z hz w hw h
  let zD : 𝔻 := Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz)
  let wD : 𝔻 := Complex.UnitDisc.mk w (mem_ball_zero_iff.mp hw)
  have he : discToHalfPlane zD = discToHalfPlane wD := UpperHalfPlane.coe_injective h
  exact congrArg ((↑) : 𝔻 → ℂ) (cayleyEquiv.symm.injective he)

/-- The original disc weight transforms by the squared norm of the actual derivative. -/
theorem cayley_weight {z : ℂ} (hz : 0 < z.im) :
    (diskWeight (cayleyFormula z) : ℝ) =
      (halfPlaneWeight z : ℝ) * ‖cayleyDerivative z‖ ^ 2 := by
  let zH : ℍ := UpperHalfPlane.mk z hz
  have hn : ‖z + Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr (cayley_denom_ne_zero zH)
  change (1 - ‖cayleyFormula z‖ ^ 2) ^ 2 / 4 =
    z.im ^ 2 * ‖(2 * Complex.I) / (z + Complex.I) ^ 2‖ ^ 2
  have hformula := cayley_one_sub_norm_sq (UpperHalfPlane.mk z hz)
  simp only [UpperHalfPlane.mk_im] at hformula
  rw [hformula]
  simp only [norm_div, norm_mul, Complex.norm_I, mul_one, norm_pow,
    show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  field_simp [hn]
  ring

/-- The inverse formula has the corresponding identity for the original weights. -/
theorem inverseCayley_weight {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (halfPlaneWeight (inverseCayleyFormula z) : ℝ) =
      (diskWeight z : ℝ) * ‖inverseCayleyDerivative z‖ ^ 2 := by
  let zD : 𝔻 := Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz)
  have hn : ‖1 - z‖ ≠ 0 := norm_ne_zero_iff.mpr (inverseCayley_denom_ne_zero zD)
  change (inverseCayleyFormula z).im ^ 2 =
    ((1 - ‖z‖ ^ 2) ^ 2 / 4) * ‖(2 * Complex.I) / (1 - z) ^ 2‖ ^ 2
  have hformula := inverseCayley_im (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz))
  simp only [Complex.UnitDisc.coe_mk] at hformula
  rw [hformula]
  simp only [norm_div, norm_mul, Complex.norm_I, mul_one, norm_pow,
    show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  field_simp [hn]
  ring

/-- This is the determinant of the actual real derivative, rather than a density convention. -/
theorem inverseCayley_jacobian (z : ℂ) :
    |(inverseCayleyRealFDeriv z).det| = ‖inverseCayleyDerivative z‖ ^ 2 := by
  unfold inverseCayleyDerivative
  rw [det_inverseCayleyRealFDeriv, abs_of_nonneg (sq_nonneg _)]

/-- True two-dimensional change of variables gives both directions of integrability. -/
theorem inverseCayley_integrableOn_iff (g : ℂ → ℝ) :
    IntegrableOn g {z : ℂ | 0 < z.im} ↔
      IntegrableOn (fun z => ‖inverseCayleyDerivative z‖ ^ 2 *
        g (inverseCayleyFormula z)) (Metric.ball (0 : ℂ) 1) := by
  simpa only [inverseCayley_image_disk, inverseCayley_jacobian, smul_eq_mul] using
    (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      (f := inverseCayleyFormula) (f' := inverseCayleyRealFDeriv) measurableSet_ball
      (fun z hz => (hasFDerivAt_inverseCayley_real
        (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz))).hasFDerivWithinAt)
      inverseCayley_injOn_disk g)

/-- The same real Jacobian transports the actual planar integral. -/
theorem inverseCayley_integral (g : ℂ → ℝ) :
    (∫ z in {z : ℂ | 0 < z.im}, g z) =
      ∫ z in Metric.ball (0 : ℂ) 1,
        ‖inverseCayleyDerivative z‖ ^ 2 * g (inverseCayleyFormula z) := by
  simpa only [inverseCayley_image_disk, inverseCayley_jacobian, smul_eq_mul] using
    (integral_image_eq_integral_abs_det_fderiv_smul volume
      (f := inverseCayleyFormula) (f' := inverseCayleyRealFDeriv) measurableSet_ball
      (fun z hz => (hasFDerivAt_inverseCayley_real
        (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz))).hasFDerivWithinAt)
      inverseCayley_injOn_disk g)

/-- The true quadratic pullback is holomorphic on the entire original disc. -/
theorem inverseCayleyPullback_holomorphic {ψ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ {z : ℂ | 0 < z.im}) :
    DifferentiableOn ℂ (inverseCayleyPullback ψ) (Metric.ball (0 : ℂ) 1) := by
  have hS : DifferentiableOn ℂ inverseCayleyFormula (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    exact (hasDerivAt_inverseCayleyFormula
      (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz))).differentiableAt.differentiableWithinAt
  have hd : DifferentiableOn ℂ inverseCayleyDerivative (Metric.ball (0 : ℂ) 1) := by
    unfold inverseCayleyDerivative
    refine (differentiableOn_const _).div
      (((differentiableOn_const (1 : ℂ)).sub differentiableOn_id).pow 2) ?_
    intro z hz
    exact pow_ne_zero 2 (inverseCayley_denom_ne_zero
      (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz)))
  exact (hψ.fun_comp hS inverseCayley_mapsTo).mul (hd.pow 2)

private theorem memLp_two_weighted_iff (Ω : Set ℂ) (w : ℂ → ℝ≥0)
    (hΩ : IsOpen Ω) (hw : Measurable w) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ Ω) :
    MemLp φ 2 (weightedMeasure Ω w) ↔
      IntegrableOn (fun z => (w z : ℝ) * ‖φ z‖ ^ 2) Ω := by
  have hm₀ : AEStronglyMeasurable φ (volume.restrict Ω) :=
    hφ.continuousOn.aestronglyMeasurable hΩ.measurableSet
  have hm : AEStronglyMeasurable φ (weightedMeasure Ω w) :=
    AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _) hm₀
  rw [memLp_two_iff_integrable_sq_norm hm]
  unfold weightedMeasure
  simpa only [IntegrableOn, smul_eq_mul] using
    (integrable_withDensity_iff_integrable_coe_smul (μ := volume.restrict Ω) hw
      (g := fun z => ‖φ z‖ ^ 2))

private theorem inverseCayley_weighted_norm_sq (ψ : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (diskWeight z : ℝ) * ‖inverseCayleyPullback ψ z‖ ^ 2 =
      ‖inverseCayleyDerivative z‖ ^ 2 *
        ((halfPlaneWeight (inverseCayleyFormula z) : ℝ) * ‖ψ (inverseCayleyFormula z)‖ ^ 2) := by
  simp only [inverseCayleyPullback, norm_mul, norm_pow, mul_pow]
  rw [inverseCayley_weight hz]
  ring

/-- Genuine square integrability is equivalent under the actual quadratic pullback. -/
theorem inverseCayleyPullback_memLp_iff {ψ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ {z : ℂ | 0 < z.im}) :
    MemLp ψ 2 halfPlaneMeasure ↔ MemLp (inverseCayleyPullback ψ) 2 diskMeasure := by
  rw [memLp_two_weighted_iff _ _ (isOpen_lt continuous_const Complex.continuous_im)
      halfPlaneWeight_measurable hψ,
    memLp_two_weighted_iff _ _ Metric.isOpen_ball diskWeight_measurable
      (inverseCayleyPullback_holomorphic hψ)]
  refine (inverseCayley_integrableOn_iff
    (fun z => (halfPlaneWeight z : ℝ) * ‖ψ z‖ ^ 2)).trans ?_
  exact integrableOn_congr_fun
    (fun z hz => (inverseCayley_weighted_norm_sq ψ hz).symm) measurableSet_ball

/-- The original weighted-square integrals are transported by the genuine planar Jacobian. -/
theorem inverseCayleyPullback_integral_norm_sq (ψ : ℂ → ℂ) :
    (∫ z in Metric.ball (0 : ℂ) 1, (diskWeight z : ℝ) * ‖inverseCayleyPullback ψ z‖ ^ 2) =
      ∫ z in {z : ℂ | 0 < z.im}, (halfPlaneWeight z : ℝ) * ‖ψ z‖ ^ 2 := by
  rw [inverseCayley_integral]
  exact setIntegral_congr_fun measurableSet_ball fun z hz =>
    inverseCayley_weighted_norm_sq ψ hz

/-- Every element of the full original half-plane space gives a genuine original disc element. -/
def inverseCayleyPullbackElement (q : HalfPlane) : Disk :=
  ofFunction (inverseCayleyPullback (coefficient q))
    (inverseCayleyPullback_holomorphic (coefficient_holomorphic q))
    ((inverseCayleyPullback_memLp_iff (coefficient_holomorphic q)).mp (coefficient_memLp q))

/-- The constructor retains the quadratic pullback at every original disc point. -/
theorem inverseCayleyPullbackElement_coefficient (q : HalfPlane) :
    EqOn (coefficient (inverseCayleyPullbackElement q))
      (inverseCayleyPullback (coefficient q)) (Metric.ball (0 : ℂ) 1) := by
  unfold inverseCayleyPullbackElement
  exact disk_coefficient_ofFunction _ _ _

/-- The actual native norm square is preserved for every original half-plane element. -/
theorem inverseCayleyPullbackElement_norm_sq (q : HalfPlane) :
    ‖inverseCayleyPullbackElement q‖ ^ 2 = ‖q‖ ^ 2 := by
  rw [disk_norm_sq_eq_integral, halfPlane_norm_sq_eq_integral]
  calc
    (∫ z in Metric.ball (0 : ℂ) 1,
        (diskWeight z : ℝ) * ‖coefficient (inverseCayleyPullbackElement q) z‖ ^ 2) =
        ∫ z in Metric.ball (0 : ℂ) 1,
          (diskWeight z : ℝ) * ‖inverseCayleyPullback (coefficient q) z‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      dsimp only
      rw [inverseCayleyPullbackElement_coefficient q hz]
    _ = _ := inverseCayleyPullback_integral_norm_sq (coefficient q)

/-- This equality uses the same original norm on each full weighted space. -/
theorem inverseCayleyPullbackElement_norm (q : HalfPlane) :
    ‖inverseCayleyPullbackElement q‖ = ‖q‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (inverseCayleyPullbackElement_norm_sq q)

end LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman
