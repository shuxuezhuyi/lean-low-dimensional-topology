module

public import LowDimensionalTopology.Unproved.Quasiconformal.RealDirectionalHilbert
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Regularity of the circular Hilbert directional average

The real-line Riesz assertion supplies the principal values for all affine
line restrictions of a smooth compact planar test. Those actual principal
values form a jointly strongly measurable function of the angle and point.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Unproved.Quasiconformal

private theorem affineLine_isometry (θ : ℝ) (ζ : ℂ) :
    Isometry (fun x : ℝ => (x : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub, ← sub_mul,
    norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_sub,
    Complex.norm_real]

/-- Restricting a compactly supported planar test to an actual affine line
preserves compact support. -/
theorem hasCompactSupport_affineLine {φ : ℂ → ℂ} (hφ : HasCompactSupport φ)
    (θ : ℝ) (ζ : ℂ) :
    HasCompactSupport
      (fun x : ℝ => φ ((x : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ)) :=
  hφ.comp_isClosedEmbedding (affineLine_isometry θ ζ).isClosedEmbedding

/-- The same literal affine restriction is smooth as a real-variable test. -/
theorem contDiff_affineLine {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (θ : ℝ) (ζ : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => φ ((x : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ)) := by
  exact hφ.comp ((Complex.ofRealCLM.contDiff.mul contDiff_const).add contDiff_const)

/-- Every direction in the circular average has the genuine real principal
value, conditional only on the specified real-line Riesz assertion. -/
theorem hasRealHilbertPrincipalValue_affineLine {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) (θ : ℝ) (ζ : ℂ) (ξ : ℝ) :
    HasRealHilbertPrincipalValue
      (fun x : ℝ => φ ((x : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ)) ξ :=
  (hA.2.2 p hp _ (contDiff_affineLine hφ θ ζ)
    (hasCompactSupport_affineLine hc θ ζ)).1 ξ

/-- The untruncated directional values are jointly strongly measurable in
the angle and the actual planar point. -/
theorem stronglyMeasurable_directionalHilbertTransform {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    StronglyMeasurable
      (fun w : ℝ × ℂ => directionalHilbertTransform φ w.1 w.2) := by
  have hφm : Measurable φ := hφ.continuous.measurable
  have hm (ε : ℝ) : StronglyMeasurable (fun w : ℝ × ℂ =>
      realHilbertTruncation
        (fun x : ℝ => φ ((x : ℂ) * Complex.exp ((w.1 : ℂ) * I) + w.2)) 0 ε) := by
    have hf : StronglyMeasurable (fun v : (ℝ × ℂ) × ℝ =>
        φ ((v.2 : ℂ) * Complex.exp ((v.1.1 : ℂ) * I) + v.1.2) / (v.2 : ℂ)) := by
      apply Measurable.stronglyMeasurable
      fun_prop
    have hi := hf.integral_prod_right' (ν := (volume : Measure ℝ).restrict
      {x : ℝ | ε < |x|})
    simpa only [realHilbertTruncation, sub_zero] using hi.const_mul (1 / (Real.pi : ℂ))
  apply stronglyMeasurable_of_tendsto (𝓝[>] (0 : ℝ)) hm
  apply tendsto_pi_nhds.mpr
  intro w
  exact hasRealHilbertPrincipalValue_affineLine hA hp hφ hc w.1 w.2 0

/-- The literal angular average itself is strongly measurable. This does
not identify it with the separate radial principal-value expression. -/
theorem stronglyMeasurable_circularHilbertTransform {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hc : HasCompactSupport φ) : StronglyMeasurable (circularHilbertTransform φ) := by
  have hd := stronglyMeasurable_directionalHilbertTransform hA hp hφ hc
  have he : StronglyMeasurable (fun w : ℝ × ℂ =>
      Complex.exp (-((w.1 : ℂ) * I))) := by
    apply Continuous.stronglyMeasurable
    fun_prop
  have hf : StronglyMeasurable (fun w : ℝ × ℂ =>
      directionalHilbertTransform φ w.1 w.2 * Complex.exp (-((w.1 : ℂ) * I))) := by
    simpa only [Pi.mul_def] using hd.mul he
  have hi := hf.integral_prod_left' (μ :=
    (volume : Measure ℝ).restrict (Ioc 0 Real.pi))
  have heq : circularHilbertTransform φ = (fun ζ : ℂ => (1 / 2 : ℂ) *
      ∫ θ in Ioc (0 : ℝ) Real.pi,
        directionalHilbertTransform φ θ ζ * Complex.exp (-((θ : ℂ) * I))) := by
    funext ζ
    rw [circularHilbertTransform, intervalIntegral.integral_of_le Real.pi_pos.le]
  rw [heq]
  exact hi.const_mul (1 / 2 : ℂ)

/-- Any family satisfying the real-line estimate has nonnegative constants
on the stated exponent range. No positivity premise is added to the estimate. -/
theorem RealHilbertEstimate.nonneg {A : ℝ → ℝ} (hA : RealHilbertEstimate A)
    {p : ℝ} (hp : 2 ≤ p) : 0 ≤ A p := by
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := 1
      rOut := 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let φ : ℝ → ℂ := fun x => (b.normed volume x : ℂ)
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ :=
    Complex.ofRealCLM.contDiff.comp (b.contDiff_normed (μ := volume))
  have hc : HasCompactSupport φ :=
    b.hasCompactSupport_normed.comp_left (g := fun x : ℝ => (x : ℂ)) rfl
  have hm : MemLp φ (ENNReal.ofReal p) (volume : Measure ℝ) :=
    hφ.continuous.memLp_of_hasCompactSupport hc
  have hint : (∫ x, φ x) = (1 : ℂ) := by
    rw [show φ = (fun x => (b.normed volume x : ℂ)) from rfl,
      integral_complex_ofReal, b.integral_normed, Complex.ofReal_one]
  have hne : eLpNorm φ (ENNReal.ofReal p) (volume : Measure ℝ) ≠ 0 := by
    intro hz
    have hzφ : φ =ᵐ[volume] (0 : ℝ → ℂ) :=
      (eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le (by norm_num) hp)).ne').mp hz
    have hint0 : (∫ x, φ x) = (0 : ℂ) := by
      simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hzφ
    exact one_ne_zero (hint.symm.trans hint0)
  have hn : 0 < (eLpNorm φ (ENNReal.ofReal p) (volume : Measure ℝ)).toReal :=
    ENNReal.toReal_pos hne hm.eLpNorm_ne_top
  have hb := (hA.2.2 p hp φ hφ hc).2.2
  have hH := ENNReal.toReal_nonneg
    (a := eLpNorm (realHilbertTransform φ) (ENNReal.ofReal p) (volume : Measure ℝ))
  nlinarith

end LowDimensionalTopology.Geometry.Quasiconformal
