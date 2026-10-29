module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertRadialPotential
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertPotentialFubini
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertConvolutionGreen

/-!
# The actual radial iteration of a compact-test circular transform

Joint absolute integrability gives the renormalized double potential.
The compact-test Green identity identifies it with the original Cauchy
potential. Its Wirtinger derivative is the negative planar transform.
The noncompact input is interpreted through its genuine radial limit.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The renormalized value integral is genuinely integrable for the literal
circular transform of an original smooth compact test, at every pole. -/
theorem integrable_circularHilbertTransform_renormalizedKernel {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) (w : ℂ) :
    Integrable (fun t : ℂ => circularHilbertTransform φ t *
      renormalizedInverseNormKernel t w) (volume : Measure ℂ) := by
  have hψ : Continuous (LiZhongQC.dz φ) := LiZhongQC.continuous_dz (hφ.of_le (by simp))
  have hcψ : HasCompactSupport (LiZhongQC.dz φ) := LiZhongQC.dz_hasCompactSupport hc
  have hi := integrable_compactTest_inverseNormConvolution hψ hcψ w
  have hiter : Integrable (fun t : ℂ => ∫ z : ℂ,
      LiZhongQC.dz φ z * renormalizedInverseNormConvolutionIntegrand z w t)
      (volume : Measure ℂ) := hi.integral_prod_right
  have hpotential : Integrable (fun t : ℂ => inverseNormPotential (LiZhongQC.dz φ) t *
      renormalizedInverseNormKernel t w) (volume : Measure ℂ) := by
    apply hiter.congr
    filter_upwards with t
    rw [inverseNormPotential_eq_integral, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with z
    dsimp only [renormalizedInverseNormConvolutionIntegrand]
    ring
  apply (hpotential.const_mul (1 / (Real.pi : ℂ))).congr
  filter_upwards with t
  rw [circularHilbertTransform_eq_inverseNormPotential_dz hφ hc t]
  ring

/-- The actual renormalized potential of the first circular transform
is the normalized difference of the original Cauchy potentials. -/
theorem renormalizedInverseNormPotential_circularHilbertTransform {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) (w : ℂ) :
    renormalizedInverseNormPotential (circularHilbertTransform φ) w =
      -(Real.pi : ℂ) * (LiZhongQC.cauchyT φ w - LiZhongQC.cauchyT φ 0) := by
  have hψ : Continuous (LiZhongQC.dz φ) := LiZhongQC.continuous_dz (hφ.of_le (by simp))
  have hcψ : HasCompactSupport (LiZhongQC.dz φ) := LiZhongQC.dz_hasCompactSupport hc
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcoeff : (1 / (Real.pi : ℂ)) * (Real.pi : ℂ) = 1 := by field_simp [hπ]
  have halg (a b : ℂ) : a - b = -(Real.pi : ℂ) *
      ((-(1 / (Real.pi : ℂ))) * a - (-(1 / (Real.pi : ℂ))) * b) := by
    have hc' : (Real.pi : ℂ) * (1 / (Real.pi : ℂ)) = 1 := by
      simpa only [mul_comm] using hcoeff
    calc
      a - b = ((Real.pi : ℂ) * (1 / (Real.pi : ℂ))) * (a - b) := by
        rw [hc', one_mul]
      _ = _ := by ring
  calc
    renormalizedInverseNormPotential (circularHilbertTransform φ) w =
        (1 / (Real.pi : ℂ)) *
          renormalizedInverseNormPotential (inverseNormPotential (LiZhongQC.dz φ)) w := by
      unfold renormalizedInverseNormPotential
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      rw [circularHilbertTransform_eq_inverseNormPotential_dz hφ hc t]
      ring
    _ = (1 / (Real.pi : ℂ)) * ((Real.pi : ℂ) *
        ((∫ z : ℂ, φ z / (z - w)) - (∫ z : ℂ, φ z / z))) := by
      rw [renormalizedInverseNormPotential_inverseNormPotential hψ hcψ w,
        integral_dz_mul_renormalizedInverseNormConvolution hφ hc w]
    _ = (∫ z : ℂ, φ z / (z - w)) - (∫ z : ℂ, φ z / z) := by
      rw [← mul_assoc, hcoeff, one_mul]
    _ = -(Real.pi : ℂ) * (LiZhongQC.cauchyT φ w - LiZhongQC.cauchyT φ 0) := by
      simpa only [LiZhongQC.cauchyT, sub_zero] using
        halg (∫ z : ℂ, φ z / (z - w)) (∫ z : ℂ, φ z / z)

/-- On its literal smooth noncompact input, the second radial circular
transform equals the negative original smooth planar transform. -/
theorem radialCircularHilbertTransform_circular_eq_neg_hilbertHSmooth {p : ℝ}
    (hp : 1 < p) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ)
    (hmem : MemLp (circularHilbertTransform φ) (ENNReal.ofReal p) (volume : Measure ℂ))
    (z : ℂ) :
    radialCircularHilbertTransform (circularHilbertTransform φ) z =
      -LiZhongQC.hilbertHSmooth φ z := by
  rw [radialCircularHilbertTransform_eq_dz_renormalizedInverseNormPotential hp
    (contDiff_circularHilbertTransform hφ hc) hmem
    (integrable_circularHilbertTransform_renormalizedKernel hφ hc) z]
  have hP : renormalizedInverseNormPotential (circularHilbertTransform φ) =
      fun w => -(Real.pi : ℂ) * (LiZhongQC.cauchyT φ w - LiZhongQC.cauchyT φ 0) :=
    funext (renormalizedInverseNormPotential_circularHilbertTransform hφ hc)
  have hCd : DifferentiableAt ℝ (LiZhongQC.cauchyT φ) z :=
    ((LiZhongQC.eq11_17 hφ hc).1.differentiable one_ne_zero) z
  have hsubfun : (LiZhongQC.cauchyT φ - fun _ : ℂ => LiZhongQC.cauchyT φ 0) =
      fun w : ℂ => LiZhongQC.cauchyT φ w - LiZhongQC.cauchyT φ 0 := by
    funext w
    simp only [Pi.sub_apply]
  have hCdsub := hCd.sub (differentiableAt_const (LiZhongQC.cauchyT φ 0))
  rw [hsubfun] at hCdsub
  have hconst : LiZhongQC.dz (fun _ : ℂ => -(Real.pi : ℂ)) z = 0 := by
    simp [LiZhongQC.dz]
  have hconst0 : LiZhongQC.dz (fun _ : ℂ => LiZhongQC.cauchyT φ 0) z = 0 := by
    simp [LiZhongQC.dz]
  rw [hP, LiZhongQC.dz_mul (differentiableAt_const (-(Real.pi : ℂ)))
    hCdsub,
    LiZhongQC.dz_sub_pointwise hCd (differentiableAt_const (LiZhongQC.cauchyT φ 0)),
    hconst, hconst0, mul_zero, add_zero, sub_zero, ((LiZhongQC.eq11_17 hφ hc).2 z).2]
  have hcoeff : (1 / (Real.pi : ℂ)) * (-(Real.pi : ℂ)) = -1 := by
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [← mul_assoc, hcoeff, neg_one_mul]

end LowDimensionalTopology.Geometry.Quasiconformal
