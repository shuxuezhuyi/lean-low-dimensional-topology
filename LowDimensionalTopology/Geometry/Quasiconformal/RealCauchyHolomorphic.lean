module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealCauchyKernel
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Holomorphicity of the upper-half-plane Cauchy integral

Its differentiability
follows from Mathlib's dominated integral derivative theorem, with the explicit
uniform separation from the real axis. The proof uses the same public API
pattern as the existing Li-Zhong-QC Cauchy-kernel development; no additional
singular-integral estimate or harmonic extension premise is assumed.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The book's Cauchy function as a function of the actual complex point. -/
def realCauchyFunction (φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  ((1 / Real.pi : ℝ) : ℂ) * ∫ x : ℝ, (φ x : ℂ) / ((x : ℂ) - z)

/-- Agreement with the already formalized re/im kernel integral. -/
theorem realCauchyFunction_eq_integral (φ : ℝ → ℝ) (ξ η : ℝ) :
    realCauchyFunction φ ((ξ : ℂ) + (η : ℂ) * I) = realCauchyIntegral φ ξ η := rfl

/-- The genuine complex derivative, without a supplied holomorphy or derivative premise. -/
theorem hasDerivAt_realCauchyFunction {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hcompact : HasCompactSupport φ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (realCauchyFunction φ)
      (((1 / Real.pi : ℝ) : ℂ) * ∫ x : ℝ, (φ x : ℂ) / ((x : ℂ) - z) ^ 2) z := by
  let δ : ℝ := z.im / 2
  have hδ : 0 < δ := half_pos hz
  have hsep (w : ℂ) (hw : w ∈ Metric.ball z δ) (x : ℝ) : δ ≤ ‖(x : ℂ) - w‖ := by
    have hw' : ‖w - z‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have him : |w.im - z.im| ≤ ‖w - z‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - z)
    have hwim : δ ≤ w.im := by
      have := neg_le_abs (w.im - z.im)
      dsimp [δ] at *
      linarith
    have habs : |w.im| ≤ ‖(x : ℂ) - w‖ := by
      simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] using
        Complex.abs_im_le_norm ((x : ℂ) - w)
    exact hwim.trans ((le_abs_self _).trans habs)
  have hnorm : Integrable (fun x : ℝ => ‖(φ x : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      (hφ.integrable_of_hasCompactSupport hcompact).norm
  have hmeas (w : ℂ) :
      AEStronglyMeasurable (fun x : ℝ => (φ x : ℂ) / ((x : ℂ) - w)) :=
    ((Complex.continuous_ofReal.comp hφ).measurable.div
      (Complex.continuous_ofReal.measurable.sub_const w)).aestronglyMeasurable
  have hmeas2 (w : ℂ) :
      AEStronglyMeasurable (fun x : ℝ => (φ x : ℂ) / ((x : ℂ) - w) ^ 2) :=
    ((Complex.continuous_ofReal.comp hφ).measurable.div
      ((Complex.continuous_ofReal.measurable.sub_const w).pow_const 2)).aestronglyMeasurable
  have hint : Integrable (fun x : ℝ => (φ x : ℂ) / ((x : ℂ) - z)) := by
    apply (hnorm.div_const δ).mono' (hmeas z)
    exact Eventually.of_forall fun x => by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hδ
        (hsep z (Metric.mem_ball_self hδ) x)
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w (x : ℝ) => (φ x : ℂ) / ((x : ℂ) - w))
    (F' := fun w (x : ℝ) => (φ x : ℂ) / ((x : ℂ) - w) ^ 2)
    (bound := fun x : ℝ => ‖(φ x : ℂ)‖ / δ ^ 2)
    (Metric.ball_mem_nhds z hδ) (Eventually.of_forall hmeas) hint (hmeas2 z)
    (Eventually.of_forall fun x w hw => by
      have hs := hsep w hw x
      rw [norm_div, norm_pow]
      apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hδ)
      nlinarith [norm_nonneg ((x : ℂ) - w)])
    (hnorm.div_const (δ ^ 2))
    (Eventually.of_forall fun x w hw => by
      have hs := hsep w hw x
      have hne : (x : ℂ) - w ≠ 0 := by
        intro hzero
        rw [hzero, norm_zero] at hs
        linarith
      have h := (((hasDerivAt_id w).const_sub (x : ℂ)).inv hne).const_mul (φ x : ℂ)
      convert h using 1
      · rfl
      · simp only [id, neg_neg]
        ring)
  exact hkey.2.const_mul ((1 / Real.pi : ℝ) : ℂ)

/-- The same original Cauchy function is genuinely holomorphic on the upper half-plane. -/
theorem differentiableOn_realCauchyFunction {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hcompact : HasCompactSupport φ) :
    DifferentiableOn ℂ (realCauchyFunction φ) {z : ℂ | 0 < z.im} :=
  fun _z hz => (hasDerivAt_realCauchyFunction hφ hcompact hz).differentiableAt.differentiableWithinAt

/-- The two harmonicity assertions used before the book's `W` calculation. -/
theorem harmonicAt_realCauchyFunction_re_im {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hcompact : HasCompactSupport φ) {z : ℂ} (hz : 0 < z.im) :
    InnerProductSpace.HarmonicAt (fun w => (realCauchyFunction φ w).re) z ∧
      InnerProductSpace.HarmonicAt (fun w => (realCauchyFunction φ w).im) z := by
  have ha := (differentiableOn_realCauchyFunction hφ hcompact).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_im) z hz
  exact ⟨ha.harmonicAt_re, ha.harmonicAt_im⟩

end LowDimensionalTopology.Geometry.Quasiconformal
