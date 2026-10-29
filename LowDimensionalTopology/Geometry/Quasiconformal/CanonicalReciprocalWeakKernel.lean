module

public import LowDimensionalTopology.Geometry.Quasiconformal.WeakWirtingerPunctureCutoff
public import LowDimensionalTopology.Geometry.Quasiconformal.QuasiconformalWeakDerivatives
public import LowDimensionalTopology.Geometry.Teichmuller.MeasurableBeltrami

/-!
# The actual punctured reciprocal kernel has genuine weak derivatives

The canonical plane homeomorphism is composed with ordinary reciprocal
inversion off zero. A locally smooth rational multiplier then supplies the
literal antiholomorphic area integrand. Every weak witness is derived from
actual quasiconformality and the ordinary Wirtinger chain rule.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open scoped ContDiff
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- The literal rational reciprocal kernel, with no imposed puncture value. -/
def canonicalReciprocalKernel (μ : MeasurableBeltramiBall) (ζ z : ℂ) : ℂ :=
  z / (MeasurableBeltramiBall.normalizedSolution μ z * (1 - z * ζ))

/-- The kernel of the original canonical map has actual continuous punctured
trace and genuine weak data on an open neighborhood of the punctured closed
unit disc. Its antiholomorphic derivative is the literal desired integrand,
derived from the real chain rule, not supplied as a premise. -/
theorem canonicalReciprocalKernel_weak (μ : MeasurableBeltramiBall)
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    ∃ r : ℝ, 1 < r ∧ ∃ g h : ℂ → ℂ,
      ContinuousOn (canonicalReciprocalKernel μ ζ) (ball (0 : ℂ) r \ {0}) ∧
      HasDistributionalWirtingerDerivatives (canonicalReciprocalKernel μ ζ) g h
        (ball (0 : ℂ) r \ {0}) ∧
      h =ᵐ[volume.restrict (ball (0 : ℂ) r \ {0})]
        (fun z => -(z * dzbar (MeasurableBeltramiBall.normalizedSolution μ) z) /
          ((MeasurableBeltramiBall.normalizedSolution μ z) ^ 2 * (1 - z * ζ))) := by
  let F := MeasurableBeltramiBall.normalizedSolution μ
  let Q : ℂ → ℂ := fun z => (F z)⁻¹
  let φ : ℂ → ℂ := fun z => z / (1 - z * ζ)
  let r : ℝ := 2 / (1 + ‖ζ‖)
  let V : Set ℂ := ball (0 : ℂ) r \ {0}
  have hζn : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have hdn : 0 < 1 + ‖ζ‖ := by positivity
  have hr : 1 < r := (lt_div_iff₀ hdn).mpr (by linarith)
  have hrζ : r * ‖ζ‖ < 1 := by
    dsimp only [r]
    rw [div_mul_eq_mul_div, div_lt_one hdn]
    linarith
  have hden : ∀ z ∈ ball (0 : ℂ) r, 1 - z * ζ ≠ 0 := by
    intro z hz hzero
    have hn : ‖z * ζ‖ < 1 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (mem_ball_zero_iff.mp hz).le
        (norm_nonneg ζ)).trans_lt hrζ
    have heq : z * ζ = 1 := (sub_eq_zero.mp hzero).symm
    rw [heq, norm_one] at hn
    exact lt_irrefl _ hn
  have hV : IsOpen V := isOpen_ball.sdiff isClosed_singleton
  have hF := MeasurableBeltramiBall.normalizedSolution_spec μ
  have hF0 : F 0 = 0 := hF.1.2.2.1
  have hFn : ∀ z : ℂ, z ≠ 0 → F z ≠ 0 := by
    intro z hz hzero
    exact hz (F.injective (hzero.trans hF0.symm))
  have hinv : IsKQC (fun z : ℂ => z⁻¹) {0}ᶜ 1 :=
    isKQC_one_of_conformal isOpen_compl_singleton nx_inv_isConformalOnto
  have himage : F '' V ⊆ {(0 : ℂ)}ᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    exact hFn z (by simpa only [mem_singleton_iff] using hz.2)
  have hQ : IsKQC Q V ((1 + ‖μ.val‖) / (1 - ‖μ.val‖)) := by
    simpa only [mul_one, Function.comp_def, Q] using
      thm7_1_comp (nx_isKQC_restrict hF.2.1 hV (subset_univ V)) hinv himage
  have hwQ := quasiconformal_distributional_wirtinger_derivatives hQ
  have hφ : ContDiffOn ℝ ∞ φ V := by
    intro z hz
    have hid : ContDiffAt ℝ ∞ (fun w : ℂ => w) z := contDiffAt_id
    have hone : ContDiffAt ℝ ∞ (fun _ : ℂ => (1 : ℂ)) z := contDiffAt_const
    have hζc : ContDiffAt ℝ ∞ (fun _ : ℂ => ζ) z := contDiffAt_const
    have hd : ContDiffAt ℝ ∞ (fun w : ℂ => 1 - w * ζ) z :=
      hone.sub (hid.mul hζc)
    simpa only [φ, div_eq_mul_inv, Pi.inv_apply] using
      (hid.mul (hd.inv (hden z hz.1))).contDiffWithinAt
  have hφd : ∀ z ∈ V, DifferentiableAt ℂ φ z := by
    intro z hz
    have hid : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
    have hd : DifferentiableAt ℂ (fun w : ℂ => 1 - w * ζ) z :=
      (differentiableAt_const (1 : ℂ)).sub (hid.mul (differentiableAt_const ζ))
    exact hid.div hd (hden z hz.1)
  let g : ℂ → ℂ := fun z => φ z * dz Q z + dz φ z * Q z
  let h : ℂ → ℂ := fun z => φ z * dzbar Q z + dzbar φ z * Q z
  have hweak : HasDistributionalWirtingerDerivatives (fun z => φ z * Q z) g h V :=
    HasDistributionalWirtingerDerivatives.mul_contDiffOn hV hwQ hφ
  have hcont : ContinuousOn (fun z => φ z * Q z) V :=
    hφ.continuousOn.mul hQ.2.2.1.1
  have hfun : canonicalReciprocalKernel μ ζ = fun z => φ z * Q z := by
    funext z
    simp only [canonicalReciprocalKernel, φ, Q, div_eq_mul_inv, mul_inv_rev]
    ring
  have hdiff : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ F z := by
    simpa only [Measure.restrict_univ] using thm9_3_differentiable_ae hF.2.1
  have hbar : dzbar Q =ᵐ[volume.restrict V]
      (fun z => -dzbar F z / (F z) ^ 2) := by
    filter_upwards [ae_restrict_of_ae hdiff, ae_restrict_mem hV.measurableSet] with z hz hzin
    have hn : F z ≠ 0 := hFn z (by simpa only [mem_singleton_iff] using hzin.2)
    have hi := hasDerivAt_inv hn
    change dzbar ((fun w : ℂ => w⁻¹) ∘ F) z = _
    rw [eq6_2_dzbar_comp hz (hi.differentiableAt.restrictScalars ℝ),
      dz_eq_deriv hi.differentiableAt, hi.deriv,
      (cauchyRiemann_iff.mp hi.differentiableAt).2, zero_mul, add_zero, div_eq_mul_inv]
    ring
  refine ⟨r, hr, g, h, ?_, ?_, ?_⟩
  · rw [hfun]
    exact hcont
  · rw [hfun]
    exact hweak
  · filter_upwards [hbar, ae_restrict_mem hV.measurableSet] with z hz hzin
    dsimp only [h]
    rw [(cauchyRiemann_iff.mp (hφd z hzin)).2, zero_mul, add_zero, hz]
    dsimp only [φ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

end LowDimensionalTopology.Geometry.Quasiconformal
