module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertScaledDisc

/-!
# A finite-disc decomposition of the renormalized convolution

The two finite disc potentials use discs centered at their own poles.
Their difference is corrected by two integrals over the set differences
of the discs, together with the actual integrable far tail.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The correction for replacing a disc centered at `w` by a disc
centered at zero in the reference-pole integral. -/
def inverseNormRecenteringError (R : ℝ) (w z : ℂ) : ℂ :=
  (∫ t in Metric.ball w R \ Metric.ball (0 : ℂ) R,
    inverseNormKernel t * inverseNormKernel (z - t)) -
  ∫ t in Metric.ball (0 : ℂ) R \ Metric.ball w R,
    inverseNormKernel t * inverseNormKernel (z - t)

/-- The actual far tail of the renormalized convolution outside the
disc centered at its moving kernel pole. -/
def renormalizedInverseNormConvolutionTail (R : ℝ) (w z : ℂ) : ℂ :=
  ∫ t in (Metric.ball w R)ᶜ, renormalizedInverseNormConvolutionIntegrand z w t

private theorem ball_subset_origin_ball (w : ℂ) (R : ℝ) :
    Metric.ball w R ⊆ Metric.ball (0 : ℂ) (R + ‖w‖ + 1) := by
  intro t ht
  have htR : ‖t - w‖ < R := by simpa only [Metric.mem_ball, dist_eq_norm] using ht
  have htri : ‖t‖ ≤ ‖t - w‖ + ‖w‖ := by
    simpa only [sub_add_cancel] using norm_add_le (t - w) w
  simp only [Metric.mem_ball, dist_zero_right]
  linarith

/-- The reference two-pole product is integrable on every finite disc
centered at `w`. -/
theorem integrableOn_inverseNormReference_shiftedBall {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    IntegrableOn (fun t : ℂ => inverseNormKernel t * inverseNormKernel (z - t))
      (Metric.ball w R) := by
  have hi := integrableOn_inverseNormDiscPotential (R := R + ‖w‖ + 1)
    (by positivity) hz
  exact hi.mono_set (ball_subset_origin_ball w R)

/-- The first shifted two-pole integral is exactly the finite disc
potential at the difference of its two poles. -/
theorem integral_inverseNorm_shiftedBall (R : ℝ) (w z : ℂ) :
    (∫ t in Metric.ball w R,
      inverseNormKernel (t - w) * inverseNormKernel (z - t)) =
        inverseNormDiscPotential R (z - w) := by
  rw [LiZhongQC.setIntegral_ball_translate]
  apply integral_congr_ae
  filter_upwards with t
  simp only [add_sub_cancel_right]
  rw [show z - (t + w) = (z - w) - t by ring]

/-- Subtracting the common intersection expresses the change of center
as two genuinely integrable set-difference terms. -/
theorem integral_inverseNormReference_shiftedBall_eq {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    (∫ t in Metric.ball w R,
      inverseNormKernel t * inverseNormKernel (z - t)) =
        inverseNormDiscPotential R z + inverseNormRecenteringError R w z := by
  have hw := integral_inter_add_sdiff
    (s := Metric.ball w R) (t := Metric.ball (0 : ℂ) R)
    measurableSet_ball (integrableOn_inverseNormReference_shiftedBall hR hz w)
  have h0 := integral_inter_add_sdiff
    (s := Metric.ball (0 : ℂ) R) (t := Metric.ball w R)
    measurableSet_ball (integrableOn_inverseNormDiscPotential hR hz)
  rw [inter_comm (Metric.ball w R) (Metric.ball (0 : ℂ) R)] at hw
  change (∫ t in Metric.ball w R,
      inverseNormKernel t * inverseNormKernel (z - t)) =
    (∫ t in Metric.ball (0 : ℂ) R,
      inverseNormKernel t * inverseNormKernel (z - t)) +
    ((∫ t in Metric.ball w R \ Metric.ball (0 : ℂ) R,
      inverseNormKernel t * inverseNormKernel (z - t)) -
      ∫ t in Metric.ball (0 : ℂ) R \ Metric.ball w R,
        inverseNormKernel t * inverseNormKernel (z - t))
  linear_combination h0 - hw

/-- The renormalized convolution splits into its two finite disc
potentials, the change-of-center correction, and the actual far tail. -/
theorem renormalizedInverseNormConvolution_eq_disc_sub_error_add_tail
    {R : ℝ} (hR : 0 < R) {z w : ℂ} (hz0 : z ≠ 0) (hzw : z ≠ w) :
    renormalizedInverseNormConvolution w z =
      inverseNormDiscPotential R (z - w) - inverseNormDiscPotential R z -
        inverseNormRecenteringError R w z + renormalizedInverseNormConvolutionTail R w z := by
  have hbig : 0 < R + ‖w‖ + 1 := by positivity
  have hA : IntegrableOn (fun t : ℂ =>
      inverseNormKernel (t - w) * inverseNormKernel (z - t)) (Metric.ball w R) := by
    have h := (integrableOn_inverseNormKernel_mul_ball hbig hzw.symm).mono_set
      (ball_subset_origin_ball w R)
    convert h using 1
    funext t
    rw [show inverseNormKernel (z - t) = inverseNormKernel (t - z) by
      simp only [inverseNormKernel, norm_sub_rev]]
  have hB := integrableOn_inverseNormReference_shiftedBall hR hz0 w
  have hfinite : (∫ t in Metric.ball w R,
      renormalizedInverseNormConvolutionIntegrand z w t) =
      inverseNormDiscPotential R (z - w) -
        (inverseNormDiscPotential R z + inverseNormRecenteringError R w z) := by
    have heq : renormalizedInverseNormConvolutionIntegrand z w =
        fun t : ℂ => inverseNormKernel (t - w) * inverseNormKernel (z - t) -
          inverseNormKernel t * inverseNormKernel (z - t) := by
      funext t
      exact sub_mul _ _ _
    rw [heq, integral_sub hA hB, integral_inverseNorm_shiftedBall,
      integral_inverseNormReference_shiftedBall_eq hR hz0 w]
  have hsplit := integral_add_compl (s := Metric.ball w R) measurableSet_ball
    (integrable_renormalizedInverseNormConvolutionIntegrand hz0 hzw)
  change (∫ t : ℂ, renormalizedInverseNormConvolutionIntegrand z w t) = _
  rw [← hsplit, hfinite]
  change inverseNormDiscPotential R (z - w) -
      (inverseNormDiscPotential R z + inverseNormRecenteringError R w z) +
      renormalizedInverseNormConvolutionTail R w z = _
  ring

end LowDimensionalTopology.Geometry.Quasiconformal
