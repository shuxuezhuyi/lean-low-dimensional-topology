module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertKernelConvolution
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertBoundaryFactor

/-!
# The radial profile of the two-pole inverse-norm integral

Polar coordinates apply to the actual integrable two-pole function.
Outside the unit radius, its angular density is continuous and is the
derivative of the disc integral with respect to its radius.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The inverse-distance product with its two poles at zero and one. -/
def inverseNormUnitPoleProduct (t : ℂ) : ℂ :=
  inverseNormKernel t * inverseNormKernel (1 - t)

/-- The disc integral of the two fixed inverse-distance singularities. -/
def inverseNormUnitPoleDiscPotential (R : ℝ) : ℂ :=
  ∫ t in Metric.ball (0 : ℂ) R, inverseNormUnitPoleProduct t

/-- The angular density that remains after cancellation of the radial
Jacobian against the inverse distance to zero. -/
def inverseNormUnitPoleRadialDensity (r : ℝ) : ℂ :=
  ∫ θ in Ioo (-Real.pi) Real.pi,
    inverseNormKernel ((1 : ℂ) - circleMap 0 r θ)

theorem measurable_inverseNormUnitPoleProduct :
    Measurable inverseNormUnitPoleProduct :=
  measurable_inverseNormKernel.mul
    (measurable_inverseNormKernel.comp (measurable_const.sub measurable_id))

theorem integrableOn_inverseNormUnitPoleProduct_ball {R : ℝ} (hR : 0 < R) :
    IntegrableOn inverseNormUnitPoleProduct (Metric.ball (0 : ℂ) R) := by
  have h := integrableOn_inverseNormKernel_mul_ball hR (by norm_num : (0 : ℂ) ≠ 1)
  convert h using 1
  funext t
  simp only [inverseNormUnitPoleProduct, sub_zero]
  rw [show inverseNormKernel (1 - t) = inverseNormKernel (t - 1) by
    simp only [inverseNormKernel, norm_sub_rev]]

private theorem inverseNormUnitPole_polar_inner {r : ℝ} (hr : 0 < r) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      (r : ℂ) * inverseNormUnitPoleProduct (Complex.polarCoord.symm (r, θ))) =
        inverseNormUnitPoleRadialDensity r := by
  apply integral_congr_ae
  filter_upwards with θ
  have hc : Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
    simpa only [add_zero] using LiZhongQC.polarCoord_symm_add_eq_circleMap 0 r θ
  rw [hc, inverseNormUnitPoleProduct, ← mul_assoc]
  have hcancel : (r : ℂ) * inverseNormKernel (circleMap 0 r θ) = 1 := by
    simp only [inverseNormKernel, norm_circleMap_zero, abs_of_pos hr]
    exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
  rw [hcancel, one_mul]

/-- The radial density is integrable across the isolated singular radius
because it comes from an actually integrable function on the plane. -/
theorem intervalIntegrable_inverseNormUnitPoleRadialDensity {R : ℝ} (hR : 0 < R) :
    IntervalIntegrable inverseNormUnitPoleRadialDensity volume 0 R := by
  have hp := LiZhongQC.integrableOn_polar_of_integrableOn_ball
    measurable_inverseNormUnitPoleProduct (integrableOn_inverseNormUnitPoleProduct_ball hR)
  change Integrable _ (volume.restrict (Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi)) at hp
  rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at hp
  have hi := hp.integral_prod_left
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hR.le).mpr
  refine hi.congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with r hr
  exact inverseNormUnitPole_polar_inner hr.1

/-- Polar coordinates for the singular disc integral, with genuine
integrability supplying the Fubini step. -/
theorem inverseNormUnitPoleDiscPotential_eq_radialIntegral {R : ℝ} (hR : 0 < R) :
    inverseNormUnitPoleDiscPotential R =
      ∫ r in (0 : ℝ)..R, inverseNormUnitPoleRadialDensity r := by
  have hp := LiZhongQC.integrableOn_polar_of_integrableOn_ball
    measurable_inverseNormUnitPoleProduct (integrableOn_inverseNormUnitPoleProduct_ball hR)
  have heq : inverseNormUnitPoleDiscPotential R =
      ∫ r in Ioo (0 : ℝ) R, inverseNormUnitPoleRadialDensity r := by
    rw [inverseNormUnitPoleDiscPotential, LiZhongQC.setIntegral_ball_zero_polar,
      LiZhongQC.setIntegral_polar_fubini' hp]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    exact inverseNormUnitPole_polar_inner hr.1
  rw [heq, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le]

theorem stronglyMeasurable_inverseNormUnitPoleRadialDensity :
    StronglyMeasurable inverseNormUnitPoleRadialDensity := by
  have hc : Continuous (fun p : ℝ × ℝ => (1 : ℂ) - circleMap 0 p.1 p.2) := by
    simp only [circleMap]
    fun_prop
  exact (measurable_inverseNormKernel.comp hc.measurable).stronglyMeasurable.integral_prod_right'

/-- The angular density is continuous at every radius greater than one. -/
theorem continuousOn_inverseNormUnitPoleRadialDensity :
    ContinuousOn inverseNormUnitPoleRadialDensity (Ioi (1 : ℝ)) := by
  let : LocallyCompactSpace (Ioi (1 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  have hc : Continuous (fun p : Ioi (1 : ℝ) × ℝ =>
      (1 : ℂ) - circleMap 0 (p.1 : ℝ) p.2) := by
    simp only [circleMap]
    fun_prop
  have hne : ∀ p : Ioi (1 : ℝ) × ℝ,
      (‖(1 : ℂ) - circleMap 0 (p.1 : ℝ) p.2‖ : ℂ) ≠ 0 := by
    intro p
    apply Complex.ofReal_ne_zero.mpr
    have hp : (1 : ℝ) < (p.1 : ℝ) := p.1.property
    have h := norm_sub_norm_le (circleMap 0 (p.1 : ℝ) p.2) (1 : ℂ)
    rw [norm_circleMap_zero, abs_of_pos (lt_trans zero_lt_one hp), norm_one,
      norm_sub_rev] at h
    exact ne_of_gt (by linarith [hp] :
      0 < ‖(1 : ℂ) - circleMap 0 (p.1 : ℝ) p.2‖)
  have hf : Continuous (fun p : Ioi (1 : ℝ) × ℝ =>
      inverseNormKernel ((1 : ℂ) - circleMap 0 (p.1 : ℝ) p.2)) :=
    (Complex.continuous_ofReal.comp hc.norm).inv₀ hne
  have hi : Continuous (fun r : Ioi (1 : ℝ) =>
      ∫ θ in Icc (-Real.pi) Real.pi,
        inverseNormKernel ((1 : ℂ) - circleMap 0 (r : ℝ) θ)) :=
    continuous_parametric_integral_of_continuous (μ := (volume : Measure ℝ))
      (f := fun r : Ioi (1 : ℝ) => fun θ : ℝ =>
        inverseNormKernel ((1 : ℂ) - circleMap 0 (r : ℝ) θ)) hf
      (isCompact_Icc (a := -Real.pi) (b := Real.pi))
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert! hi using 1
  funext r
  exact integral_Icc_eq_integral_Ioo.symm

/-- The derivative in the radius is the actual angular integral. -/
theorem hasDerivAt_inverseNormUnitPoleDiscPotential {R : ℝ} (hR : 1 < R) :
    HasDerivAt inverseNormUnitPoleDiscPotential
      (inverseNormUnitPoleRadialDensity R) R := by
  have hR0 : 0 < R := lt_trans zero_lt_one hR
  have hd := intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_inverseNormUnitPoleRadialDensity hR0)
    stronglyMeasurable_inverseNormUnitPoleRadialDensity.stronglyMeasurableAtFilter
    (continuousOn_inverseNormUnitPoleRadialDensity.continuousAt (Ioi_mem_nhds hR))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hR0] with r hr
  exact inverseNormUnitPoleDiscPotential_eq_radialIntegral hr

/-- Shifting the periodic angular interval gives the usual full-circle
formula for the density. -/
theorem inverseNormUnitPoleRadialDensity_eq_fullCircle (r : ℝ) :
    inverseNormUnitPoleRadialDensity r =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), inverseNormKernel ((1 : ℂ) - circleMap 0 r θ) := by
  have hper : Function.Periodic
      (fun θ : ℝ => inverseNormKernel ((1 : ℂ) - circleMap 0 r θ)) (2 * Real.pi) := by
    intro θ
    change inverseNormKernel ((1 : ℂ) - circleMap 0 r (θ + 2 * Real.pi)) =
      inverseNormKernel ((1 : ℂ) - circleMap 0 r θ)
    rw [periodic_circleMap 0 r θ]
  rw [inverseNormUnitPoleRadialDensity, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  exact LiZhongQC.intervalIntegral_shift_period hper

end LowDimensionalTopology.Geometry.Quasiconformal
