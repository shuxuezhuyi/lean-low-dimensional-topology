module

public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalInversion
public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalReciprocalGreen
public import LowDimensionalTopology.Geometry.Quasiconformal.UnitCircleInversion

/-!
# The actual circle and reciprocal area terms

Reciprocal substitution is applied to the same canonical map and its actual
inversion conjugate. The original boundary Cauchy integral then splits into
two genuine boundary coefficients and the literal reciprocal area integral.
The parameter is inside the unit disc; boundary normalization is separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- The inverted circle term of the same original canonical map equals the
literal second area term. The reciprocal conjugate is not supplied as an
extra solution: normalized uniqueness constructs its actual coefficient. -/
theorem normalizedSolution_inverted_circle_area
    {p : ℝ} (hp : 8 < p) (μ : MeasurableBeltramiBall)
    (hsmall : ‖μ.val‖ * smoothHilbertNorm p < 1)
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    (∮ z in C(0, 1), MeasurableBeltramiBall.normalizedSolution μ z /
      (z ^ 2 * (z - ζ))) = -(2 * I) * ∫ z in ball (0 : ℂ) 1,
        z * dzbar (nxInvConj (MeasurableBeltramiBall.normalizedSolution μ)) z /
          ((nxInvConj (MeasurableBeltramiBall.normalizedSolution μ) z) ^ 2 *
            (1 - z * ζ)) := by
  let F := MeasurableBeltramiBall.normalizedSolution μ
  obtain ⟨ν, hνnorm, hν⟩ := normalizedSolution_inversion_exists μ
  have hp1 : 1 < p := lt_trans (by norm_num) hp
  have hCp : 0 ≤ smoothHilbertNorm p := by
    rw [smoothHilbertNorm_eq_hilbertNorm hp1]
    exact hilbertNorm_nonneg p
  have hνsmall : ‖ν.val‖ * smoothHilbertNorm p < 1 :=
    (mul_le_mul_of_nonneg_right hνnorm hCp).trans_lt hsmall
  have hfun : (MeasurableBeltramiBall.normalizedSolution ν : ℂ → ℂ) = nxInvConj F :=
    funext hν
  have hgreen := (normalizedSolution_reciprocal_green hp ν hνsmall hζ).2
  let b : ℂ → ℂ := fun z => F z / (z ^ 2 * (z - ζ))
  have hcircle : (∮ z in C(0, 1), canonicalReciprocalKernel ν ζ z) =
      ∮ z in C(0, 1), b (z⁻¹) / z ^ 2 := by
    apply circleIntegral.integral_congr zero_le_one
    intro z hz
    have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
    have hfac : 1 - z * ζ = z * (z⁻¹ - ζ) := by
      rw [mul_sub, mul_inv_cancel₀ hz0]
    have hpow : (z⁻¹) ^ 2 * z ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hz0, one_pow]
    calc
      canonicalReciprocalKernel ν ζ z = F (z⁻¹) / (z⁻¹ - ζ) := by
        dsimp only [canonicalReciprocalKernel]
        rw [hν, hfac, div_mul_eq_div_div, div_inv_eq_mul,
          mul_div_mul_left _ _ hz0]
      _ = b (z⁻¹) / z ^ 2 := by
        dsimp only [b]
        rw [div_div]
        have hden : ((z⁻¹) ^ 2 * (z⁻¹ - ζ)) * z ^ 2 = z⁻¹ - ζ := by
          calc
            _ = (z⁻¹ - ζ) * ((z⁻¹) ^ 2 * z ^ 2) := by ring
            _ = _ := by rw [hpow, mul_one]
        rw [hden]
  have hinvert : (∮ z in C(0, 1), canonicalReciprocalKernel ν ζ z) =
      ∮ z in C(0, 1), b z := hcircle.trans (circleIntegral_unit_inversion b)
  rw [hinvert, hfun] at hgreen
  exact hgreen

/-- Partial fractions on the actual unit circle, with all three summands
circle integrable. The two undetermined coefficients are genuine integrals
of the original function; no polynomial representation is assumed. -/
theorem circleIntegral_cauchy_partial_fractions
    (F : ℂ → ℂ) (hF : ContinuousOn F (sphere (0 : ℂ) 1))
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    (∮ z in C(0, 1), F z / (z - ζ)) = (∮ z in C(0, 1), F z / z) +
      ζ * (∮ z in C(0, 1), F z / z ^ 2) +
      ζ ^ 2 * (∮ z in C(0, 1), F z / (z ^ 2 * (z - ζ))) := by
  have hz0 : ∀ z ∈ sphere (0 : ℂ) 1, z ≠ 0 := by
    intro z hz
    apply norm_ne_zero_iff.mp
    rw [mem_sphere_zero_iff_norm.mp hz]
    norm_num
  have hzζ : ∀ z ∈ sphere (0 : ℂ) 1, z - ζ ≠ 0 := by
    intro z hz
    apply sub_ne_zero.mpr
    intro heq
    have hn := mem_ball_zero_iff.mp hζ
    rw [← heq, mem_sphere_zero_iff_norm.mp hz] at hn
    exact (lt_irrefl (1 : ℝ)) hn
  have hA : ContinuousOn (fun z => F z / z) (sphere (0 : ℂ) 1) :=
    hF.div continuousOn_id hz0
  have hB : ContinuousOn (fun z => F z / z ^ 2) (sphere (0 : ℂ) 1) :=
    hF.div (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (hz0 z hz))
  have hC : ContinuousOn (fun z => F z / (z ^ 2 * (z - ζ))) (sphere (0 : ℂ) 1) :=
    hF.div ((continuousOn_id.pow 2).mul (continuousOn_id.sub continuousOn_const))
      (fun z hz => mul_ne_zero (pow_ne_zero 2 (hz0 z hz)) (hzζ z hz))
  have hBζ : CircleIntegrable (fun z => ζ * (F z / z ^ 2)) 0 1 :=
    (continuousOn_const.mul hB).circleIntegrable zero_le_one
  have hCζ : CircleIntegrable (fun z => ζ ^ 2 * (F z / (z ^ 2 * (z - ζ)))) 0 1 :=
    (continuousOn_const.mul hC).circleIntegrable zero_le_one
  have hAB : CircleIntegrable (fun z => F z / z + ζ * (F z / z ^ 2)) 0 1 := by
    exact CircleIntegrable.fun_add (hA.circleIntegrable zero_le_one) hBζ
  calc
    (∮ z in C(0, 1), F z / (z - ζ)) = ∮ z in C(0, 1),
        (F z / z + ζ * (F z / z ^ 2)) + ζ ^ 2 * (F z / (z ^ 2 * (z - ζ))) := by
      apply circleIntegral.integral_congr zero_le_one
      intro z hz
      field_simp [hz0 z hz, hzζ z hz]; ring
    _ = _ := by
      rw [circleIntegral.integral_add hAB hCζ,
        circleIntegral.integral_add (hA.circleIntegrable zero_le_one) hBζ,
        circleIntegral.integral_const_mul, circleIntegral.integral_const_mul]

end LowDimensionalTopology.Geometry.Quasiconformal
