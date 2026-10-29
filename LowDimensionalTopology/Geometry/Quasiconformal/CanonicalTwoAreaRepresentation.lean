module

public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalCircleAreaDecomposition
public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalAreaContinuity
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# The two-area formula for every original canonical plane solution

The prescribed exponent is retained throughout. Actual circle partial
fractions and reciprocal Green determine an affine boundary term. The
actual area integrals are continuous on the closed parameter disc, so the
normalization at one is taken as a genuine boundary limit. The final two
literal integrands are absolutely integrable, including their boundary
normalizing kernels.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

private theorem normalizedSolution_twoArea_combination
    {p : ℝ} (hp : 8 < p) (μ : MeasurableBeltramiBall)
    (hsmall : ‖μ.val‖ * smoothHilbertNorm p < 1)
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    MeasurableBeltramiBall.normalizedSolution μ ζ = ζ - (1 / Real.pi : ℂ) *
      (canonicalFirstArea μ ζ - ζ * canonicalFirstArea μ 1 +
        (ζ - 1) * canonicalFirstArea μ 0) - (1 / Real.pi : ℂ) *
      (ζ ^ 2 * (∫ z in ball (0 : ℂ) 1,
        z * dzbar (nxInvConj (MeasurableBeltramiBall.normalizedSolution μ)) z /
          ((nxInvConj (MeasurableBeltramiBall.normalizedSolution μ) z) ^ 2 * (1 - z * ζ))) -
        ζ * (∫ z in ball (0 : ℂ) 1,
          z * dzbar (nxInvConj (MeasurableBeltramiBall.normalizedSolution μ)) z /
            ((nxInvConj (MeasurableBeltramiBall.normalizedSolution μ) z) ^ 2 * (1 - z)))) := by
  let F := MeasurableBeltramiBall.normalizedSolution μ
  let A := canonicalFirstArea μ
  let R : ℂ → ℂ := fun η => ∫ z in ball (0 : ℂ) 1,
    z * dzbar (nxInvConj F) z / ((nxInvConj F z) ^ 2 * (1 - z * η))
  let C : ℂ := 1 / (2 * Real.pi * I)
  let c : ℂ := 1 / Real.pi
  let b : ℂ := C * ∮ z in C(0, 1), F z / z
  let a : ℂ := C * ∮ z in C(0, 1), F z / z ^ 2
  have hp2 : 2 < p := lt_trans (by norm_num) hp
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hC : C * (-(2 * I)) = -c := by
    dsimp only [C, c]
    field_simp [hπ, I_ne_zero]
  have hpoly : EqOn F (fun η => b + η * a - c * A η - c * η ^ 2 * R η)
      (ball (0 : ℂ) 1) := by
    intro η hη
    have hP := (normalizedSolution_pompeiu_sameExponent hp2 μ hsmall hη).2
    rw [circleIntegral_cauchy_partial_fractions F F.continuous.continuousOn hη,
      normalizedSolution_inverted_circle_area hp μ hsmall hη] at hP
    calc
      F η = C * ((∮ z in C(0, 1), F z / z) +
          η * (∮ z in C(0, 1), F z / z ^ 2) + η ^ 2 * (-(2 * I) * R η)) -
          c * A η := hP
      _ = b + η * a - c * A η + η ^ 2 * (C * (-(2 * I))) * R η := by
        dsimp only [a, b]
        ring
      _ = b + η * a - c * A η - c * η ^ 2 * R η := by rw [hC]; ring
  have hA : Continuous A := continuous_canonicalFirstArea hp2 μ hsmall
  have hR : ContinuousOn R (closedBall (0 : ℂ) 1) := by
    obtain ⟨ν, hνnorm, hν⟩ := normalizedSolution_inversion_exists μ
    have hp1 : 1 < p := lt_trans one_lt_two hp2
    have hCp : 0 ≤ smoothHilbertNorm p := by
      rw [smoothHilbertNorm_eq_hilbertNorm hp1]
      exact hilbertNorm_nonneg p
    have hνsmall : ‖ν.val‖ * smoothHilbertNorm p < 1 :=
      (mul_le_mul_of_nonneg_right hνnorm hCp).trans_lt hsmall
    have hfun : (MeasurableBeltramiBall.normalizedSolution ν : ℂ → ℂ) = nxInvConj F :=
      funext hν
    have heq : R = canonicalReciprocalArea ν := by
      funext η
      dsimp only [R, canonicalReciprocalArea]
      rw [hfun]
    rw [heq]
    exact continuousOn_canonicalReciprocalArea hp ν hνsmall
  have hright : ContinuousOn (fun η => b + η * a - c * A η - c * η ^ 2 * R η)
      (closedBall (0 : ℂ) 1) :=
    ((continuousOn_const.add (continuousOn_id.mul continuousOn_const)).sub
      (continuousOn_const.mul hA.continuousOn)).sub
        ((continuousOn_const.mul (continuousOn_id.pow 2)).mul hR)
  have hclosed : EqOn F (fun η => b + η * a - c * A η - c * η ^ 2 * R η)
      (closedBall (0 : ℂ) 1) :=
    hpoly.of_subset_closure F.continuous.continuousOn hright ball_subset_closedBall
      (by rw [closure_ball (0 : ℂ) one_ne_zero])
  have hF0 : F 0 = 0 := (MeasurableBeltramiBall.normalizedSolution_spec μ).1.2.2.1
  have hF1 : F 1 = 1 := (MeasurableBeltramiBall.normalizedSolution_spec μ).1.2.2.2.1
  have hb : b = c * A 0 := by
    have hh := hpoly (show (0 : ℂ) ∈ ball (0 : ℂ) 1 from mem_ball_self zero_lt_one)
    have heq : 0 = b - c * A 0 := by
      simpa only [hF0, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0),
        mul_zero, add_zero, sub_zero] using hh
    exact sub_eq_zero.mp heq.symm
  have ha : a = 1 - b + c * A 1 + c * R 1 := by
    have hh := hclosed (by simp : (1 : ℂ) ∈ closedBall (0 : ℂ) 1)
    simp only [hF1, one_mul, one_pow, mul_one] at hh
    linear_combination -hh
  have hfinal : F ζ = ζ - c * (A ζ - ζ * A 1 + (ζ - 1) * A 0) -
      c * (ζ ^ 2 * R ζ - ζ * R 1) := by
    calc
      F ζ = b + ζ * a - c * A ζ - c * ζ ^ 2 * R ζ := hpoly hζ
      _ = _ := by rw [ha, hb]; ring
  simpa only [F, A, R, c, mul_one] using hfinal

/-- The two literal area kernels in the normalized representation are
absolutely integrable for the same original coefficient and prescribed p.
The normalization poles zero and one are included in this assertion. -/
theorem normalizedSolution_twoArea_integrable
    {p : ℝ} (hp : 8 < p) (μ : MeasurableBeltramiBall)
    (hsmall : ‖μ.val‖ * smoothHilbertNorm p < 1)
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    IntegrableOn (fun z => dzbar (MeasurableBeltramiBall.normalizedSolution μ) z *
      (1 / (z - ζ) - ζ / (z - 1) + (ζ - 1) / z)) (ball (0 : ℂ) 1) ∧
      IntegrableOn (fun z =>
        dzbar (nxInvConj (MeasurableBeltramiBall.normalizedSolution μ)) z /
          (nxInvConj (MeasurableBeltramiBall.normalizedSolution μ) z) ^ 2 *
            (ζ ^ 2 * z / (1 - z * ζ) - ζ * z / (1 - z))) (ball (0 : ℂ) 1) := by
  let F := MeasurableBeltramiBall.normalizedSolution μ
  let G : ℂ → ℂ := nxInvConj F
  have hp2 : 2 < p := lt_trans (by norm_num) hp
  obtain ⟨_, hbar, _⟩ := normalizedSolution_sameExponent_localLp hp2 μ hsmall
  have harea : ∀ η : ℂ, IntegrableOn (fun z => dzbar F z / (z - η)) (ball (0 : ℂ) 1) := by
    intro η
    apply pompeiu_area_integrable_of_local_memLp (U := closedBall (0 : ℂ) 3) hp2
      (closedBall_subset_closedBall (by norm_num))
    intro K hK _
    exact hbar.mono_measure (Measure.restrict_mono hK le_rfl)
  have hfirst := ((harea ζ).sub ((harea 1).const_mul ζ)).add ((harea 0).const_mul (ζ - 1))
  have hfirstEq : (fun z => dzbar F z *
      (1 / (z - ζ) - ζ / (z - 1) + (ζ - 1) / z)) =
      (fun z => dzbar F z / (z - ζ) - ζ * (dzbar F z / (z - 1)) +
        (ζ - 1) * (dzbar F z / (z - 0))) := by
    funext z
    simp only [sub_zero, div_eq_mul_inv, one_mul]
    ring
  refine ⟨hfirstEq.symm ▸ hfirst, ?_⟩
  obtain ⟨ν, hνnorm, hν⟩ := normalizedSolution_inversion_exists μ
  have hfun : (MeasurableBeltramiBall.normalizedSolution ν : ℂ → ℂ) = G := funext hν
  have hCp : 0 ≤ smoothHilbertNorm p := by
    rw [smoothHilbertNorm_eq_hilbertNorm (lt_trans one_lt_two hp2)]
    exact hilbertNorm_nonneg p
  have hνsmall : ‖ν.val‖ * smoothHilbertNorm p < 1 :=
    (mul_le_mul_of_nonneg_right hνnorm hCp).trans_lt hsmall
  have hT : ∀ η ∈ closedBall (0 : ℂ) 1, IntegrableOn
      (fun z => z * dzbar G z / (G z ^ 2 * (1 - z * η))) (ball (0 : ℂ) 1) := by
    intro η hη
    have hi := normalizedSolution_reciprocal_area_integrable hp ν hνsmall hη
    rwa [hfun] at hi
  have hT1 : IntegrableOn (fun z => z * dzbar G z / (G z ^ 2 * (1 - z)))
      (ball (0 : ℂ) 1) := by
    simpa only [mul_one] using hT 1 (by simp)
  have hsecond := ((hT ζ (ball_subset_closedBall hζ)).const_mul (ζ ^ 2)).sub
    (hT1.const_mul ζ)
  have hsecondEq : (fun z => dzbar G z / G z ^ 2 *
      (ζ ^ 2 * z / (1 - z * ζ) - ζ * z / (1 - z))) =
      (fun z => ζ ^ 2 * (z * dzbar G z / (G z ^ 2 * (1 - z * ζ))) -
        ζ * (z * dzbar G z / (G z ^ 2 * (1 - z)))) := by
    funext z
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  exact hsecondEq.symm ▸ hsecond

/-- The full two-area representation of the original canonical map, with
its literal reciprocal conjugate. The original coefficient is arbitrary on
the whole plane. The same prescribed p>8 and literal C_p condition are the
only analytic smallness assumptions; both displayed integrals are genuine
absolute integrals by `normalizedSolution_twoArea_integrable`. -/
theorem normalizedSolution_twoArea_representation
    {p : ℝ} (hp : 8 < p) (μ : MeasurableBeltramiBall)
    (hsmall : ‖μ.val‖ * smoothHilbertNorm p < 1)
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    MeasurableBeltramiBall.normalizedSolution μ ζ = ζ - (1 / Real.pi : ℂ) *
      (∫ z in ball (0 : ℂ) 1, dzbar (MeasurableBeltramiBall.normalizedSolution μ) z *
        (1 / (z - ζ) - ζ / (z - 1) + (ζ - 1) / z)) - (1 / Real.pi : ℂ) *
      (∫ z in ball (0 : ℂ) 1,
        dzbar (nxInvConj (MeasurableBeltramiBall.normalizedSolution μ)) z /
          (nxInvConj (MeasurableBeltramiBall.normalizedSolution μ) z) ^ 2 *
            (ζ ^ 2 * z / (1 - z * ζ) - ζ * z / (1 - z))) := by
  let F := MeasurableBeltramiBall.normalizedSolution μ
  let G : ℂ → ℂ := nxInvConj F
  have hp2 : 2 < p := lt_trans (by norm_num) hp
  obtain ⟨_, hbar, _⟩ := normalizedSolution_sameExponent_localLp hp2 μ hsmall
  have harea : ∀ η : ℂ, IntegrableOn (fun z => dzbar F z / (z - η)) (ball (0 : ℂ) 1) := by
    intro η
    apply pompeiu_area_integrable_of_local_memLp (U := closedBall (0 : ℂ) 3) hp2
      (closedBall_subset_closedBall (by norm_num))
    intro K hK _
    exact hbar.mono_measure (Measure.restrict_mono hK le_rfl)
  have hfirst : (∫ z in ball (0 : ℂ) 1,
      dzbar F z * (1 / (z - ζ) - ζ / (z - 1) + (ζ - 1) / z)) =
      canonicalFirstArea μ ζ - ζ * canonicalFirstArea μ 1 +
        (ζ - 1) * canonicalFirstArea μ 0 := by
    have heq : (fun z => dzbar F z * (1 / (z - ζ) - ζ / (z - 1) + (ζ - 1) / z)) =
        (fun z => dzbar F z / (z - ζ) - ζ * (dzbar F z / (z - 1)) +
          (ζ - 1) * (dzbar F z / (z - 0))) := by
      funext z
      simp only [sub_zero, div_eq_mul_inv, one_mul]
      ring
    rw [heq, integral_add ((harea ζ).sub' ((harea 1).const_mul ζ))
      ((harea 0).const_mul (ζ - 1)), integral_sub (harea ζ) ((harea 1).const_mul ζ),
      integral_const_mul, integral_const_mul]
    rfl
  obtain ⟨ν, hνnorm, hν⟩ := normalizedSolution_inversion_exists μ
  have hfun : (MeasurableBeltramiBall.normalizedSolution ν : ℂ → ℂ) = G := funext hν
  have hCp : 0 ≤ smoothHilbertNorm p := by
    rw [smoothHilbertNorm_eq_hilbertNorm (lt_trans one_lt_two hp2)]
    exact hilbertNorm_nonneg p
  have hνsmall : ‖ν.val‖ * smoothHilbertNorm p < 1 :=
    (mul_le_mul_of_nonneg_right hνnorm hCp).trans_lt hsmall
  have hT : ∀ η ∈ closedBall (0 : ℂ) 1, IntegrableOn
      (fun z => z * dzbar G z / (G z ^ 2 * (1 - z * η))) (ball (0 : ℂ) 1) := by
    intro η hη
    have hi := normalizedSolution_reciprocal_area_integrable hp ν hνsmall hη
    rwa [hfun] at hi
  have hT1 : IntegrableOn (fun z => z * dzbar G z / (G z ^ 2 * (1 - z)))
      (ball (0 : ℂ) 1) := by
    simpa only [mul_one] using hT 1 (by simp)
  have hsecond : (∫ z in ball (0 : ℂ) 1, dzbar G z / G z ^ 2 *
      (ζ ^ 2 * z / (1 - z * ζ) - ζ * z / (1 - z))) =
      ζ ^ 2 * (∫ z in ball (0 : ℂ) 1, z * dzbar G z / (G z ^ 2 * (1 - z * ζ))) -
        ζ * (∫ z in ball (0 : ℂ) 1, z * dzbar G z / (G z ^ 2 * (1 - z))) := by
    have heq : (fun z => dzbar G z / G z ^ 2 *
        (ζ ^ 2 * z / (1 - z * ζ) - ζ * z / (1 - z))) =
        (fun z => ζ ^ 2 * (z * dzbar G z / (G z ^ 2 * (1 - z * ζ))) -
          ζ * (z * dzbar G z / (G z ^ 2 * (1 - z)))) := by
      funext z
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq, integral_sub ((hT ζ (ball_subset_closedBall hζ)).const_mul (ζ ^ 2))
      (hT1.const_mul ζ), integral_const_mul, integral_const_mul]
  rw [hfirst, hsecond]
  exact normalizedSolution_twoArea_combination hp μ hsmall hζ

end LowDimensionalTopology.Geometry.Quasiconformal
