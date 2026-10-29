module

public import LowDimensionalTopology.Geometry.Teichmuller.BersDirectionalKernel

/-!
# A uniform quadratic remainder for the actual Bers function

The actual scalar family is holomorphic on a fixed unit disc after normalizing
its coefficient. The pointwise Kraus bound, multiplied by the square of height,
is independent of the evaluation point. The scalar Taylor estimate consequently
gives a uniform quadratic remainder in the actual coefficient norm.

The analytic family, Kraus bound and scalar Taylor estimate are due to
Wu Xiaobin's Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0); see
`THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology MeasureTheory Metric
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergman

open LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- A coefficient with global bound one half gives a scalar quadratic estimate
on the fixed parameter disc. The constant is independent of the lower-plane point. -/
theorem bersFunction_scalar_weighted_remainder
    (ν : BeltramiGamma Γ)
    (hν : IsBeltramiCoeff ν.val.val univ (1 / 2 : ℝ))
    {z : ℂ} (hz : z ∈ lowerHalf) {t : ℂ} (ht : ‖t‖ < 1 / 2) :
    ‖bersFunction (fun w => t * ν.val.val w) z -
        t * bersDerivative ν.val.val z‖ * z.im ^ 2 ≤ 12 * ‖t‖ ^ 2 := by
  have hb : ∀ u ∈ ball (0 : ℂ) 1,
      IsBeltramiCoeff (fun w => b36_q_zero.val w + u * ν.val.val w)
        univ (1 / 2 : ℝ) := by
    intro u hu
    refine ⟨?_, ?_⟩
    · change AEStronglyMeasurable (fun w => 0 + u * ν.val.val w) _
      simpa only [zero_add] using hν.1.const_mul u
    · filter_upwards [hν.2] with w hw
      change ‖0 + u * ν.val.val w‖ ≤ (1 / 2 : ℝ)
      rw [zero_add, norm_mul]
      calc
        ‖u‖ * ‖ν.val.val w‖ ≤ 1 * (1 / 2 : ℝ) :=
          mul_le_mul (mem_ball_zero_iff.mp hu).le hw (norm_nonneg _) zero_le_one
        _ = (1 / 2 : ℝ) := one_mul _
  let family : ℂ → BeltramiH := b36_q_fam b36_q_zero ν.val
  have hfamily (u : ℂ) (hu : u ∈ ball (0 : ℂ) 1) :
      (family u).val = fun w => u * ν.val.val w := by
    simpa only [family, b36_q_zero, Pi.zero_apply, zero_add] using
      b36_q_fam_val b36_q_zero ν.val (by norm_num : 0 ≤ (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) < 1) hb hu
  obtain ⟨hkP, hhol⟩ := b36_q_fam_hyps b36_q_zero ν.val
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1) hb
  let φ : ℂ → ℂ := fun u => schwarzian (normalizedSolution (family u).val) z
  have hφ : DifferentiableOn ℂ φ (ball (0 : ℂ) 1) :=
    b36_q_schwarzian_holo isOpen_ball
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1) hkP hhol hz
  have heq (u : ℂ) (hu : u ∈ ball (0 : ℂ) 1) :
      φ u = bersFunction (fun w => u * ν.val.val w) z := by
    change schwarzian (normalizedSolution (family u).val) z = _
    rw [hfamily u hu, bersFunction, indicator_of_mem hz]
  have hraw : HasDerivAt
      (fun u : ℂ => bersFunction (fun w => u * ν.val.val w) z)
      (bersDerivative ν.val.val z) 0 :=
    (b36_q_main (fun σ _ hw => bersDerivative_eq_cauchyT_third σ hw) ν).2 ν z hz
  have hd : HasDerivAt φ (bersDerivative ν.val.val z) 0 := by
    apply hraw.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds
      (mem_ball_self (by norm_num : 0 < (1 : ℝ)))] with u hu
    exact heq u hu
  have hφzero : φ 0 = 0 := by
    change schwarzian (normalizedSolution (b36_q_fam b36_q_zero ν.val 0).val) z = 0
    rw [b36_q_F0 ν.val (by norm_num : 0 < (1 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1) hb,
      bB_l_schwarzian_id]
  have hweight : ‖((z.im ^ 2 : ℝ) : ℂ)‖ = z.im ^ 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  let g : ℂ → ℂ := fun u => φ u * ((z.im ^ 2 : ℝ) : ℂ)
  have hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1) := hφ.mul_const _
  have hbound : ∀ u ∈ ball (0 : ℂ) 1, ‖g u‖ ≤ (3 / 2 : ℝ) := by
    intro u _
    change ‖schwarzian (normalizedSolution (family u).val) z *
      ((z.im ^ 2 : ℝ) : ℂ)‖ ≤ (3 / 2 : ℝ)
    rw [norm_mul, hweight]
    exact bB_sd_kraus_pt (family u) hz
  have hTaylor := bB_h0_taylor_le (c := (0 : ℂ)) (ε := 1) (M := 3 / 2)
    (by norm_num) hg hbound ht
  have hdg : HasDerivAt g
      (bersDerivative ν.val.val z * ((z.im ^ 2 : ℝ) : ℂ)) 0 := hd.mul_const _
  have htball : t ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (by linarith)
  calc
    ‖bersFunction (fun w => t * ν.val.val w) z -
        t * bersDerivative ν.val.val z‖ * z.im ^ 2 =
        ‖g (0 + t) - g 0 - t * deriv g 0‖ := by
      rw [zero_add, hdg.deriv]
      change _ = ‖φ t * ((z.im ^ 2 : ℝ) : ℂ) -
        φ 0 * ((z.im ^ 2 : ℝ) : ℂ) -
          t * (bersDerivative ν.val.val z * ((z.im ^ 2 : ℝ) : ℂ))‖
      rw [hφzero, zero_mul, sub_zero, heq t htball]
      have hfactor :
          bersFunction (fun w => t * ν.val.val w) z * ((z.im ^ 2 : ℝ) : ℂ) -
            t * (bersDerivative ν.val.val z * ((z.im ^ 2 : ℝ) : ℂ)) =
          (bersFunction (fun w => t * ν.val.val w) z -
            t * bersDerivative ν.val.val z) * ((z.im ^ 2 : ℝ) : ℂ) := by ring
      rw [hfactor, norm_mul, hweight]
    _ ≤ 8 * (3 / 2 : ℝ) / (1 : ℝ) ^ 2 * ‖t‖ ^ 2 := hTaylor
    _ = 12 * ‖t‖ ^ 2 := by ring

/-- Every nonzero sufficiently small actual compatible L-infinity class has
the same weighted quadratic remainder, uniformly at every lower-plane point.
The separate zero-class case is the elementary a.e.-zero normalization identity. -/
theorem bersFunction_weighted_remainder_of_ne_zero
    (μ : GammaMeasurableBeltrami.Space Γ) (hμ : μ ≠ 0) (hsmall : ‖μ‖ < 1 / 4)
    {z : ℂ} (hz : z ∈ lowerHalf) :
    ‖bersFunction (GammaMeasurableBeltrami.planeRepresentative μ.val) z -
        bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val) z‖ *
      z.im ^ 2 ≤ 48 * ‖μ‖ ^ 2 := by
  let κ : ℂ → ℂ := GammaMeasurableBeltrami.planeRepresentative μ.val
  have hn : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  let t : ℂ := ((2 * ‖μ‖ : ℝ) : ℂ)
  let c : ℂ := t⁻¹
  have ht0 : t ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_pos two_pos hn).ne'
  have htnorm : ‖t‖ = 2 * ‖μ‖ := by
    rw [show t = ((2 * ‖μ‖ : ℝ) : ℂ) from rfl, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hc : ‖c‖ = (2 * ‖μ‖)⁻¹ := by
    rw [show c = t⁻¹ from rfl, norm_inv, htnorm]
  have hcnorm : ‖c‖ * ‖μ‖ = (1 / 2 : ℝ) := by
    rw [hc, inv_mul_eq_div]
    apply (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hn.ne')).2
    ring
  have hsubunit : ‖c‖ * ‖μ‖ < 1 := by rw [hcnorm]; norm_num
  let ν : BeltramiGamma Γ := GammaMeasurableBeltrami.sourceGammaOfScalar μ c hsubunit
  have hB := GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff_univ μ.val
  have hν : IsBeltramiCoeff ν.val.val univ (1 / 2 : ℝ) := by
    change IsBeltramiCoeff (fun w => c * κ w) univ (1 / 2 : ℝ)
    refine ⟨hB.1.const_mul c, ?_⟩
    filter_upwards [hB.2] with w hw
    rw [norm_mul]
    calc
      ‖c‖ * ‖κ w‖ ≤ ‖c‖ * ‖μ‖ := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
      _ = (1 / 2 : ℝ) := hcnorm
  have ht : ‖t‖ < (1 / 2 : ℝ) := by rw [htnorm]; linarith
  have hTaylor := bersFunction_scalar_weighted_remainder ν hν hz ht
  have htc : t * c = 1 := mul_inv_cancel₀ ht0
  have heq : (fun w => t * ν.val.val w) = κ := by
    funext w
    change t * (c * κ w) = κ w
    rw [← mul_assoc, htc, one_mul]
  have hlinear : bersDerivative ν.val.val z = c * bersDerivative κ z := by
    unfold bersDerivative
    have hf : (fun w => ν.val.val w / (w - z) ^ 4) =
        fun w => c * (κ w / (w - z) ^ 4) := by
      funext w
      change (c * κ w) / (w - z) ^ 4 = c * (κ w / (w - z) ^ 4)
      ring
    rw [hf, integral_const_mul]
    ring
  have hderiv : t * bersDerivative ν.val.val z = bersDerivative κ z := by
    rw [hlinear, ← mul_assoc, htc, one_mul]
  rw [heq, hderiv] at hTaylor
  calc
    ‖bersFunction κ z - bersDerivative κ z‖ * z.im ^ 2 ≤ 12 * ‖t‖ ^ 2 := hTaylor
    _ = 48 * ‖μ‖ ^ 2 := by rw [htnorm]; ring

/-- A zero actual class gives both a zero Bers function and a zero integral
variation. The representative is used only almost everywhere, as required. -/
theorem bersFunction_and_derivative_zero_of_norm_zero
    (μ : GammaMeasurableBeltrami.Space Γ) (hn : ‖μ‖ = 0)
    {z : ℂ} (hz : z ∈ lowerHalf) :
    bersFunction (GammaMeasurableBeltrami.planeRepresentative μ.val) z = 0 ∧
      bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val) z = 0 := by
  let κ : ℂ → ℂ := GammaMeasurableBeltrami.planeRepresentative μ.val
  have hzero : κ =ᵐ[volume.restrict upperHalf] (0 : ℂ → ℂ) := by
    filter_upwards [(GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val).2]
      with w hw
    change ‖κ w‖ ≤ ‖μ‖ at hw
    rw [hn] at hw
    exact norm_eq_zero.mp (le_antisymm hw (norm_nonneg _))
  have hunit : ‖μ‖ < 1 := by rw [hn]; norm_num
  let μball : GammaMeasurableBeltrami.Ball Γ :=
    ⟨μ, by simpa only [mem_ball, dist_zero_right] using hunit⟩
  let μsource : BeltramiGamma Γ := GammaMeasurableBeltrami.toSourceGamma μball
  let νsource : BeltramiGamma Γ :=
    GammaMeasurableBeltrami.sourceGammaOfScalar μ 0 (by simp)
  have heq : μsource.val.val =ᵐ[volume.restrict upperHalf] νsource.val.val := by
    filter_upwards [hzero] with w hw
    change κ w = (0 : ℂ) * κ w
    simpa only [zero_mul, Pi.zero_apply] using hw
  have hbers : bersFunction κ = bersFunction (0 : ℂ → ℂ) := by
    have h := GammaMeasurableBeltrami.sourceBers_congr_ae μsource νsource heq
    change bersFunction κ = bersFunction (fun w => (0 : ℂ) * κ w) at h
    have hfzero : (fun w => (0 : ℂ) * κ w) = (0 : ℂ → ℂ) := by
      funext w
      change (0 : ℂ) * κ w = 0
      exact zero_mul _
    rw [hfzero] at h
    exact h
  constructor
  · change bersFunction κ z = 0
    rw [hbers]
    simp only [bersFunction, indicator_of_mem hz, bB_l_normalizedSolution_zero,
      bB_l_schwarzian_id]
  · change bersDerivative κ z = 0
    unfold bersDerivative
    have hi : (∫ w in upperHalf, κ w / (w - z) ^ 4) = 0 := by
      calc
        (∫ w in upperHalf, κ w / (w - z) ^ 4) =
            ∫ w in upperHalf, (0 : ℂ → ℂ) w := by
          apply integral_congr_ae
          filter_upwards [hzero] with w hw
          rw [hw, Pi.zero_apply, zero_div]
        _ = 0 := by
          simpa only [Pi.zero_apply] using
            (integral_zero ℂ ℂ (μ := volume.restrict upperHalf))
    rw [hi, mul_zero]

/-- The actual Bers function has a uniform weighted quadratic remainder on
the full native coefficient ball of radius one quarter, including zero. -/
theorem bersFunction_weighted_quadratic_remainder
    (μ : GammaMeasurableBeltrami.Space Γ) (hsmall : ‖μ‖ < 1 / 4)
    {z : ℂ} (hz : z ∈ lowerHalf) :
    ‖bersFunction (GammaMeasurableBeltrami.planeRepresentative μ.val) z -
        bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val) z‖ *
      z.im ^ 2 ≤ 48 * ‖μ‖ ^ 2 := by
  by_cases hμ : μ = 0
  · obtain ⟨hB, hD⟩ := bersFunction_and_derivative_zero_of_norm_zero μ
      (norm_eq_zero.mpr hμ) hz
    rw [hB, hD, sub_self, norm_zero, zero_mul]
    positivity
  · exact bersFunction_weighted_remainder_of_ne_zero μ hμ hsmall hz

end LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergman
