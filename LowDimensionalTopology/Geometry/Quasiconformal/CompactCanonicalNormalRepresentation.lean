module

public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiQuasiconformal
public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiEstimates

/-!
# The actual compact-cutoff canonical map at a prescribed exponent

The compact support belongs to the cutoff coefficient. The original exponent
and the original Hilbert-transform norm are retained. The canonical plane map
is identified with the affine normalization of its same-exponent normal
solution; its actual classical Wirtinger derivative has that normalization.
The potential estimate supplies control of the normalizing value at one.

The fixed-point, potential and normalized-uniqueness APIs are from Wu Xiaobin's
LiZhongQC development, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology Metric
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

private theorem normalPotential_distributional {p : ℝ} (hp : 2 < p)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p) (volume : Measure ℂ)) :
    HasDistributionalWirtingerDerivatives (fun z => z + normalizedCauchyPotential ω z)
      (fun z => 1 + hilbertH ω z) ω univ := by
  have hid : HasDistributionalWirtingerDerivatives (fun z : ℂ => z)
      (fun _ => 1) (fun _ => 0) univ := by
    have h := c1_hasDistributionalWirtingerDerivatives_univ
      (f := fun z : ℂ => z) contDiff_id
    apply h.congr_derivatives_univ
    · filter_upwards with z
      rw [dz_eq_deriv (hasDerivAt_id' z).differentiableAt]
      exact (hasDerivAt_id' z).deriv
    · exact Eventually.of_forall fun z =>
        (cauchyRiemann_iff.mp (hasDerivAt_id' z).differentiableAt).2
  have h := hid.add_univ (normalizedCauchyPotential_distributional hp hω)
  apply h.congr_derivatives_univ
  · exact EventuallyEq.rfl
  · exact Eventually.of_forall fun z => zero_add (ω z)

/-- Every compact cutoff has an actual same-p normal representation, the sharp
fixed-point denominator bound, and the actual canonical derivative formula.
The constant Kp is chosen before any coefficient or its normal solution. -/
theorem canonicalCompact_normalRepresentation {p : ℝ} (hp : 2 < p) :
    ∃ Kp : ℝ, 0 ≤ Kp ∧ ∀ μ : MeasurableBeltramiBall,
      (∀ᵐ z ∂(volume : Measure ℂ), z ∉ ball 0 4 → μ.val z = 0) →
      ‖μ.val‖ * smoothHilbertNorm p < 1 →
      ∃ (ω : ℂ → ℂ) (a : ℂ),
        MemLp ω (ENNReal.ofReal p) (volume : Measure ℂ) ∧
        (eLpNorm ω (ENNReal.ofReal p) volume).toReal ≤
          (eLpNorm (μ.val : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal /
            (1 - ‖μ.val‖ * smoothHilbertNorm p) ∧
        a ≠ 0 ∧
        ‖a - 1‖ ≤ Kp * (eLpNorm ω (ENNReal.ofReal p) volume).toReal ∧
        (∀ z : ℂ, MeasurableBeltramiBall.normalizedSolution μ z =
          (z + normalizedCauchyPotential ω z) / a) ∧
        dz (MeasurableBeltramiBall.normalizedSolution μ) =ᵐ[volume]
          (fun z => (1 + hilbertH ω z) / a) := by
  obtain ⟨Kp, hKp, hholder⟩ := normalizedCauchyPotential_holder_bound hp
  refine ⟨Kp, hKp, ?_⟩
  intro μ hsupp hsmall
  let k := ‖μ.val‖
  have hk0 : 0 ≤ k := norm_nonneg _
  have hk1 : k < 1 := MeasurableBeltramiBall.norm_lt_one μ
  have hp1 : 1 < p := lt_trans one_lt_two hp
  have hsmall' : k * hilbertNorm p < 1 := by
    simpa only [smoothHilbertNorm_eq_hilbertNorm hp1] using hsmall
  let ν : ℂ → ℂ := (ball (0 : ℂ) 4).indicator (μ.val : ℂ → ℂ)
  have hνae : ν =ᵐ[volume] (μ.val : ℂ → ℂ) := by
    filter_upwards [hsupp] with z hz
    by_cases hzin : z ∈ ball (0 : ℂ) 4
    · exact indicator_of_mem hzin _
    · change (ball (0 : ℂ) 4).indicator (μ.val : ℂ → ℂ) z = μ.val z
      rw [indicator_of_notMem hzin, hz hzin]
  have hμ : IsBeltramiCoeff (μ.val : ℂ → ℂ) univ k :=
    MeasurableBeltramiSpace.isBeltramiCoeff μ.val
  have hν : IsBeltramiCoeff ν univ k :=
    (planar_isBeltramiCoeff_congr_ae hνae).mpr hμ
  have hνsupp : ∀ z : ℂ, 4 < ‖z‖ → ν z = 0 := by
    intro z hz
    exact indicator_of_notMem (by simpa only [mem_ball_zero_iff] using (not_lt_of_ge hz.le)) _
  have hcomp : HasCompactEssentialSupport (μ.val : ℂ → ℂ) := by
    refine ⟨closedBall 0 4, isCompact_closedBall _ _, ?_⟩
    filter_upwards [hsupp] with z hz
    intro hzc
    exact hz (fun hzb => hzc (ball_subset_closedBall hzb))
  have hμLp := measurableBeltrami_memLp_of_compactEssentialSupport μ.val hcomp
    (ENNReal.ofReal p)
  have hνLp : MemLp ν (ENNReal.ofReal p) (volume : Measure ℂ) :=
    MemLp.ae_eq hνae.symm hμLp
  obtain ⟨ω, hω, hfixed, _⟩ := eq12_1_solution hk0 hν hp hsmall' hνLp
  let F : ℂ → ℂ := fun z => z + normalizedCauchyPotential ω z
  have hFnormal : IsNormalLpSolution (μ.val : ℂ → ℂ) F p :=
    (isNormalLpSolution_congr_coefficient_ae hνae).mp
      (normalLpSolution_of_fixedPoint hp hω hfixed)
  have hFqc := (normalLpSolution_quasiconformal μ.val ⟨hk0, hk1⟩ le_rfl
    hcomp hp hsmall hFnormal).1
  have hw : HasDistributionalWirtingerDerivatives F
      (fun z => 1 + hilbertH ω z) ω univ := normalPotential_distributional hp hω
  have hactual : ∀ᵐ z ∂(volume : Measure ℂ), dz F z = 1 + hilbertH ω z := by
    have h := homeomorph_wirtinger_eq_distributional_ae isOpen_univ hFqc.2.2.1 hw
    simpa only [Measure.restrict_univ] using h.mono (fun _ hz => hz.1)
  have hdiff : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ F z := by
    simpa only [Measure.restrict_univ] using thm9_3_differentiable_ae hFqc
  have hG := MeasurableBeltramiBall.normalizedSolution_isNormalized_of_ae μ hνae.symm
  obtain ⟨ha, hrepr⟩ := ahC_normalized_eq hk0 hk1 hν hνsupp hp hsmall' hω hfixed hG
  let a : ℂ := 1 + cauchyT ω 1 - cauchyT ω 0
  have hP := normalizedCauchyPotential_eq_cauchyT_sub_of_fixedPoint hp hω hνsupp hfixed
  have haF : a = F 1 := by
    dsimp only [a, F]
    rw [hP]
    dsimp only
    ring
  have hrepr' : ∀ z : ℂ, MeasurableBeltramiBall.normalizedSolution μ z = F z / a := by
    intro z
    rw [hrepr z]
    apply congrArg (fun b : ℂ => b / a)
    dsimp only [F]
    rw [hP]
    dsimp only
    ring
  have hωbound : (eLpNorm ω (ENNReal.ofReal p) volume).toReal ≤
      (eLpNorm (μ.val : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal /
        (1 - k * smoothHilbertNorm p) := by
    obtain ⟨hb, htri⟩ := ahC_omega_bounds hk0 hν hp1 hνLp hω hfixed
    rw [smoothHilbertNorm_eq_hilbertNorm hp1]
    rw [eLpNorm_congr_ae hνae] at htri
    apply (le_div_iff₀ (sub_pos.mpr hsmall')).mpr
    nlinarith
  have hanorm : ‖a - 1‖ ≤ Kp * (eLpNorm ω (ENNReal.ofReal p) volume).toReal := by
    have h := hholder ω hω 1 0
    simpa only [haF, F, add_sub_cancel_left, normalizedCauchyPotential_zero,
      sub_zero, norm_one, Real.one_rpow, mul_one] using h
  refine ⟨ω, a, hω, hωbound, ha, hanorm, hrepr', ?_⟩
  have hfun : (MeasurableBeltramiBall.normalizedSolution μ : ℂ → ℂ) =
      (fun u : ℂ => u / a) ∘ F := funext hrepr'
  filter_upwards [hdiff, hactual] with z hdz hz
  have hdA : HasDerivAt (fun u : ℂ => u / a) (1 / a) (F z) :=
    (hasDerivAt_id' (F z)).div_const a
  rw [hfun, eq6_2_dz_comp hdz (hdA.differentiableAt.restrictScalars ℝ),
    dz_eq_deriv hdA.differentiableAt, hdA.deriv,
    (cauchyRiemann_iff.mp hdA.differentiableAt).2, zero_mul, add_zero, hz]
  ring

end LowDimensionalTopology.Geometry.Quasiconformal
