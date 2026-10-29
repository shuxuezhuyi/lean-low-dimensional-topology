/-
The quasiconformal area formula and normal-solution estimates used below are
due to Wu Xiaobin, Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2. Their Apache-2.0 attribution is
retained in the external source and THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiInverse
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Tactic.FieldSimp

/-!
# The Lp bound for the coefficient of an actual inverse

Nonnegative weighted area is used before taking real values of the norms.
Hölder's inequality preserves the original exponent and both coefficient
factors, including zero coefficients.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

private theorem lintegral_enorm_rpow_eq_lp {v : ℂ → ℂ} {p : ℝ} (hp : 0 < p)
    (hv : AEStronglyMeasurable v (volume : Measure ℂ)) :
    (∫⁻ z, ‖v z‖ₑ ^ p) = eLpNorm v (ENNReal.ofReal p) volume ^ p := by
  rw [eLpNorm_eq_eLpNorm' (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
    ENNReal.ofReal_ne_top hv, ENNReal.toReal_ofReal (le_of_lt hp)]
  exact lintegral_rpow_enorm_eq_rpow_eLpNorm' hp

/-- The inverse coefficient's exact interpolation bound follows from its
actual coefficient composition law and the actual Beltrami equation. The
conclusion includes Lp membership, proved by nonnegative integration. -/
theorem inverse_coefficient_lp_interpolation
    (e : ℂ ≃ₜ ℂ) {K p : ℝ} (he : IsKQC e univ K) (hp : 2 < p)
    {μ : ℂ → ℂ} (hμLp : MemLp μ (ENNReal.ofReal p) (volume : Measure ℂ))
    (hbarLp : MemLp (dzbar e) (ENNReal.ofReal p) (volume : Measure ℂ))
    (hbar : ∀ᵐ z ∂(volume : Measure ℂ), dzbar e z = μ z * dz e z)
    (hinv : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖complexDilatation e.symm (e z)‖ ≤ ‖μ z‖) :
    MemLp (complexDilatation e.symm) (ENNReal.ofReal p) (volume : Measure ℂ) ∧
      (eLpNorm (complexDilatation e.symm) (ENNReal.ofReal p) volume).toReal ≤
        (eLpNorm μ (ENNReal.ofReal p) volume).toReal ^ (1 - 2 / p) *
          (eLpNorm (dzbar e) (ENNReal.ofReal p) volume).toReal ^ (2 / p) := by
  have hp0 : 0 < p := lt_trans zero_lt_two hp
  let a : ℝ := 1 - 2 / p
  let b : ℝ := 2 / p
  have ha : 0 < a := by
    dsimp only [a]
    exact sub_pos.mpr ((div_lt_one hp0).mpr hp)
  have hb : 0 < b := div_pos zero_lt_two hp0
  have hab : a + b = 1 := by dsimp only [a, b]; ring
  have hpa : p * a = p - 2 := by dsimp only [a]; field_simp [hp0.ne']
  have hpb : p * b = 2 := by dsimp only [b]; field_simp [hp0.ne']
  have hνm : Measurable (complexDilatation e.symm) :=
    (measurable_dzbar e.symm).div (measurable_dz e.symm)
  have harea := quasiconformal_homeomorph_lintegral e he (hνm.enorm.pow_const p)
  have hpoint : ∀ᵐ z ∂(volume : Measure ℂ),
      ENNReal.ofReal (jacobian e z) * ‖complexDilatation e.symm (e z)‖ₑ ^ p ≤
        (‖μ z‖ₑ ^ p) ^ a * (‖dzbar e z‖ₑ ^ p) ^ b := by
    filter_upwards [hbar, hinv] with z hzbar hzinv
    have hJ : ENNReal.ofReal (jacobian e z) ≤ ‖dz e z‖ₑ ^ (2 : ℝ) := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        Real.rpow_two]
      apply ENNReal.ofReal_le_ofReal
      dsimp only [jacobian]
      nlinarith [sq_nonneg ‖dzbar e z‖]
    have hnorm : ‖complexDilatation e.symm (e z)‖ₑ ≤ ‖μ z‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hzinv
    have hid : (‖μ z‖ₑ ^ p) ^ a * (‖dzbar e z‖ₑ ^ p) ^ b =
        ‖dz e z‖ₑ ^ (2 : ℝ) * ‖μ z‖ₑ ^ p := by
      rw [← ENNReal.rpow_mul, hpa, ← ENNReal.rpow_mul, hpb,
        hzbar, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [← mul_assoc,
        ← ENNReal.rpow_add_of_nonneg (p - 2) 2 (sub_nonneg.mpr hp.le) (by norm_num),
        sub_add_cancel]
      exact mul_comm _ _
    exact (mul_le_mul' hJ (ENNReal.rpow_le_rpow hnorm hp0.le)).trans_eq hid.symm
  have hholder := ENNReal.lintegral_mul_norm_pow_le
    (hμLp.aestronglyMeasurable.enorm.pow_const p)
    (hbarLp.aestronglyMeasurable.enorm.pow_const p) ha.le hb.le hab
  have hpower :
      eLpNorm (complexDilatation e.symm) (ENNReal.ofReal p) volume ^ p ≤
        (eLpNorm μ (ENNReal.ofReal p) volume ^ p) ^ a *
          (eLpNorm (dzbar e) (ENNReal.ofReal p) volume ^ p) ^ b := by
    rw [← lintegral_enorm_rpow_eq_lp hp0 hνm.aestronglyMeasurable,
      ← lintegral_enorm_rpow_eq_lp hp0 hμLp.aestronglyMeasurable,
      ← lintegral_enorm_rpow_eq_lp hp0 hbarLp.aestronglyMeasurable]
    exact harea.trans_le ((lintegral_mono_ae hpoint).trans hholder)
  have hnorm :
      eLpNorm (complexDilatation e.symm) (ENNReal.ofReal p) volume ≤
        eLpNorm μ (ENNReal.ofReal p) volume ^ a *
          eLpNorm (dzbar e) (ENNReal.ofReal p) volume ^ b := by
    apply (ENNReal.rpow_le_rpow_iff hp0).mp
    refine hpower.trans_eq ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    rw [mul_comm p a, mul_comm p b]
  have hfinite :
      eLpNorm μ (ENNReal.ofReal p) volume ^ a *
        eLpNorm (dzbar e) (ENNReal.ofReal p) volume ^ b ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg ha.le hμLp.eLpNorm_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg hb.le hbarLp.eLpNorm_ne_top)
  refine ⟨lt_of_le_of_lt hnorm (lt_top_iff_ne_top.mpr hfinite), ?_⟩
  have hreal := ENNReal.toReal_mono hfinite hnorm
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, a, b] using hreal

/-- A single constant depending only on the original p gives the quantitative
lower separation for every original normal solution. The denominator and
coefficient norm are unchanged when the same actual inverse is used. -/
theorem exists_normalLpSolution_lower_separation_constant {p : ℝ} (hp : 2 < p) :
    ∃ Kp : ℝ, 0 ≤ Kp ∧
      ∀ (μ : MeasurableBeltramiSpace) (k : ℝ) (f : ℂ → ℂ), k ∈ Ico (0 : ℝ) 1 →
        ‖μ‖ ≤ k → HasCompactEssentialSupport (μ : ℂ → ℂ) →
        k * smoothHilbertNorm p < 1 → IsNormalLpSolution (μ : ℂ → ℂ) f p →
        ∀ z₁ z₂ : ℂ, ‖z₁ - z₂‖ ≤
          Kp / (1 - k * smoothHilbertNorm p) ^ (1 + 2 / p) *
            (eLpNorm (μ : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal *
              ‖f z₁ - f z₂‖ ^ (1 - 2 / p) + ‖f z₁ - f z₂‖ := by
  obtain ⟨Kp, hKp, -, hupper⟩ := exists_normalLpSolution_estimate_constant hp
  refine ⟨Kp, hKp, ?_⟩
  intro μ k f hk hμk hcomp hsmall hf
  obtain ⟨e, he, hνCoeff, hνcomp, hνNormal⟩ :=
    normalLpSolution_inverse μ hk hμk hcomp hp hsmall hf
  obtain ⟨hQC, -, hcoeff⟩ :=
    normalLpSolution_quasiconformal μ hk hμk hcomp hp hsmall hf
  have hqe : IsKQC e univ ((1 + k) / (1 - k)) := by simpa only [he] using hQC
  have hcoeq : complexDilatation e =ᵐ[volume] (μ : ℂ → ℂ) := by
    simpa only [he] using hcoeff
  have hμbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k := by
    filter_upwards [lpInfinity_norm_ae_le μ] with z hz
    exact hz.trans hμk
  have hμCoeff : IsBeltramiCoeff (μ : ℂ → ℂ) univ k := by
    refine ⟨(MeasurableBeltramiSpace.isBeltramiCoeff μ).1, ?_⟩
    simpa only [Measure.restrict_univ] using hμbound
  have hμLp := measurableBeltrami_memLp_of_compactEssentialSupport μ hcomp (ENNReal.ofReal p)
  have hdata := hf
  obtain ⟨_, _, g, h, hw, _, hbeltrami⟩ := hdata
  have hwe : HasDistributionalWirtingerDerivatives e g h univ := by
    simpa only [he] using hw
  have hactual : ∀ᵐ z ∂(volume : Measure ℂ), dz e z = g z ∧ dzbar e z = h z := by
    simpa only [Measure.restrict_univ] using
      homeomorph_wirtinger_eq_distributional_ae isOpen_univ hqe.2.2.1 hwe
  have hbar : ∀ᵐ z ∂(volume : Measure ℂ), dzbar e z = μ z * dz e z := by
    filter_upwards [hactual, hbeltrami] with z hz hμz
    rw [hz.1, hz.2, hμz]
  obtain ⟨hhLp, hhBound⟩ := normalLpSolution_antiholomorphic_lp_bound
    hk.1 hp hμCoeff hμLp hsmall hf hw
  have hbarAE : dzbar e =ᵐ[volume] h := hactual.mono fun _ hz => hz.2
  have hbarLp : MemLp (dzbar e) (ENNReal.ofReal p) (volume : Measure ℂ) :=
    MemLp.ae_eq hbarAE.symm hhLp
  have hbarBound : (eLpNorm (dzbar e) (ENNReal.ofReal p) volume).toReal ≤
      (eLpNorm (μ : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal /
        (1 - k * smoothHilbertNorm p) := by
    rw [eLpNorm_congr_ae hbarAE]
    exact hhBound
  have hinv : Function.invFunOn e univ = e.symm := by
    funext y
    have hy : y ∈ e '' univ := by
      rw [image_univ, e.surjective.range_eq]
      exact mem_univ y
    have h1 : e (Function.invFunOn e univ y) = y := Function.invFunOn_eq hy
    rw [← h1, e.symm_apply_apply, h1]
  have hinvNorm : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖complexDilatation e.symm (e z)‖ ≤ ‖μ z‖ := by
    have hform := eq13_5_7_inverse hqe
    rw [Measure.restrict_univ, hinv] at hform
    filter_upwards [hform, hcoeq] with z hz hμz
    rw [hz.2.2, hμz, norm_mul, norm_neg]
    calc
      _ ≤ ‖μ z‖ * 1 :=
        mul_le_mul_of_nonneg_left (ahT_norm_div_conj_le (dz e z)) (norm_nonneg _)
      _ = _ := mul_one _
  obtain ⟨-, hνInterpolation⟩ :=
    inverse_coefficient_lp_interpolation e hqe hp hμLp hbarLp hbar hinvNorm
  let M : ℝ := (eLpNorm (μ : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal
  let d : ℝ := 1 - k * smoothHilbertNorm p
  let a : ℝ := 1 - 2 / p
  let b : ℝ := 2 / p
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hd : 0 < d := sub_pos.mpr hsmall
  have hp0 : 0 < p := lt_trans zero_lt_two hp
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact sub_nonneg.mpr ((div_le_one hp0).mpr hp.le)
  have hb : 0 ≤ b := (div_pos zero_lt_two hp0).le
  have hab : a + b = 1 := by dsimp only [a, b]; ring
  have hνBound : (eLpNorm (complexDilatation e.symm) (ENNReal.ofReal p) volume).toReal ≤
      M / d ^ b := by
    calc
      _ ≤ M ^ a * (eLpNorm (dzbar e) (ENNReal.ofReal p) volume).toReal ^ b := hνInterpolation
      _ ≤ M ^ a * (M / d) ^ b := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ENNReal.toReal_nonneg hbarBound hb) (Real.rpow_nonneg hM _)
      _ = M / d ^ b := by
        rw [Real.div_rpow hM hd.le, ← mul_div_assoc,
          ← Real.rpow_add_of_nonneg hM ha hb, hab, Real.rpow_one]
  let νLp := MeasurableBeltramiBall.coefficientMemLp hνCoeff
  let ν : MeasurableBeltramiSpace := νLp.toLp (complexDilatation e.symm)
  have hν : (ν : ℂ → ℂ) =ᵐ[volume] complexDilatation e.symm := νLp.coeFn_toLp
  have hνk : ‖ν‖ ≤ k := by
    apply lpInfinity_norm_le_of_ae_bound ν hk.1
    have hνb : ∀ᵐ z ∂(volume : Measure ℂ), ‖complexDilatation e.symm z‖ ≤ k := by
      simpa only [Measure.restrict_univ] using hνCoeff.2
    filter_upwards [hν, hνb] with z hz hbz
    rw [hz]
    exact hbz
  have hνcomp' : HasCompactEssentialSupport (ν : ℂ → ℂ) :=
    (hasCompactEssentialSupport_congr_ae hν).mpr hνcomp
  have hνNormal' : IsNormalLpSolution (ν : ℂ → ℂ) e.symm p :=
    (isNormalLpSolution_congr_coefficient_ae hν).mpr hνNormal
  obtain ⟨_, _, gi, hi, hwi, _, _⟩ := hνNormal
  have hinverseUpper := (hupper ν k e.symm gi hi hk hνk hνcomp' hsmall hνNormal' hwi).2.2
  have hνBound' : (eLpNorm (ν : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ≤ M / d ^ b := by
    rw [eLpNorm_congr_ae hν]
    exact hνBound
  intro z₁ z₂
  have hupperAt := hinverseUpper (e z₁) (e z₂)
  simp only [e.symm_apply_apply] at hupperAt
  have hnonneg : 0 ≤ Kp / d := div_nonneg hKp hd.le
  have hidentity : Kp / d * (M / d ^ b) = Kp / d ^ (1 + b) * M := by
    rw [Real.rpow_add hd 1 b, Real.rpow_one]
    field_simp [hd.ne', (Real.rpow_pos_of_pos hd b).ne']
  calc
    ‖z₁ - z₂‖ ≤ Kp / d * (eLpNorm (ν : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal *
        ‖e z₁ - e z₂‖ ^ a + ‖e z₁ - e z₂‖ := hupperAt
    _ ≤ Kp / d * (M / d ^ b) * ‖e z₁ - e z₂‖ ^ a + ‖e z₁ - e z₂‖ := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
      exact mul_le_mul_of_nonneg_left hνBound' hnonneg
    _ = _ := by rw [hidentity, he]

/-- The quantitative separation bound keeps each literal coefficient
representative and each original normal map. It therefore applies directly
to every member of a smooth approximating sequence without renormalizing
that member or changing its Lp norm. -/
theorem exists_normalLpSolution_lower_separation_constant_for_coefficients
    {p : ℝ} (hp : 2 < p) :
    ∃ Kp : ℝ, 0 ≤ Kp ∧
      ∀ (μ f : ℂ → ℂ) (k : ℝ), k ∈ Ico (0 : ℝ) 1 →
        IsBeltramiCoeff μ univ k → HasCompactEssentialSupport μ →
        k * smoothHilbertNorm p < 1 → IsNormalLpSolution μ f p →
        ∀ z₁ z₂ : ℂ, ‖z₁ - z₂‖ ≤
          Kp / (1 - k * smoothHilbertNorm p) ^ (1 + 2 / p) *
            (eLpNorm μ (ENNReal.ofReal p) volume).toReal *
              ‖f z₁ - f z₂‖ ^ (1 - 2 / p) + ‖f z₁ - f z₂‖ := by
  obtain ⟨Kp, hKp, hsep⟩ := exists_normalLpSolution_lower_separation_constant hp
  refine ⟨Kp, hKp, ?_⟩
  intro μ f k hk hμ hcomp hsmall hf z₁ z₂
  let μLp := MeasurableBeltramiBall.coefficientMemLp hμ
  let γ : MeasurableBeltramiSpace := μLp.toLp μ
  have hγ : (γ : ℂ → ℂ) =ᵐ[volume] μ := μLp.coeFn_toLp
  have hγk : ‖γ‖ ≤ k := by
    apply lpInfinity_norm_le_of_ae_bound γ hk.1
    have hμb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k := by
      simpa only [Measure.restrict_univ] using hμ.2
    filter_upwards [hγ, hμb] with z hz hb
    rw [hz]
    exact hb
  have hγcomp : HasCompactEssentialSupport (γ : ℂ → ℂ) :=
    (hasCompactEssentialSupport_congr_ae hγ).mpr hcomp
  have hγf : IsNormalLpSolution (γ : ℂ → ℂ) f p :=
    (isNormalLpSolution_congr_coefficient_ae hγ).mpr hf
  have hresult := hsep γ k f hk hγk hγcomp hsmall hγf z₁ z₂
  rwa [eLpNorm_congr_ae hγ] at hresult

end LowDimensionalTopology.Geometry.Quasiconformal
