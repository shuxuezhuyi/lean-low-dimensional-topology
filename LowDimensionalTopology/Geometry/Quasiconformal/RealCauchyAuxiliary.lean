module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealCauchyDecay
public import LowDimensionalTopology.Geometry.Quasiconformal.RieszAuxiliaryWComposition
public import LowDimensionalTopology.Geometry.Quasiconformal.RieszHorizontalGreen
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The Cauchy auxiliary function and its horizontal integral

The original continuous compactly supported real test determines the
Cauchy function and the Riesz auxiliary value. Their regularity,
nonnegative Laplacian and square decay supply the horizontal Green
identity and prove the nonnegativity of the horizontal integral.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The literal W of the original upper-half-plane Cauchy integral. -/
def realCauchyAuxiliary (φ : ℝ → ℝ) (p : ℝ) (z : ℂ) : ℝ :=
  rieszAuxiliaryValue p (realCauchyFunction φ z)

private theorem analyticAt_realCauchy_auxiliary_input {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (realCauchyFunction φ) z :=
  (differentiableOn_realCauchyFunction hφ hc).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_im) z hz

/-- The actual W is C2 at every point of the original upper half-plane. -/
theorem contDiffAt_realCauchyAuxiliary {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {p : ℝ} (hp : 2 ≤ p)
    {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ 2 (realCauchyAuxiliary φ p) z := by
  have ha : AnalyticAt ℝ (realCauchyFunction φ) z :=
    (analyticAt_realCauchy_auxiliary_input hφ hc hz).restrictScalars
  have hfun : realCauchyAuxiliary φ p =
      (fun w : ℂ => rieszAuxiliaryValue p (realCauchyFunction φ w)) := rfl
  rw [hfun]
  exact (contDiff_two_rieszAuxiliaryValue hp).contDiffAt.comp z
    (ha.contDiffAt (n := 2))

/-- The exact real Laplacian computed in the book, for its actual F. -/
theorem laplacian_realCauchyAuxiliary_eq {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {p : ℝ} (hp : 2 ≤ p)
    {z : ℂ} (hz : 0 < z.im) :
    Laplacian.laplacian (realCauchyAuxiliary φ p) z =
      ‖deriv (realCauchyFunction φ) z‖ ^ 2 *
        (p ^ 2 * (‖realCauchyFunction φ z‖ ^ (p - 2) -
          ‖(realCauchyFunction φ z).re‖ ^ (p - 2))) := by
  change Laplacian.laplacian (fun w => rieszAuxiliaryValue p (realCauchyFunction φ w)) z = _
  rw [laplacian_rieszAuxiliaryValue_comp hp
    (analyticAt_realCauchy_auxiliary_input hφ hc hz), laplacian_rieszAuxiliaryValue_eq hp]

/-- No subharmonicity premise is added to the original compact test. -/
theorem laplacian_realCauchyAuxiliary_nonneg {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {p : ℝ} (hp : 2 ≤ p)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ Laplacian.laplacian (realCauchyAuxiliary φ p) z := by
  change 0 ≤ Laplacian.laplacian (fun w => rieszAuxiliaryValue p (realCauchyFunction φ w)) z
  rw [laplacian_rieszAuxiliaryValue_comp hp
    (analyticAt_realCauchy_auxiliary_input hφ hc hz)]
  exact mul_nonneg (sq_nonneg _) (laplacian_rieszAuxiliaryValue_nonneg hp _)

private theorem norm_rieszAuxiliaryValue_le {p : ℝ} (hp : 2 ≤ p) (z : ℂ) :
    ‖rieszAuxiliaryValue p z‖ ≤ (1 + p / (p - 1)) * ‖z‖ ^ p := by
  have hc : 0 ≤ p / (p - 1) := div_nonneg (by linarith) (by linarith)
  have hr : ‖z.re‖ ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm z
  have hpow : ‖z.re‖ ^ p ≤ ‖z‖ ^ p :=
    Real.rpow_le_rpow (norm_nonneg _) hr (by linarith)
  have hnorm : ‖‖z‖ ^ p‖ = ‖z‖ ^ p :=
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
  have hnormRe : ‖p / (p - 1) * ‖z.re‖ ^ p‖ = p / (p - 1) * ‖z.re‖ ^ p :=
    Real.norm_of_nonneg (mul_nonneg hc (Real.rpow_nonneg (norm_nonneg _) _))
  calc
    _ ≤ ‖‖z‖ ^ p‖ + ‖p / (p - 1) * ‖z.re‖ ^ p‖ := norm_sub_le _ _
    _ = ‖z‖ ^ p + p / (p - 1) * ‖z.re‖ ^ p := by rw [hnorm, hnormRe]
    _ ≤ ‖z‖ ^ p + p / (p - 1) * ‖z‖ ^ p := by gcongr
    _ = _ := by ring

private theorem norm_fderiv_rieszAuxiliaryValue_le {p : ℝ} (hp : 2 ≤ p) (z : ℂ) :
    ‖fderiv ℝ (rieszAuxiliaryValue p) z‖ ≤
      p * (1 + p / (p - 1)) * ‖z‖ ^ (p - 1) := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hc : 0 ≤ p / (p - 1) := div_nonneg hp0 (by linarith)
  have hpMinus : 0 ≤ p - 1 := by linarith
  let f : ℂ → ℝ := fun w => ‖w‖ ^ p
  let g : ℂ → ℝ := fun w => ‖w.re‖ ^ p
  have hf : Differentiable ℝ f := differentiable_norm_rpow hp1
  have hg : Differentiable ℝ g :=
    (differentiable_norm_rpow (E := ℝ) hp1).comp Complex.reCLM.differentiable
  have hre : ‖Complex.reCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    simpa only [Complex.reCLM_apply, one_mul, Real.norm_eq_abs] using
      Complex.abs_re_le_norm w
  have hr : ‖z.re‖ ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm z
  have hgnorm : ‖fderiv ℝ g z‖ ≤ p * ‖z‖ ^ (p - 1) := by
    have h := norm_fderiv_norm_rpow_le Complex.reCLM.differentiable (x := z) hp1
    rw [ContinuousLinearMap.fderiv] at h
    have hbase : ‖fderiv ℝ g z‖ ≤ p * ‖z.re‖ ^ (p - 1) * ‖Complex.reCLM‖ := by
      simpa only [g, Complex.reCLM_apply] using h
    calc
      _ ≤ p * ‖z.re‖ ^ (p - 1) * ‖Complex.reCLM‖ := hbase
      _ ≤ p * ‖z‖ ^ (p - 1) * 1 := by gcongr
      _ = _ := mul_one _
  have hD : HasFDerivAt (rieszAuxiliaryValue p)
      (fderiv ℝ f z - (p / (p - 1)) • fderiv ℝ g z) z := by
    simpa only [f, g, rieszAuxiliaryValue, smul_eq_mul] using!
      (hf z).hasFDerivAt.sub ((hg z).hasFDerivAt.const_smul (p / (p - 1)))
  have hfnorm : ‖fderiv ℝ f z‖ = p * ‖z‖ ^ (p - 1) :=
    norm_fderiv_norm_id_rpow z hp1
  rw [hD.fderiv]
  calc
    _ ≤ ‖fderiv ℝ f z‖ + ‖(p / (p - 1)) • fderiv ℝ g z‖ := norm_sub_le _ _
    _ = p * ‖z‖ ^ (p - 1) + (p / (p - 1)) * ‖fderiv ℝ g z‖ := by
      rw [hfnorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ p * ‖z‖ ^ (p - 1) + (p / (p - 1)) * (p * ‖z‖ ^ (p - 1)) := by gcongr
    _ = _ := by ring

/-- The actual W and its actual real differential have the common square
profile needed for the horizontal Green argument, on every Im z>=delta>0.
There is no supplied decay hypothesis on the original compact test. -/
theorem exists_realCauchyAuxiliary_decay_profile {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {p : ℝ} (hp : 2 ≤ p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, δ ≤ z.im →
      ‖realCauchyAuxiliary φ p z‖ ≤ C / (1 + ‖z‖) ^ 2 ∧
        ‖fderiv ℝ (realCauchyAuxiliary φ p) z‖ ≤ C / (1 + ‖z‖) ^ 2 := by
  obtain ⟨M, hM, hMb⟩ := exists_realCauchy_decay_profile hφ hc hδ
  let c : ℝ := p / (p - 1)
  let Cv : ℝ := (1 + c) * M ^ (p - 2) * M ^ 2
  let Cg : ℝ := p * (1 + c) * M ^ (p - 1) * M
  let C : ℝ := Cv + Cg
  have hp0 : 0 ≤ p := by linarith
  have hp2 : 0 ≤ p - 2 := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hc0 : 0 ≤ c := div_nonneg hp0 (by linarith)
  have hCv : 0 ≤ Cv := by dsimp [Cv]; positivity
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hC : 0 ≤ C := add_nonneg hCv hCg
  refine ⟨C, hC, fun z hz => ?_⟩
  have hz0 : 0 < z.im := hδ.trans_le hz
  have hq : 0 < 1 + ‖z‖ := by positivity
  have hF := (hMb z hz).1
  have hdF := (hMb z hz).2
  have hFM : ‖realCauchyFunction φ z‖ ≤ M := hF.trans (by
    apply (div_le_iff₀ hq).2
    nlinarith [norm_nonneg z])
  have hpow : ‖realCauchyFunction φ z‖ ^ p ≤ M ^ (p - 2) * (M / (1 + ‖z‖)) ^ 2 := by
    calc
      _ = ‖realCauchyFunction φ z‖ ^ (p - 2) * ‖realCauchyFunction φ z‖ ^ 2 := by
        rw [← Real.rpow_two, ← Real.rpow_add_of_nonneg (norm_nonneg _) hp2 (by norm_num)]
        congr 1
        ring
      _ ≤ _ := mul_le_mul
        (Real.rpow_le_rpow (norm_nonneg _) hFM hp2)
        (pow_le_pow_left₀ (norm_nonneg _) hF 2)
        (sq_nonneg _) (Real.rpow_nonneg hM _)
  have hvalue : ‖realCauchyAuxiliary φ p z‖ ≤ Cv / (1 + ‖z‖) ^ 2 := by
    calc
      _ ≤ (1 + c) * ‖realCauchyFunction φ z‖ ^ p := norm_rieszAuxiliaryValue_le hp _
      _ ≤ (1 + c) * (M ^ (p - 2) * (M / (1 + ‖z‖)) ^ 2) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by
        dsimp only [Cv]
        rw [div_pow]
        ring
  have hFreal : HasFDerivAt (realCauchyFunction φ)
      ((deriv (realCauchyFunction φ) z) • (1 : ℂ →L[ℝ] ℂ)) z :=
    (analyticAt_realCauchy_auxiliary_input hφ hc hz0).differentiableAt.hasDerivAt.complexToReal_fderiv
  have hmult : ‖(deriv (realCauchyFunction φ) z) • (1 : ℂ →L[ℝ] ℂ)‖ ≤
      ‖deriv (realCauchyFunction φ) z‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    simp only [smul_apply, one_apply_eq_self, smul_eq_mul, norm_mul]
    exact le_rfl
  have hchain : HasFDerivAt (realCauchyAuxiliary φ p)
      ((fderiv ℝ (rieszAuxiliaryValue p) (realCauchyFunction φ z)).comp
        ((deriv (realCauchyFunction φ) z) • (1 : ℂ →L[ℝ] ℂ))) z :=
    (((contDiff_two_rieszAuxiliaryValue hp).differentiable two_ne_zero
      (realCauchyFunction φ z)).hasFDerivAt).comp z hFreal
  have hgradient : ‖fderiv ℝ (realCauchyAuxiliary φ p) z‖ ≤ Cg / (1 + ‖z‖) ^ 2 := by
    rw [hchain.fderiv]
    calc
      _ ≤ ‖fderiv ℝ (rieszAuxiliaryValue p) (realCauchyFunction φ z)‖ *
          ‖(deriv (realCauchyFunction φ) z) • (1 : ℂ →L[ℝ] ℂ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (p * (1 + c) * ‖realCauchyFunction φ z‖ ^ (p - 1)) *
          ‖deriv (realCauchyFunction φ) z‖ :=
        mul_le_mul (norm_fderiv_rieszAuxiliaryValue_le hp _) hmult
          (norm_nonneg _) (by positivity)
      _ ≤ (p * (1 + c) * M ^ (p - 1)) * (M / (1 + ‖z‖) ^ 2) := by gcongr
      _ = _ := by simp only [Cg, div_eq_mul_inv]; ring
  exact ⟨hvalue.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right hCg) (sq_nonneg _)),
    hgradient.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_left hCv) (sq_nonneg _))⟩

/-- The actual horizontal inequality in the book's Green argument, derived
from the original compact test. All calculus premises have been supplied;
there is no Green, slice-bound or Hilbert-estimate premise. -/
theorem integral_realCauchyAuxiliary_nonneg {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {p : ℝ} (hp : 2 ≤ p)
    {η : ℝ} (hη : 0 < η) :
    0 ≤ ∫ x : ℝ, realCauchyAuxiliary φ p ((x : ℂ) + (η : ℂ) * I) := by
  exact riesz_horizontal_integral_nonneg_of_laplacian_and_decay
    (fun z hz => contDiffAt_realCauchyAuxiliary hφ hc hp hz)
    (fun z hz => laplacian_realCauchyAuxiliary_nonneg hφ hc hp hz)
    (fun δ hδ => exists_realCauchyAuxiliary_decay_profile hφ hc hp hδ) hη

end LowDimensionalTopology.Geometry.Quasiconformal
