module

public import LowDimensionalTopology.Geometry.Quasiconformal.RieszAuxiliaryW
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The complex chain rule for the Riesz auxiliary function

The Laplacian of `|F|^p-p/(p-1)|Re F|^p` follows from the complex chain
rule for analytic F. The trace of the term containing its second complex
derivative vanishes. The calculation includes zeros of F and p=2.
-/

@[expose] public section
noncomputable section

open Filter Topology Complex InnerProductSpace

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem complex_bilinear_trace (A : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (a : ℂ) :
    A a a + A (a * I) (a * I) = ‖a‖ ^ 2 * (A 1 1 + A I I) := by
  let r : ℝ := a.re
  let s : ℝ := a.im
  have ha : a = r • (1 : ℂ) + s • I := by
    dsimp [r, s]
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im a).symm
  have hai : a * I = (-s) • (1 : ℂ) + r • I := by
    dsimp [r, s]
    apply Complex.ext <;> simp
  have hn : ‖a‖ ^ 2 = r ^ 2 + s ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, r, s]
    ring
  rw [hn, hai, ha]
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  ring

private theorem laplacian_comp_analytic_riesz {G : ℂ → ℝ} (hG : ContDiff ℝ 2 G)
    {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) :
    Laplacian.laplacian (fun w => G (F w)) z =
      ‖deriv F z‖ ^ 2 * Laplacian.laplacian G (F z) := by
  let a : ℂ := deriv F z
  let b : ℂ := deriv (deriv F) z
  let A : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ G) (F z)
  let B : ℂ →L[ℝ] ℝ := fderiv ℝ G (F z)
  have hf : HasFDerivAt F (a • (1 : ℂ →L[ℝ] ℂ)) z :=
    hF.differentiableAt.hasDerivAt.complexToReal_fderiv
  have hdf : HasFDerivAt (deriv F) (b • (1 : ℂ →L[ℝ] ℂ)) z :=
    hF.deriv.differentiableAt.hasDerivAt.complexToReal_fderiv
  have hgrad : HasFDerivAt (fun w => fderiv ℝ G (F w))
      (A.comp (a • (1 : ℂ →L[ℝ] ℂ))) z := by
    exact (((hG.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero).hasFDerivAt).comp z hf
  have hfield := hdf.smul_const (1 : ℂ →L[ℝ] ℂ)
  have hchain := hgrad.clm_comp hfield
  have hlocal : fderiv ℝ (fun w => G (F w)) =ᶠ[𝓝 z]
      (fun w => (fderiv ℝ G (F w)).comp ((deriv F w) • (1 : ℂ →L[ℝ] ℂ))) := by
    filter_upwards [hF.eventually_analyticAt] with w hw
    exact (((hG.differentiable two_ne_zero (F w)).hasFDerivAt).comp w
      hw.differentiableAt.hasDerivAt.complexToReal_fderiv).fderiv
  have hsecond := hchain.congr_of_eventuallyEq hlocal
  have hcalc (v w : ℂ) :
      fderiv ℝ (fderiv ℝ (fun q => G (F q))) z v w =
        A (a * v) (a * w) + B (b * v * w) := by
    rw [hsecond.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.smulRight_apply, smul_apply,
      one_apply_eq_self, smul_eq_mul]
    ring
  have hbI : b * I * I = -b := by
    rw [mul_assoc, I_mul_I, mul_neg_one]
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply]
  change fderiv ℝ (fderiv ℝ (fun q => G (F q))) z 1 1 +
      fderiv ℝ (fderiv ℝ (fun q => G (F q))) z I I =
    ‖a‖ ^ 2 * (A 1 1 + A I I)
  calc
    _ = A a a + A (a * I) (a * I) := by
      simp only [hcalc, mul_one, hbI, map_neg]
      ring
    _ = _ := complex_bilinear_trace A a

/-- The actual complex-plane chain step in the book's `W` computation,
valid also at zeros and for `p=2`. The analytic premise will be supplied by
the original Cauchy integral's already proved holomorphy calculation. -/
theorem laplacian_rieszAuxiliaryValue_comp {p : ℝ} (hp : 2 ≤ p)
    {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) :
    Laplacian.laplacian (fun w => rieszAuxiliaryValue p (F w)) z =
      ‖deriv F z‖ ^ 2 * Laplacian.laplacian (rieszAuxiliaryValue p) (F z) :=
  laplacian_comp_analytic_riesz (contDiff_two_rieszAuxiliaryValue hp) hF

end LowDimensionalTopology.Geometry.Quasiconformal
