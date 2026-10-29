module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealHilbertRealInput
public import LowDimensionalTopology.Geometry.Quasiconformal.RieszComponentNormComparison
public import LowDimensionalTopology.Geometry.Quasiconformal.RieszComplexificationConstant
public import LowDimensionalTopology.Unproved.Quasiconformal.RealDirectionalHilbert
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The real-line Riesz estimate

The real-input proof is combined with the actual principal-value component
identities and the native two-component norm comparison. The explicit continuous
constant absorbs the component factor while retaining continuity and A2=1.
The final theorem targets the unchanged original RealHilbertEstimate Prop,
including actual PV convergence and MemLp for every complex smooth compact
test. No Hilbert estimate, Lp extension or same-goal premise is assumed.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The actual original complex C1 compact test has both finite output and
the explicit bound. The real tests are its genuine Re/Im components. -/
theorem realHilbert_complex_memLp_and_norm_le {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) {p : ℝ} (hp : 2 ≤ p) :
    MemLp (realHilbertTransform φ) (ENNReal.ofReal p) volume ∧
      (eLpNorm (realHilbertTransform φ) (ENNReal.ofReal p) volume).toReal ≤
        rieszBookConstant p * (eLpNorm φ (ENNReal.ofReal p) volume).toReal := by
  let H : ℝ → ℂ := realHilbertTransform φ
  let B : ℝ := (rieszBookDenominator p) ^ (-(1 / 2 : ℝ))
  let c : ℝ := (2 : ℝ) ^ ((1 / 2 : ℝ) - 1 / p)
  have hRe : ContDiff ℝ 1 (fun x => (φ x).re) := Complex.reCLM.contDiff.comp hφ
  have hIm : ContDiff ℝ 1 (fun x => (φ x).im) := Complex.imCLM.contDiff.comp hφ
  have hcRe : HasCompactSupport (fun x => (φ x).re) :=
    hc.comp_left (g := Complex.re) rfl
  have hcIm : HasCompactSupport (fun x => (φ x).im) :=
    hc.comp_left (g := Complex.im) rfl
  have hRtest : MemLp (realHilbertTransform (fun x => ((φ x).re : ℂ)))
      (ENNReal.ofReal p) volume :=
    (realHilbert_ofReal_memLp_and_eLpNorm_le hRe hcRe hp).1
  have hItest : MemLp (realHilbertTransform (fun x => ((φ x).im : ℂ)))
      (ENNReal.ofReal p) volume :=
    (realHilbert_ofReal_memLp_and_eLpNorm_le hIm hcIm hp).1
  have hHRe : MemLp (fun ξ => (H ξ).re) (ENNReal.ofReal p) volume := by
    apply hRtest.re.ae_eq
    exact Eventually.of_forall fun ξ => by
      simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re, H] using!
        congrArg Complex.re (realHilbertTransform_realPart hφ hc ξ)
  have hHIm : MemLp (fun ξ => (H ξ).im) (ENNReal.ofReal p) volume := by
    apply hItest.re.ae_eq
    exact Eventually.of_forall fun ξ => by
      simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re, H] using!
        congrArg Complex.re (realHilbertTransform_imaginaryPart hφ hc ξ)
  have hH : MemLp H (ENNReal.ofReal p) volume := by
    apply (memLp_re_im_iff (f := H)).1
    constructor
    · simpa only [RCLike.re_eq_complex_re] using! hHRe
    · simpa only [RCLike.im_eq_complex_im] using! hHIm
  have hNormRe : eLpNorm (fun ξ => (H ξ).re) (ENNReal.ofReal p) volume =
      eLpNorm (realHilbertTransform (fun x => ((φ x).re : ℂ))) (ENNReal.ofReal p) volume := by
    apply eLpNorm_congr_norm_ae hHRe.aestronglyMeasurable hRtest.aestronglyMeasurable
    exact Eventually.of_forall fun ξ => by
      rw [realHilbertTransform_realPart hφ hc ξ]
      exact (Complex.norm_real ((H ξ).re)).symm
  have hNormIm : eLpNorm (fun ξ => (H ξ).im) (ENNReal.ofReal p) volume =
      eLpNorm (realHilbertTransform (fun x => ((φ x).im : ℂ))) (ENNReal.ofReal p) volume := by
    apply eLpNorm_congr_norm_ae hHIm.aestronglyMeasurable hItest.aestronglyMeasurable
    exact Eventually.of_forall fun ξ => by
      rw [realHilbertTransform_imaginaryPart hφ hc ξ]
      exact (Complex.norm_real ((H ξ).im)).symm
  let Nout : ℝ := (eLpNorm H (ENNReal.ofReal p) volume).toReal
  let NoutRe : ℝ := (eLpNorm (fun ξ => (H ξ).re) (ENNReal.ofReal p) volume).toReal
  let NoutIm : ℝ := (eLpNorm (fun ξ => (H ξ).im) (ENNReal.ofReal p) volume).toReal
  let Nin : ℝ := (eLpNorm φ (ENNReal.ofReal p) volume).toReal
  let NinRe : ℝ := (eLpNorm (fun x => (φ x).re) (ENNReal.ofReal p) volume).toReal
  let NinIm : ℝ := (eLpNorm (fun x => (φ x).im) (ENNReal.ofReal p) volume).toReal
  have hB : 0 ≤ B := Real.rpow_nonneg (rieszBookDenominator_bounds hp).1.le _
  have hcomp : 0 ≤ c := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  have hNout : 0 ≤ Nout := ENNReal.toReal_nonneg
  have hNoutRe : 0 ≤ NoutRe := ENNReal.toReal_nonneg
  have hNoutIm : 0 ≤ NoutIm := ENNReal.toReal_nonneg
  have hNin : 0 ≤ Nin := ENNReal.toReal_nonneg
  have hNinRe : 0 ≤ NinRe := ENNReal.toReal_nonneg
  have hNinIm : 0 ≤ NinIm := ENNReal.toReal_nonneg
  have hRbound : NoutRe ≤ B * NinRe := by
    change (eLpNorm (fun ξ => (H ξ).re) (ENNReal.ofReal p) volume).toReal ≤ _
    rw [hNormRe]
    exact realHilbert_ofReal_norm_le hRe hcRe hp
  have hIbound : NoutIm ≤ B * NinIm := by
    change (eLpNorm (fun ξ => (H ξ).im) (ENNReal.ofReal p) volume).toReal ≤ _
    rw [hNormIm]
    exact realHilbert_ofReal_norm_le hIm hcIm hp
  have hφp : MemLp φ (ENNReal.ofReal p) volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hφRe : MemLp (fun x => (φ x).re) (ENNReal.ofReal p) volume := by
    simpa only [RCLike.re_eq_complex_re] using! hφp.re
  have hφIm : MemLp (fun x => (φ x).im) (ENNReal.ofReal p) volume := by
    simpa only [RCLike.im_eq_complex_im] using! hφp.im
  have hcoef : (2 : ℝ≥0∞) ^ (1 - 2 / p) = ENNReal.ofReal ((2 : ℝ) ^ (1 - 2 / p)) := by
    simpa using ENNReal.ofReal_rpow_of_pos (p := 1 - 2 / p) (by norm_num : (0 : ℝ) < 2)
  have hinput := eLpNorm_re_im_sq_le_complex hφ.continuous hp
  rw [hcoef] at hinput
  have hReSq := ENNReal.pow_ne_top (n := 2) hφRe.eLpNorm_ne_top
  have hImSq := ENNReal.pow_ne_top (n := 2) hφIm.eLpNorm_ne_top
  have hRight : ENNReal.ofReal ((2 : ℝ) ^ (1 - 2 / p)) *
      eLpNorm φ (ENNReal.ofReal p) volume ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top (n := 2) hφp.eLpNorm_ne_top)
  have hinputReal : NinRe ^ 2 + NinIm ^ 2 ≤ (2 : ℝ) ^ (1 - 2 / p) * Nin ^ 2 := by
    have h := ENNReal.toReal_mono hRight hinput
    simpa only [NinRe, NinIm, Nin, ENNReal.toReal_add hReSq hImSq,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)] using! h
  have hcsq : c ^ 2 = (2 : ℝ) ^ (1 - 2 / p) := by
    dsimp only [c]
    rw [← Real.rpow_two, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hmink : Nout ^ 2 ≤ NoutRe ^ 2 + NoutIm ^ 2 := by
    simpa only [Nout, NoutRe, NoutIm] using! eLpNorm_toReal_complex_sq_le_re_im hp hH
  have hRboundSq : NoutRe ^ 2 ≤ (B * NinRe) ^ 2 :=
    (sq_le_sq₀ hNoutRe (mul_nonneg hB hNinRe)).2 hRbound
  have hIboundSq : NoutIm ^ 2 ≤ (B * NinIm) ^ 2 :=
    (sq_le_sq₀ hNoutIm (mul_nonneg hB hNinIm)).2 hIbound
  have hsquare : Nout ^ 2 ≤ (B * c * Nin) ^ 2 := by
    calc
      _ ≤ NoutRe ^ 2 + NoutIm ^ 2 := hmink
      _ ≤ (B * NinRe) ^ 2 + (B * NinIm) ^ 2 := by gcongr
      _ = B ^ 2 * (NinRe ^ 2 + NinIm ^ 2) := by ring
      _ ≤ B ^ 2 * ((2 : ℝ) ^ (1 - 2 / p) * Nin ^ 2) :=
        mul_le_mul_of_nonneg_left hinputReal (sq_nonneg B)
      _ = _ := by rw [mul_pow, mul_pow, hcsq]; ring
  have hout : Nout ≤ B * c * Nin :=
    (sq_le_sq₀ hNout (mul_nonneg (mul_nonneg hB hcomp) hNin)).1 hsquare
  have hbook : B * c ≤ rieszBookConstant p := riesz_real_constant_mul_component_factor_le_book hp
  have hnorm : Nout ≤ rieszBookConstant p * Nin :=
    hout.trans (mul_le_mul_of_nonneg_right hbook hNin)
  exact ⟨hH, hnorm⟩

/-- The unchanged original full specified-family contract, including genuine
PV convergence, complex smooth compact tests, MemLp, continuity and A2=1. -/
theorem realHilbertEstimate_rieszBookConstant :
    LowDimensionalTopology.Unproved.Quasiconformal.RealHilbertEstimate rieszBookConstant := by
  refine ⟨rieszBookConstant_continuousOn, rieszBookConstant_two, ?_⟩
  intro p hp φ hφ hc
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  obtain ⟨hmem, hnorm⟩ := realHilbert_complex_memLp_and_norm_le hφ1 hc hp
  exact ⟨fun ξ => (realHilbert_principalValue_and_eq_paired hφ1 hc ξ).1, hmem, hnorm⟩

/-- The real-line Riesz estimate with the explicit continuous family as witness. -/
theorem rieszRealHilbertEstimate :
    LowDimensionalTopology.Unproved.Quasiconformal.RieszRealHilbertEstimate :=
  ⟨rieszBookConstant, realHilbertEstimate_rieszBookConstant⟩

end LowDimensionalTopology.Geometry.Quasiconformal
