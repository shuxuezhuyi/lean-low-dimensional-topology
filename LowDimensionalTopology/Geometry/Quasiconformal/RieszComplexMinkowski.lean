module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The squared Minkowski inequality for complex functions

The triangle inequality in `L^(p/2)` applied to
`|F|² = |Re F|² + |Im F|²` gives the component estimate. The real-valued
norm formulation retains explicit finiteness of the original Lp norms.
-/

@[expose] public section
noncomputable section

open MeasureTheory

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The book's `L^(p/2)` Minkowski inequality, allowing infinite norms. -/
theorem eLpNorm_complex_sq_le_re_im {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : α → ℂ} (hF : AEStronglyMeasurable F μ)
    {p : ℝ} (hp : 2 ≤ p) :
    eLpNorm F (ENNReal.ofReal p) μ ^ 2 ≤
      eLpNorm (fun x => (F x).re) (ENNReal.ofReal p) μ ^ 2 +
        eLpNorm (fun x => (F x).im) (ENNReal.ofReal p) μ ^ 2 := by
  have hRe : AEStronglyMeasurable (fun x => (F x).re) μ :=
    Complex.continuous_re.comp_aestronglyMeasurable hF
  have hIm : AEStronglyMeasurable (fun x => (F x).im) μ :=
    Complex.continuous_im.comp_aestronglyMeasurable hF
  have he : ENNReal.ofReal (p / 2) * ENNReal.ofReal (2 : ℝ) =
      ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ p / 2)]
    congr 1
    ring
  have hFnorm := eLpNorm_norm_rpow (μ := μ) (p := ENNReal.ofReal (p / 2))
    F hF (by norm_num : 0 < (2 : ℝ))
  have hRenorm := eLpNorm_norm_rpow (μ := μ) (p := ENNReal.ofReal (p / 2))
    (fun x => (F x).re) hRe (by norm_num : 0 < (2 : ℝ))
  have hImnorm := eLpNorm_norm_rpow (μ := μ) (p := ENNReal.ofReal (p / 2))
    (fun x => (F x).im) hIm (by norm_num : 0 < (2 : ℝ))
  rw [he, ENNReal.rpow_two] at hFnorm hRenorm hImnorm
  have hsplit : (fun x => ‖F x‖ ^ (2 : ℝ)) =
      (fun x => ‖(F x).re‖ ^ (2 : ℝ)) +
        (fun x => ‖(F x).im‖ ^ (2 : ℝ)) := by
    funext x
    simp only [Pi.add_apply, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      Complex.sq_norm, Complex.normSq_apply]
    ring
  calc
    eLpNorm F (ENNReal.ofReal p) μ ^ 2 =
        eLpNorm (fun x => ‖F x‖ ^ (2 : ℝ)) (ENNReal.ofReal (p / 2)) μ :=
      hFnorm.symm
    _ = eLpNorm ((fun x => ‖(F x).re‖ ^ (2 : ℝ)) +
        (fun x => ‖(F x).im‖ ^ (2 : ℝ))) (ENNReal.ofReal (p / 2)) μ := by
      rw [hsplit]
    _ ≤ eLpNorm (fun x => ‖(F x).re‖ ^ (2 : ℝ)) (ENNReal.ofReal (p / 2)) μ +
        eLpNorm (fun x => ‖(F x).im‖ ^ (2 : ℝ)) (ENNReal.ofReal (p / 2)) μ :=
      eLpNorm_add_le (ENNReal.one_le_ofReal.2 (by linarith))
    _ = _ := by rw [hRenorm, hImnorm]

/-- The real-valued version used after the book's horizontal-slice integrals
have been shown finite. Finiteness is explicit before taking `toReal`. -/
theorem eLpNorm_toReal_complex_sq_le_re_im {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : α → ℂ} {p : ℝ} (hp : 2 ≤ p)
    (hF : MemLp F (ENNReal.ofReal p) μ) :
    (eLpNorm F (ENNReal.ofReal p) μ).toReal ^ 2 ≤
      (eLpNorm (fun x => (F x).re) (ENNReal.ofReal p) μ).toReal ^ 2 +
        (eLpNorm (fun x => (F x).im) (ENNReal.ofReal p) μ).toReal ^ 2 := by
  have hRe := ENNReal.pow_ne_top (n := 2) hF.re.eLpNorm_ne_top
  have hIm := ENNReal.pow_ne_top (n := 2) hF.im.eLpNorm_ne_top
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hRe, hIm⟩)
    (eLpNorm_complex_sq_le_re_im hF.aestronglyMeasurable hp)
  simpa only [ENNReal.toReal_add hRe hIm, ENNReal.toReal_pow] using! h

end LowDimensionalTopology.Geometry.Quasiconformal
