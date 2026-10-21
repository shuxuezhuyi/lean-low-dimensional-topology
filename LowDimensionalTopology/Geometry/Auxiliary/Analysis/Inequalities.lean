/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Function.L2Space

/-!
Finite Cauchy–Schwarz inequalities and the weighted arithmetic–geometric mean inequality.
-/

public section

open scoped BigOperators

namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis

variable {ι K : Type*}

/-- A normed-division-ring form of the finite inequality used. -/
theorem finite_cauchy_schwarz [NormedDivisionRing K] (s : Finset ι) (a b : ι → K) :
    ‖∑ i ∈ s, a i * b i‖ ≤
      Real.sqrt (∑ i ∈ s, ‖a i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) := by
  calc
    ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i * b i‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by simp_rw [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt s _ _

/-- The real finite Cauchy–Schwarz inequality. -/
theorem cauchy_schwarz_real (s : Finset ι) (a b : ι → ℝ) :
    |∑ i ∈ s, a i * b i| ≤
      Real.sqrt (∑ i ∈ s, |a i| ^ 2) * Real.sqrt (∑ i ∈ s, |b i| ^ 2) := by
  simpa only [Real.norm_eq_abs] using finite_cauchy_schwarz s a b

/-- The complex finite Cauchy–Schwarz inequality. -/
theorem cauchy_schwarz_complex (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ≤
      Real.sqrt (∑ i ∈ s, ‖a i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) :=
  finite_cauchy_schwarz s a b

/-- The weighted AM–GM inequality. -/
theorem weighted_arithmetic_geometric_mean (s : Finset ι) (w y : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∏ i ∈ s, y i ^ w i ≤ ∑ i ∈ s, w i * y i :=
  Real.geom_mean_le_arith_mean_weighted s w y hw hsum hy

/-- A nonnegative second derivative gives convexity on an interval. -/
theorem convexOn_of_second_derivative_nonneg {a b : ℝ} {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioo a b))
    (h : ∀ x ∈ Set.Ioo a b, 0 ≤ (deriv^[2] f) x) :
    ConvexOn ℝ (Set.Ioo a b) f :=
  convexOn_of_deriv2_nonneg' (convex_Ioo a b) hf hf' h

/--
The integral Cauchy–Schwarz inequality for real square-integrable
functions. The `MemLp` hypotheses make the finite-integral convention explicit.
-/
theorem integral_cauchy_schwarz {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {f g : X → ℝ}
    (hf : MeasureTheory.MemLp f 2 μ) (hg : MeasureTheory.MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (f := f) (g := g) Real.HolderConjugate.two_two (by simpa using hf) (by simpa using hg)
  calc
    (∫ x, f x * g x ∂μ) ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
      apply MeasureTheory.integral_mono (hf.integrable_mul hg) (hf.norm.integrable_mul hg.norm)
      intro x
      exact (le_abs_self _).trans_eq (abs_mul _ _)
    _ ≤ _ := by simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs,
      ← Real.sqrt_eq_rpow] using h

end LowDimensionalTopology.Geometry.Auxiliary.Analysis
