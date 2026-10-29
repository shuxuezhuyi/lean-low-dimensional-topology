module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanNormalizedBasis
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Parseval identities in the original weighted disc space

The specified normalized monomial basis gives Parseval for every original
vector. Its actual power-series coefficients retain the precise cubic weights
of the same native square-integral norm.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman

/-- Parseval uses the specified basis and the first-linear pairing on the original carrier. -/
theorem normalizedMonomial_parseval (q : Disk) :
    HasSum (fun n => ‖pairing q (normalizedMonomial n)‖ ^ 2) (‖q‖ ^ 2) := by
  have htwo : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  have hs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
    (normalizedMonomialBasis.repr q)
  simpa only [htwo, Real.rpow_two, HilbertBasis.repr_apply_apply,
    normalizedMonomialBasis_apply, LinearIsometryEquiv.norm_map, pairing] using hs

private theorem expansionCoefficient_norm_sq (q : Disk) (n : ℕ) :
    ‖diskMonomialExpansionCoefficient q n‖ ^ 2 =
      ‖pairing q (normalizedMonomial n)‖ ^ 2 * diskKernelSeriesCoefficient n := by
  change ‖pairing q (normalizedMonomial n) *
    (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ)‖ ^ 2 = _
  rw [norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (diskKernelSeriesCoefficient_pos n).le]

/-- The original power coefficients have a genuinely summable weighted square norm. -/
theorem diskMonomialExpansion_parseval (q : Disk) :
    HasSum (fun n => ‖diskMonomialExpansionCoefficient q n‖ ^ 2 /
      diskKernelSeriesCoefficient n) (‖q‖ ^ 2) := by
  refine (normalizedMonomial_parseval q).congr_fun fun n => ?_
  exact (div_eq_iff (diskKernelSeriesCoefficient_pos n).ne').mpr
    (expansionCoefficient_norm_sq q n)

/-- The exact weights retain the original disc density normalization. -/
theorem diskMonomialExpansion_parseval_explicit (q : Disk) :
    HasSum (fun n : ℕ =>
      (Real.pi / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) *
        ‖diskMonomialExpansionCoefficient q n‖ ^ 2) (‖q‖ ^ 2) := by
  refine (diskMonomialExpansion_parseval q).congr_fun fun n => ?_
  have hw : 1 / diskKernelSeriesCoefficient n =
      Real.pi / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) :=
    (monomialElement_norm_sq n).symm.trans (monomialElement_norm_sq_explicit n)
  rw [← hw]
  ring

/-- The original norm square is the convergent, precisely weighted coefficient sum. -/
theorem diskMonomialExpansion_norm_sq_explicit (q : Disk) :
    ‖q‖ ^ 2 = ∑' n : ℕ,
      (Real.pi / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))) *
        ‖diskMonomialExpansionCoefficient q n‖ ^ 2 :=
  (diskMonomialExpansion_parseval_explicit q).tsum_eq.symm

end LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman
