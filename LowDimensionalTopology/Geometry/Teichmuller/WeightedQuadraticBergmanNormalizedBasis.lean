module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanMonomialGram
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Tactic.Ring

/-!
# The specified normalized monomial basis of the original weighted disc space

The exact Gram matrix proves orthonormality of the specified normalized
monomials. The true kernel series and reproduction force their orthogonal
complement to vanish in the original carrier. This constructs the actual Hilbert
basis and gives its norm expansions and conjugate-first kernel series.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ComplexConjugate ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman

private theorem normalizedMonomial_scale_sq (n : ℕ) :
    (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) ^ 2 = (diskKernelSeriesCoefficient n : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (diskKernelSeriesCoefficient_pos n).le]

private theorem normalizedMonomial_scale_ne_zero (n : ℕ) :
    (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.2 (diskKernelSeriesCoefficient_pos n))

/-- The specified normalization is applied to the genuine original monomial class. -/
def normalizedMonomial (n : ℕ) : Disk :=
  (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) • monomialElement n

/-- Every original disc value is the literal normalized monomial. -/
theorem normalizedMonomial_coefficient (n : ℕ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    coefficient (normalizedMonomial n) z =
      (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) * z ^ n := by
  rw [disk_reproducing_inner (normalizedMonomial n) hz]
  change inner ℂ (diskKernelElement hz)
    ((Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) • monomialElement n) = _
  rw [inner_smul_right (𝕜 := ℂ) (diskKernelElement hz) (monomialElement n)
    (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ),
    ← disk_reproducing_inner (monomialElement n) hz, monomialElement_coefficient n hz]

/-- The coefficient retains the exact cubic normalization of the original weight. -/
theorem normalizedMonomial_coefficient_explicit (n : ℕ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    coefficient (normalizedMonomial n) z =
      (Real.sqrt ((2 / Real.pi) * ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) : ℂ) * z ^ n := by
  rw [normalizedMonomial_coefficient n hz, diskKernelSeriesCoefficient_eq_product]

/-- The specified normalized monomials are orthonormal in the unchanged native inner product. -/
theorem normalizedMonomial_orthonormal : Orthonormal ℂ normalizedMonomial := by
  rw [orthonormal_iff_ite]
  intro n m
  change inner ℂ ((Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) • monomialElement n)
    ((Real.sqrt (diskKernelSeriesCoefficient m) : ℂ) • monomialElement m) = _
  rw [inner_smul_left (𝕜 := ℂ) (monomialElement n)
    ((Real.sqrt (diskKernelSeriesCoefficient m) : ℂ) • monomialElement m)
    (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ),
    inner_smul_right (𝕜 := ℂ) (monomialElement n) (monomialElement m)
      (Real.sqrt (diskKernelSeriesCoefficient m) : ℂ),
    Complex.conj_ofReal, monomialElement_gram n m]
  by_cases hnm : n = m
  · subst m
    simp only
    calc
      (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) *
          ((Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) *
            (diskKernelSeriesCoefficient n : ℂ)⁻¹) =
          (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) ^ 2 *
            (diskKernelSeriesCoefficient n : ℂ)⁻¹ := by ring
      _ = 1 := by
        rw [normalizedMonomial_scale_sq,
          mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (diskKernelSeriesCoefficient_pos n).ne')]
  · simp only [ite_eq_right hnm, mul_zero]

/-- The original-carrier orthogonal complement is zero, as forced by actual reproduction. -/
theorem normalizedMonomial_span_orthogonal :
    (Submodule.span ℂ (Set.range normalizedMonomial))ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro q hq
  have hE : ∀ n, inner ℂ (normalizedMonomial n) q = 0 := by
    intro n
    exact (Submodule.mem_orthogonal (Submodule.span ℂ (Set.range normalizedMonomial)) q).mp hq
      (normalizedMonomial n) (Submodule.subset_span ⟨n, rfl⟩)
  have hM : ∀ n, inner ℂ (monomialElement n) q = 0 := by
    intro n
    have hn := hE n
    change inner ℂ ((Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) • monomialElement n) q = 0 at hn
    rw [inner_smul_left (𝕜 := ℂ) (monomialElement n) q
      (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ), Complex.conj_ofReal] at hn
    exact (mul_eq_zero.mp hn).resolve_left (normalizedMonomial_scale_ne_zero n)
  have hq0 : q = 0 := by
    apply disk_coefficient_ext
    intro a ha
    have hs := (innerSLFlip ℂ q).hasSum (diskKernelSeries_hasSum ha)
    change HasSum (fun n => inner ℂ (diskKernelSeriesTerm a n) q)
      (inner ℂ (diskKernelElement ha) q) at hs
    have hz : HasSum (fun _ : ℕ => (0 : ℂ)) (inner ℂ (diskKernelElement ha) q) := by
      refine hs.congr_fun fun n => ?_
      change 0 = inner ℂ (((diskKernelSeriesCoefficient n : ℂ) * conj a ^ n) • monomialElement n) q
      rw [inner_smul_left (𝕜 := ℂ) (monomialElement n) q
        ((diskKernelSeriesCoefficient n : ℂ) * conj a ^ n), hM n, mul_zero]
    have hi : inner ℂ (diskKernelElement ha) q = 0 := hz.unique hasSum_zero
    have hzero : coefficient (0 : Disk) a = 0 := by
      rw [disk_reproducing_inner (0 : Disk) ha]
      exact inner_zero_right (𝕜 := ℂ) (diskKernelElement ha)
    exact ((disk_reproducing_inner q ha).trans hi).trans hzero.symm
  rw [hq0]
  exact Submodule.zero_mem _

/-- The Hilbert basis has the specified original normalized monomials as its family. -/
def normalizedMonomialBasis : HilbertBasis ℕ ℂ Disk :=
  HilbertBasis.mkOfOrthogonalEqBot normalizedMonomial_orthonormal normalizedMonomial_span_orthogonal

theorem normalizedMonomialBasis_apply (n : ℕ) :
    normalizedMonomialBasis n = normalizedMonomial n :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    normalizedMonomial_orthonormal normalizedMonomial_span_orthogonal) n

/-- Every original vector has its genuine native L² expansion with the first-linear book slots. -/
theorem normalizedMonomial_hasSum (q : Disk) :
    HasSum (fun n => pairing q (normalizedMonomial n) • normalizedMonomial n) q := by
  simpa only [HilbertBasis.repr_apply_apply, normalizedMonomialBasis_apply, pairing] using
    normalizedMonomialBasis.hasSum_repr q

/-- The actual scalar coefficients for the original power-series expansion. -/
def diskMonomialExpansionCoefficient (q : Disk) (n : ℕ) : ℂ :=
  pairing q (normalizedMonomial n) * (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ)

/-- The same expansion retains every original disc coefficient value. -/
theorem diskMonomialExpansion_hasSum (q : Disk) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    HasSum (fun n => diskMonomialExpansionCoefficient q n * z ^ n) (coefficient q z) := by
  have hs := (innerSL ℂ (diskKernelElement hz)).hasSum (normalizedMonomial_hasSum q)
  rw [disk_reproducing_inner q hz]
  refine hs.congr_fun fun n => ?_
  change (pairing q (normalizedMonomial n) * (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ)) *
    z ^ n = inner ℂ (diskKernelElement hz) (pairing q (normalizedMonomial n) • normalizedMonomial n)
  rw [inner_smul_right (𝕜 := ℂ) (diskKernelElement hz) (normalizedMonomial n)
    (pairing q (normalizedMonomial n)),
    ← disk_reproducing_inner (normalizedMonomial n) hz, normalizedMonomial_coefficient n hz]
  ring

/-- The normalized kernel summand is the actual original monomial kernel summand. -/
theorem normalizedMonomial_kernel_term_eq (n : ℕ) {a : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    conj (coefficient (normalizedMonomial n) a) • normalizedMonomial n = diskKernelSeriesTerm a n := by
  rw [normalizedMonomial_coefficient n ha]
  change conj ((Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) * a ^ n) •
    ((Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) • monomialElement n) =
      ((diskKernelSeriesCoefficient n : ℂ) * conj a ^ n) • monomialElement n
  rw [smul_smul, map_mul, map_pow, Complex.conj_ofReal]
  apply congrArg (fun c : ℂ => c • monomialElement n)
  calc
    ((Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) * conj a ^ n) *
        (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) =
      (Real.sqrt (diskKernelSeriesCoefficient n) : ℂ) ^ 2 * conj a ^ n := by ring
    _ = _ := by rw [normalizedMonomial_scale_sq]

/-- The canonical normalized kernel series is absolutely summable in the actual disc norm. -/
theorem normalizedMonomial_kernel_norm_summable {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    Summable (fun n => ‖conj (coefficient (normalizedMonomial n) a) • normalizedMonomial n‖) := by
  simpa only [normalizedMonomial_kernel_term_eq _ ha] using diskKernelSeries_norm_summable ha

/-- The normalized series converges to the actual kernel in the original native L² norm. -/
theorem normalizedMonomial_kernel_hasSum {a : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1) :
    HasSum (fun n => conj (coefficient (normalizedMonomial n) a) • normalizedMonomial n)
      (diskKernelElement ha) := by
  simpa only [normalizedMonomial_kernel_term_eq _ ha] using diskKernelSeries_hasSum ha

/-- The basis-defined conjugate-first kernel series agrees at every pair of original disc points. -/
theorem normalizedMonomial_kernel_scalar_hasSum {a b : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) (hb : b ∈ Metric.ball (0 : ℂ) 1) :
    HasSum (fun n => conj (coefficient (normalizedMonomial n) a) *
      coefficient (normalizedMonomial n) b) (diskQuadraticKernel a b) := by
  have hs := (innerSL ℂ (diskKernelElement hb)).hasSum (normalizedMonomial_kernel_hasSum ha)
  have hv : HasSum (fun n => conj (coefficient (normalizedMonomial n) a) *
      coefficient (normalizedMonomial n) b) (coefficient (diskKernelElement ha) b) := by
    rw [disk_reproducing_inner (diskKernelElement ha) hb]
    refine hs.congr_fun fun n => ?_
    change conj (coefficient (normalizedMonomial n) a) * coefficient (normalizedMonomial n) b =
      inner ℂ (diskKernelElement hb)
        (conj (coefficient (normalizedMonomial n) a) • normalizedMonomial n)
    rw [inner_smul_right (𝕜 := ℂ) (diskKernelElement hb) (normalizedMonomial n)
      (conj (coefficient (normalizedMonomial n) a)),
      ← disk_reproducing_inner (normalizedMonomial n) hb]
  rw [diskKernelElement_coefficient ha hb] at hv
  exact hv

/-- The complete normalized basis series has the literal original fourth-power value. -/
theorem normalizedMonomial_kernel_tsum {a b : ℂ}
    (ha : a ∈ Metric.ball (0 : ℂ) 1) (hb : b ∈ Metric.ball (0 : ℂ) 1) :
    ∑' n, conj (coefficient (normalizedMonomial n) a) * coefficient (normalizedMonomial n) b =
      (12 / Real.pi : ℂ) / (1 - conj a * b) ^ 4 := by
  simpa only [diskQuadraticKernel] using (normalizedMonomial_kernel_scalar_hasSum ha hb).tsum_eq

end LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman
