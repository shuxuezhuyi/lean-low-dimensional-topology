module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanReproduction
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Point evaluation bounds in the full weighted half-plane space

The genuine kernel element has an exact norm determined by its diagonal value.
The original L² inner product then bounds every coefficient value. On every
actual compact subset of the upper half-plane, a single constant controls all
coefficient differences by the original ambient L² difference norm.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ComplexConjugate ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman

open LiZhongQC QuadraticBergman

/-- The literal kernel diagonal, with the original positive normalization. -/
theorem halfPlaneQuadraticKernel_diagonal {z : ℂ} (hz : z ∈ upperHalf) :
    halfPlaneQuadraticKernel z z = ((3 / (4 * Real.pi * z.im ^ 4) : ℝ) : ℂ) := by
  have hy : (z.im : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (show 0 < z.im from hz).ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hpow : (conj z - z) ^ 4 = (z - conj z) ^ 4 := by ring
  unfold halfPlaneQuadraticKernel
  rw [hpow, Complex.sub_conj, mul_pow, Complex.I_pow_four, mul_one]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  field_simp [hπ, hy]
  ring

/-- The norm is derived from the actual reproducing formula, not supplied as data. -/
theorem halfPlaneKernelElement_norm_sq {z : ℂ} (hz : z ∈ upperHalf) :
    ‖halfPlaneKernelElement hz‖ ^ 2 = 3 / (4 * Real.pi * z.im ^ 4) := by
  have he : halfPlaneQuadraticKernel z z =
      inner ℂ (halfPlaneKernelElement hz) (halfPlaneKernelElement hz) :=
    (halfPlaneKernelElement_coefficient hz hz).symm.trans
      (halfPlane_reproducing_inner (halfPlaneKernelElement hz) hz)
  have hn := norm_sq_eq_re_inner (𝕜 := ℂ) (halfPlaneKernelElement hz)
  change ‖halfPlaneKernelElement hz‖ ^ 2 =
    (inner ℂ (halfPlaneKernelElement hz) (halfPlaneKernelElement hz)).re at hn
  calc
    ‖halfPlaneKernelElement hz‖ ^ 2 =
        (inner ℂ (halfPlaneKernelElement hz) (halfPlaneKernelElement hz)).re := hn
    _ = (halfPlaneQuadraticKernel z z).re := congrArg Complex.re he.symm
    _ = _ := by rw [halfPlaneQuadraticKernel_diagonal hz, Complex.ofReal_re]

/-- The exact numerical point-evaluation bound on the original upper half-plane. -/
def halfPlaneEvaluationBound (z : ℂ) : ℝ :=
  Real.sqrt (3 / (4 * Real.pi * z.im ^ 4))

theorem halfPlaneKernelElement_norm {z : ℂ} (hz : z ∈ upperHalf) :
    ‖halfPlaneKernelElement hz‖ = halfPlaneEvaluationBound z := by
  unfold halfPlaneEvaluationBound
  rw [← halfPlaneKernelElement_norm_sq hz, Real.sqrt_sq (norm_nonneg _)]

/-- Every element of the full original space satisfies the point-evaluation estimate. -/
theorem halfPlane_evaluation_bound (q : HalfPlane) {z : ℂ} (hz : z ∈ upperHalf) :
    ‖coefficient q z‖ ≤ halfPlaneEvaluationBound z * ‖q‖ := by
  calc
    ‖coefficient q z‖ = ‖inner ℂ (halfPlaneKernelElement hz) q‖ := by
      rw [halfPlane_reproducing_inner q hz]
    _ ≤ ‖halfPlaneKernelElement hz‖ * ‖q‖ := by
      have h := norm_inner_le_norm (𝕜 := ℂ) (halfPlaneKernelElement hz) q
      rw [← RCLike.sqrt_normSq_eq_norm, RCLike.normSq_apply,
        RCLike.re_eq_complex_re, RCLike.im_eq_complex_im] at h
      simpa only [Complex.norm_def, Complex.normSq_apply] using h
    _ = _ := by rw [halfPlaneKernelElement_norm hz]

/-- Subtraction of the original L² classes agrees at every original domain point. -/
theorem halfPlane_coefficient_sub (q r : HalfPlane) :
    EqOn (coefficient (q - r)) (fun z => coefficient q z - coefficient r z) upperHalf := by
  refine halfPlane_coefficient_eqOn (q - r)
    ((coefficient_holomorphic q).sub (coefficient_holomorphic r)) ?_
  change ((q.val - r.val : Lp ℂ 2 halfPlaneMeasure) : ℂ → ℂ) =ᵐ[halfPlaneMeasure]
    fun z => coefficient q z - coefficient r z
  filter_upwards [Lp.coeFn_sub q.val r.val, coefficient_ae q, coefficient_ae r]
    with z hsub hq hr
  simpa only [Pi.sub_apply, hq, hr] using hsub

private theorem halfPlane_sub_norm (q r : HalfPlane) :
    ‖(q - r : HalfPlane)‖ = ‖q.val - r.val‖ :=
  (Submodule.norm_coe (q - r)).symm.trans (congrArg norm (Submodule.coe_sub _ q r))

/-- The point estimate for two coefficients uses their genuine ambient L² difference norm. -/
theorem halfPlane_evaluation_sub_bound (q r : HalfPlane) {z : ℂ} (hz : z ∈ upperHalf) :
    ‖coefficient q z - coefficient r z‖ ≤
      halfPlaneEvaluationBound z * ‖q.val - r.val‖ := by
  have h := halfPlane_evaluation_bound (q - r) hz
  rw [halfPlane_coefficient_sub q r hz, halfPlane_sub_norm] at h
  exact h

private theorem halfPlaneEvaluationBound_continuousOn :
    ContinuousOn halfPlaneEvaluationBound upperHalf := by
  unfold halfPlaneEvaluationBound
  refine (continuousOn_const.div
    (continuousOn_const.mul (Complex.continuous_im.continuousOn.pow 4)) ?_).sqrt
  intro z hz
  exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    (pow_ne_zero 4 (show 0 < z.im from hz).ne')

private theorem halfPlaneEvaluationBound_bounded_on_compact {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ upperHalf) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, halfPlaneEvaluationBound z ≤ C := by
  have hc : IsCompact (halfPlaneEvaluationBound '' K) :=
    hK.image_of_continuousOn (halfPlaneEvaluationBound_continuousOn.mono hKH)
  obtain ⟨C, hC⟩ := hc.isBounded.exists_norm_le
  refine ⟨max 0 C, le_max_left _ _, fun z hz => ?_⟩
  have hb : halfPlaneEvaluationBound z ≤ C := by
    have hn := hC _ (mem_image_of_mem halfPlaneEvaluationBound hz)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hn)
  exact hb.trans (le_max_right _ _)

/-- Every actual compact subset has one bound for all original coefficient values. -/
theorem halfPlane_evaluation_bound_on_compact {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ upperHalf) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : HalfPlane, ∀ z ∈ K, ‖coefficient q z‖ ≤ C * ‖q‖ := by
  obtain ⟨C, hC, hb⟩ := halfPlaneEvaluationBound_bounded_on_compact hK hKH
  refine ⟨C, hC, fun q z hz => ?_⟩
  exact (halfPlane_evaluation_bound q (hKH hz)).trans
    (mul_le_mul_of_nonneg_right (hb z hz) (norm_nonneg _))

/-- One compact-set constant controls all differences in the original ambient norm. -/
theorem halfPlane_evaluation_sub_bound_on_compact {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ upperHalf) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q r : HalfPlane, ∀ z ∈ K,
      ‖coefficient q z - coefficient r z‖ ≤ C * ‖q.val - r.val‖ := by
  obtain ⟨C, hC, hb⟩ := halfPlaneEvaluationBound_bounded_on_compact hK hKH
  refine ⟨C, hC, fun q r z hz => ?_⟩
  exact (halfPlane_evaluation_sub_bound q r (hKH hz)).trans
    (mul_le_mul_of_nonneg_right (hb z hz) (norm_nonneg _))

end LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman
