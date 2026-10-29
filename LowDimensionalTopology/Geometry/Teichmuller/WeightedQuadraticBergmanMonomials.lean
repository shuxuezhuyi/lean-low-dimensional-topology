module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanDiskReproduction
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp

/-!
# Monomials in the original weighted disc space

The kernel at the origin supplies genuine weighted L² membership of the
constant function. Pointwise domination then puts every monomial in the
unchanged disc carrier and bounds its native norm by the constant monomial.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ComplexConjugate ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman

private theorem diskMeasure_ae_mem :
    ∀ᵐ z ∂diskMeasure, z ∈ Metric.ball (0 : ℂ) 1 :=
  (withDensity_absolutelyContinuous (volume.restrict (Metric.ball (0 : ℂ) 1))
    (fun z => (diskWeight z : ℝ≥0∞))).ae_le (ae_restrict_mem measurableSet_ball)

private theorem norm_monomial_le_one (n : ℕ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) : ‖z ^ n‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg z) (mem_ball_zero_iff.mp hz).le

/-- The constant function belongs to the original weighted L² space. -/
theorem disk_memLp_const_one : MemLp (fun _ : ℂ => (1 : ℂ)) 2 diskMeasure := by
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have he : (fun z : ℂ => (Real.pi / 12 : ℂ) * diskQuadraticKernel 0 z) =
      (fun _ : ℂ => (1 : ℂ)) := by
    funext z
    simp only [diskQuadraticKernel, map_zero, zero_mul, sub_zero, one_pow, div_one]
    field_simp [hπ]
  rw [← he]
  exact (diskKernel_memLp h0).const_mul (Real.pi / 12 : ℂ)

/-- Every monomial has a genuinely finite original weighted L² norm. -/
theorem disk_monomial_memLp (n : ℕ) :
    MemLp (fun z : ℂ => z ^ n) 2 diskMeasure := by
  have hm : Measurable (fun z : ℂ => z ^ n) := by fun_prop
  refine disk_memLp_const_one.of_le hm.aestronglyMeasurable ?_
  filter_upwards [diskMeasure_ae_mem] with z hz
  simpa only [norm_one] using norm_monomial_le_one n hz

/-- A monomial as an element of the full original weighted disc carrier. -/
def monomialElement (n : ℕ) : Disk :=
  ofFunction (fun z : ℂ => z ^ n) (differentiableOn_id.pow n) (disk_monomial_memLp n)

/-- The chosen holomorphic representative retains every original monomial value. -/
theorem monomialElement_coefficient (n : ℕ) :
    EqOn (coefficient (monomialElement n)) (fun z : ℂ => z ^ n) (Metric.ball (0 : ℂ) 1) :=
  disk_coefficient_ofFunction _ _ _

/-- All monomials are uniformly bounded in the unchanged native disc norm. -/
theorem monomialElement_norm_le (n : ℕ) : ‖monomialElement n‖ ≤ ‖monomialElement 0‖ := by
  change ‖(monomialElement n).val‖ ≤ ‖(monomialElement 0).val‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [diskMeasure_ae_mem, coefficient_ae (monomialElement n),
    coefficient_ae (monomialElement 0)] with z hz hn h0
  rw [hn, h0, monomialElement_coefficient n hz, monomialElement_coefficient 0 hz]
  simpa only [pow_zero, norm_one] using norm_monomial_le_one n hz

end LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman
