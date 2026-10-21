/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Explicit upper-half-plane metric formulas

These statements use the actual `MetricSpace` instance on `UpperHalfPlane`.
They establish all five expressions for Mathlib's explicit
hyperbolic distance. this formulation first defines distance through weighted lengths
of piecewise continuously differentiable curves. Equality with that separate
path-length construction remains to be established; this module does not
rename Mathlib's distance to conceal that missing bridge.
-/

public section

open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The cosh-distance formula in the upper half-plane. -/
theorem halfPlane_cosh_dist_eq_norm_sq_formula (z w : ℍ) :
    Real.cosh (dist z w) = 1 + ‖(z : ℂ) - w‖ ^ 2 / (2 * z.im * w.im) := by
  simpa only [Complex.dist_eq] using UpperHalfPlane.cosh_dist z w

/-- The sinh half-distance formula in the upper half-plane. -/
theorem halfPlane_sinh_half_dist_eq_norm_formula (z w : ℍ) :
    Real.sinh (dist z w / 2) = ‖(z : ℂ) - w‖ / (2 * Real.sqrt (z.im * w.im)) := by
  simpa only [Complex.dist_eq] using UpperHalfPlane.sinh_half_dist z w

/-- The cosh half-distance formula in the upper half-plane. -/
theorem halfPlane_cosh_half_dist_eq_conjugate_norm_formula (z w : ℍ) :
    Real.cosh (dist z w / 2) = ‖(z : ℂ) - conj (w : ℂ)‖ /
      (2 * Real.sqrt (z.im * w.im)) := by
  simpa only [Complex.dist_eq] using UpperHalfPlane.cosh_half_dist z w

/-- The tanh half-distance formula in the upper half-plane. -/
theorem halfPlane_tanh_half_dist_eq_norm_ratio (z w : ℍ) :
    Real.tanh (dist z w / 2) = ‖(z : ℂ) - w‖ / ‖(z : ℂ) - conj (w : ℂ)‖ := by
  simpa only [Complex.dist_eq] using UpperHalfPlane.tanh_half_dist z w

/-- The difference in the denominator of the logarithmic formula is strictly positive. -/
theorem logarithmic_denominator_pos (z w : ℍ) :
    0 < ‖(z : ℂ) - conj (w : ℂ)‖ - ‖(z : ℂ) - w‖ := by
  have hk : 2 * Real.sqrt (z.im * w.im) ≠ 0 := by positivity
  have hc := ((eq_div_iff hk).mp (halfPlane_cosh_half_dist_eq_conjugate_norm_formula z w)).symm
  have hs := ((eq_div_iff hk).mp (halfPlane_sinh_half_dist_eq_norm_formula z w)).symm
  rw [hc, hs, ← sub_mul, Real.cosh_sub_sinh]
  positivity

/-- The logarithmic distance formula in the upper half-plane. -/
theorem halfPlane_dist_eq_log_norm_ratio (z w : ℍ) :
    dist z w = Real.log ((‖(z : ℂ) - conj (w : ℂ)‖ + ‖(z : ℂ) - w‖) /
      (‖(z : ℂ) - conj (w : ℂ)‖ - ‖(z : ℂ) - w‖)) := by
  have hk : 2 * Real.sqrt (z.im * w.im) ≠ 0 := by positivity
  have hc := ((eq_div_iff hk).mp (halfPlane_cosh_half_dist_eq_conjugate_norm_formula z w)).symm
  have hs := ((eq_div_iff hk).mp (halfPlane_sinh_half_dist_eq_norm_formula z w)).symm
  rw [hc, hs, ← add_mul, ← sub_mul, mul_div_mul_right _ _ hk,
    Real.cosh_add_sinh, Real.cosh_sub_sinh, ← Real.exp_sub, Real.log_exp]
  ring

/-- All five expressions are retained together; the curve-length bridge is not assumed. -/
theorem halfPlane_dist_log_cosh_sinh_tanh_formulas (z w : ℍ) :
    (dist z w = Real.log ((‖(z : ℂ) - conj (w : ℂ)‖ + ‖(z : ℂ) - w‖) /
      (‖(z : ℂ) - conj (w : ℂ)‖ - ‖(z : ℂ) - w‖))) ∧
    (Real.cosh (dist z w) = 1 + ‖(z : ℂ) - w‖ ^ 2 / (2 * z.im * w.im)) ∧
    (Real.sinh (dist z w / 2) = ‖(z : ℂ) - w‖ / (2 * Real.sqrt (z.im * w.im))) ∧
    (Real.cosh (dist z w / 2) = ‖(z : ℂ) - conj (w : ℂ)‖ /
      (2 * Real.sqrt (z.im * w.im))) ∧
    (Real.tanh (dist z w / 2) = ‖(z : ℂ) - w‖ / ‖(z : ℂ) - conj (w : ℂ)‖) :=
  ⟨halfPlane_dist_eq_log_norm_ratio z w, halfPlane_cosh_dist_eq_norm_sq_formula z w,
    halfPlane_sinh_half_dist_eq_norm_formula z w, halfPlane_cosh_half_dist_eq_conjugate_norm_formula z w, halfPlane_tanh_half_dist_eq_norm_ratio z w⟩

/-- Points on one vertical line have distance equal to the logarithm of their height ratio. -/
theorem metric_vertical_distance {z w : ℍ} (h : z.re = w.re) :
    dist z w = |Real.log (z.im / w.im)| := by
  rw [UpperHalfPlane.dist_of_re_eq h, Real.dist_eq, Real.log_div z.im_ne_zero w.im_ne_zero]

/-- The distance on the positive imaginary axis is the absolute logarithm of the height ratio. -/
theorem metric_imaginary_axis_distance (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    dist (UpperHalfPlane.mk ⟨0, p⟩ hp) (UpperHalfPlane.mk ⟨0, q⟩ hq) =
      |Real.log (p / q)| :=
  metric_vertical_distance rfl

/-- The metric's topology is definitionally the Euclidean subspace topology on the upper half-plane. -/
theorem metric_topology_eq_induced :
    (inferInstance : MetricSpace ℍ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced UpperHalfPlane.coe (inferInstance : TopologicalSpace ℂ) :=
  rfl

/-- The Euclidean embedding detects the open sets of the actual hyperbolic metric topology. -/
theorem metric_isOpen_iff_image_isOpen (U : Set ℍ) :
    IsOpen U ↔ IsOpen (UpperHalfPlane.coe '' U) :=
  UpperHalfPlane.isOpenEmbedding_coe.isOpen_iff_image_isOpen

/-- Compactness is unchanged by viewing a hyperbolic-plane subset in the complex plane. -/
theorem metric_isCompact_iff_image_isCompact (K : Set ℍ) :
    IsCompact K ↔ IsCompact (UpperHalfPlane.coe '' K) :=
  UpperHalfPlane.isEmbedding_coe.isCompact_iff

end LowDimensionalTopology.Geometry.Hyperbolic
