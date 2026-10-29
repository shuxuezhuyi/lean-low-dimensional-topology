module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealCauchyKernel
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The removable paired kernel in the real-line Riesz proof

Pairing the positive and negative real half-lines gives `(φ(ξ+x)-φ(ξ-x))/x`. Its apparent pole at zero
is removable for C1 tests. Mathlib's actual `dslope` supplies that removable
value, without assuming existence of any principal value or Riesz bound.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The paired quotient with its actual derivative value at the origin. -/
def realHilbertPairedKernel (φ : ℝ → ℂ) (ξ x : ℝ) : ℂ :=
  dslope φ ξ (ξ + x) + dslope φ ξ (ξ - x)

/-- Away from zero this is exactly the positive-sign paired kernel in the book. -/
theorem realHilbertPairedKernel_of_ne (φ : ℝ → ℂ) (ξ : ℝ) {x : ℝ} (hx : x ≠ 0) :
    realHilbertPairedKernel φ ξ x = x⁻¹ • (φ (ξ + x) - φ (ξ - x)) := by
  have hp : ξ + x ≠ ξ := by intro h; apply hx; linarith
  have hm : ξ - x ≠ ξ := by intro h; apply hx; linarith
  rw [realHilbertPairedKernel, dslope_of_ne φ hp, dslope_of_ne φ hm,
    slope_def_module, slope_def_module]
  have hsub : ξ - x - ξ = -x := by ring
  rw [add_sub_cancel_left, hsub, inv_neg, neg_smul, ← sub_eq_add_neg, ← smul_sub]
  congr 1
  abel

/-- The removable value is twice the original derivative. -/
theorem realHilbertPairedKernel_zero (φ : ℝ → ℂ) (ξ : ℝ) :
    realHilbertPairedKernel φ ξ 0 = 2 • deriv φ ξ := by
  simp [realHilbertPairedKernel, two_smul]

/-- Actual C1 regularity makes the paired kernel continuous at its apparent pole. -/
theorem continuous_realHilbertPairedKernel {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (ξ : ℝ) :
    Continuous (realHilbertPairedKernel φ ξ) := by
  have hd : DifferentiableAt ℝ φ ξ := hφ.differentiable (by norm_num) ξ
  have hds : Continuous (dslope φ ξ) := by
    apply continuous_iff_continuousAt.2
    intro y
    rcases eq_or_ne y ξ with rfl | hne
    · exact continuousAt_dslope_same.2 hd
    · exact (continuousAt_dslope_of_ne hne).2 hφ.continuous.continuousAt
  exact (hds.comp (continuous_const.add continuous_id)).add
    (hds.comp (continuous_const.sub continuous_id))

/-- Pairing cancels the two noncompact constant tails of the individual slopes. -/
theorem hasCompactSupport_realHilbertPairedKernel {φ : ℝ → ℂ}
    (hcompact : HasCompactSupport φ) (ξ : ℝ) :
    HasCompactSupport (realHilbertPairedKernel φ ξ) := by
  obtain ⟨R, hR, hbound⟩ := hcompact.isCompact.isBounded.exists_pos_norm_le
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (R + |ξ| + 1))
  intro x hx
  have hxlt : R + |ξ| + 1 < |x| := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, abs_zero] at hxlt
    linarith [abs_nonneg ξ]
  have hp : φ (ξ + x) = 0 := by
    by_contra h
    have hb := hbound (ξ + x) (subset_tsupport φ h)
    simp only [Real.norm_eq_abs] at hb
    have ht : |x| ≤ |ξ + x| + |ξ| := by
      calc
        |x| = |(ξ + x) - ξ| := by congr 1; ring
        _ ≤ |ξ + x| + |ξ| := abs_sub _ _
    linarith
  have hm : φ (ξ - x) = 0 := by
    by_contra h
    have hb := hbound (ξ - x) (subset_tsupport φ h)
    simp only [Real.norm_eq_abs] at hb
    have ht : |x| ≤ |ξ| + |ξ - x| := by
      calc
        |x| = |ξ - (ξ - x)| := by congr 1; ring
        _ ≤ |ξ| + |ξ - x| := abs_sub _ _
    linarith
  rw [realHilbertPairedKernel_of_ne φ ξ hx0, hp, hm, sub_self, smul_zero]

/-- The actual paired integrand is absolutely integrable; its existence is
derived solely from the original compact C1 test assumptions. -/
theorem integrable_realHilbertPairedKernel {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) (ξ : ℝ) :
    Integrable (realHilbertPairedKernel φ ξ) :=
  (continuous_realHilbertPairedKernel hφ ξ).integrable_of_hasCompactSupport
    (hasCompactSupport_realHilbertPairedKernel hcompact ξ)

end LowDimensionalTopology.Geometry.Quasiconformal
