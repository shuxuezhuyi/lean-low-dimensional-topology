module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertGreenLimit
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertPrincipalValue

/-!
# The smooth compact-test potential formula for the circular transform

Both genuine radial limits identify the original directional average with
the Wirtinger derivative of the inverse-norm potential. This formula also
gives smoothness of the noncompact intermediate function.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The directional circular transform has the literal inverse-norm
potential formula on every original smooth compact test. -/
theorem circularHilbertTransform_eq_inverseNormPotential_dz {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) (z : ℂ) :
    circularHilbertTransform φ z =
      (1 / (Real.pi : ℂ)) * inverseNormPotential (LiZhongQC.dz φ) z :=
  tendsto_nhds_unique (hasCircularHilbertPrincipalValue hφ hc z)
    (tendsto_circularHilbertTruncation_inverseNormPotential hφ hc z)

/-- Equivalently, the test derivative can be transferred to the potential. -/
theorem circularHilbertTransform_eq_dz_inverseNormPotential {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) (z : ℂ) :
    circularHilbertTransform φ z =
      (1 / (Real.pi : ℂ)) * LiZhongQC.dz (inverseNormPotential φ) z := by
  rw [dz_inverseNormPotential (hφ.of_le (by simp)) hc]
  exact circularHilbertTransform_eq_inverseNormPotential_dz hφ hc z

/-- Subtracting the fixed reference value leaves the same derivative formula. -/
theorem circularHilbertTransform_eq_dz_renormalizedInverseNormPotential {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) (z : ℂ) :
    circularHilbertTransform φ z =
      (1 / (Real.pi : ℂ)) * LiZhongQC.dz (renormalizedInverseNormPotential φ) z := by
  rw [dz_renormalizedInverseNormPotential (hφ.of_le (by simp)) hc]
  exact circularHilbertTransform_eq_dz_inverseNormPotential hφ hc z

/-- The actual circular transform of a compact smooth test is smooth, even
though its output need not have compact support. -/
theorem contDiff_circularHilbertTransform {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (circularHilbertTransform φ) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (inverseNormPotential (LiZhongQC.dz φ)) :=
    (LiZhongQC.dz_hasCompactSupport hc).contDiff_convolution_right _
      locallyIntegrable_inverseNormKernel (LiZhongQC.dz_contDiff hφ)
  have heq : circularHilbertTransform φ =
      fun z => (1 / (Real.pi : ℂ)) * inverseNormPotential (LiZhongQC.dz φ) z := by
    funext z
    exact circularHilbertTransform_eq_inverseNormPotential_dz hφ hc z
  rw [heq]
  exact contDiff_const.mul hs

end LowDimensionalTopology.Geometry.Quasiconformal
