module

public import LowDimensionalTopology.External.LiZhongQC.Basic

/-!
# Regularity of an existing smooth-coefficient Beltrami solution

This concrete proposition isolates real C1-to-C∞ elliptic regularity for the
same actual plane function. Importing its definition supplies no proof.
The compact smooth coefficient and its bound are actual pointwise data.
Existence, a homeomorphism, positive Jacobian and inverse smoothness are
proved separately in the explicit conditional consumer.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Quasiconformal

/-- An existing real C1 solution for a smooth compact Beltrami coefficient
with a strict uniform bound is real C∞, without changing that solution. -/
def SmoothCompactBeltramiRegularity : Prop :=
  ∀ (μ f : ℂ → ℂ) (k : ℝ),
    k < 1 →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ →
    HasCompactSupport μ →
    (∀ z, ‖μ z‖ ≤ k) →
    ContDiff ℝ 1 f →
    (∀ z, LiZhongQC.dzbar f z = μ z * LiZhongQC.dz f z) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f

end LowDimensionalTopology.Unproved.Quasiconformal
