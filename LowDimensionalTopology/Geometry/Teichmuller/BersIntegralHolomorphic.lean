module

public import LowDimensionalTopology.Geometry.Teichmuller.BersIntegralOperator

/-!
# Holomorphy of the actual bounded-coefficient Bers integral

The absolutely convergent third-kernel integral is holomorphic on the lower
half-plane. Its derivative is three times the fourth-kernel integral, so the
actual Bers integral is a constant multiple of that holomorphic derivative.
No subunit restriction, chosen terminal differential or assumed image property
is required.

Differentiation of the third-kernel integral uses Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0);
see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open LiZhongQC

/-- Every genuinely bounded measurable input has a holomorphic fourth-kernel
Bers variation on the full lower half-plane. -/
theorem bersDerivative_differentiableOn_of_bounded {κ : ℂ → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hm : AEStronglyMeasurable κ (volume.restrict upperHalf))
    (hb : ∀ᵐ ζ ∂(volume.restrict upperHalf), ‖κ ζ‖ ≤ M) :
    DifferentiableOn ℂ (bersDerivative κ) lowerHalf := by
  let H : ℂ → ℂ := fun w => ∫ ζ in upperHalf, κ ζ / (ζ - w) ^ 3
  have hd (w : ℂ) (hw : w ∈ lowerHalf) :
      HasDerivAt H (3 * ∫ ζ in upperHalf, κ ζ / (ζ - w) ^ 4) w :=
    b36_p_hasDerivAt_H3 hM hm hb hw
  have hH : DifferentiableOn ℂ H lowerHalf := fun w hw =>
    (hd w hw).differentiableAt.differentiableWithinAt
  apply ((hH.deriv isOpen_lowerHalf).const_mul (-(2 / Real.pi : ℂ))).congr
  intro w hw
  rw [(hd w hw).deriv, bersDerivative]
  ring

/-- In particular the actual integral variation of every original compatible
L-infinity class is holomorphic, without any bound on its norm. -/
theorem integralOperator_raw_differentiableOn
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (μ : GammaMeasurableBeltrami.Space Γ) :
    DifferentiableOn ℂ
      (bersDerivative (GammaMeasurableBeltrami.planeRepresentative μ.val)) lowerHalf :=
  bersDerivative_differentiableOn_of_bounded (norm_nonneg μ)
    (GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val).1
    (GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val).2

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
