module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedAutomorphicCoefficientSpace
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton

/-!
# Measurable automorphic quadratic forms before weighted boundedness

Measurability uses Euclidean area on the original upper half-plane, including
its completion. The transformation law is pointwise. No weighted bound,
holomorphy, compact quotient or fundamental region is part of the predicate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadratic

open GammaMeasurableBeltrami

/-- A measurable automorphic quadratic form, with no boundedness restriction. -/
def IsAutomorphic (Γ : Subgroup Deck) (f : ℍ → ℂ) : Prop :=
  AEStronglyMeasurable f flatMeasure ∧
    ∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) / denominator γ z ^ 4 = f z

/-- The transformation law uses the actual complex derivative of the same
Möbius transformation at every original point. -/
theorem IsAutomorphic.derivative_law {Γ : Subgroup Deck} {f : ℍ → ℂ}
    (hf : IsAutomorphic Γ f) (γ : Deck) (hγ : γ ∈ Γ) (z : ℍ) :
    f (γ • z) * deriv (LiZhongQC.h36p_m γ) (z : ℂ) ^ 2 = f z := by
  rw [(LiZhongQC.h36p_m_hasDerivAt γ z.im_pos).deriv]
  simpa only [denominator, div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow, ← pow_mul] using hf.2 γ hγ z

/-- With a weighted bound supplied separately, the same original function has
its actual weighted coefficient class and exact essential norm. -/
theorem IsAutomorphic.exists_weighted_class {Γ : Subgroup Deck} {f : ℍ → ℂ}
    (hf : IsAutomorphic Γ f)
    (hb : ∃ M : ℝ, ∀ᵐ z ∂flatMeasure, ‖f z‖ * z.im ^ 2 ≤ M) :
    ∃ g : WeightedAutomorphicCoefficient.Space Γ,
      g.val =ᵐ[flatMeasure] weightedValue f ∧ ‖g‖ = weightedEssNorm f := by
  exact ⟨WeightedAutomorphicCoefficient.ofRaw f hf.1 hf.2 hb,
    WeightedAutomorphicCoefficient.ofRaw_coe_ae_flat f hf.1 hf.2 hb,
    WeightedAutomorphicCoefficient.norm_ofRaw f hf.1 hf.2 hb⟩

end LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadratic
