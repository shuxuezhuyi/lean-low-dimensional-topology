module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCoefficientGammaCompatibility
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchySeriesIntegral
public import LowDimensionalTopology.Geometry.Teichmuller.GammaCoefficientEncoding

/-!
# The complete angular infinitesimal as a genuine compatible coefficient class

The literal sum runs over the actual projective right cosets. Its proved
one-support bound and deck tensor law encode that same entire function in
the compatible L-infinity space, with no quasiconformal subunit restriction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The entire raw infinitesimal coefficient, rather than one coset term. -/
def rightCosetInfinitesimalSum (θ : Width) (Γ : Subgroup Deck) (s : ℝ)
    (ζ : ℂ) : ℂ :=
  ∑' u : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
    rightCosetInfinitesimalZeroExtension θ Γ s u ζ

/-- The same whole coefficient defines an actual compatible Banach-space
direction with its original bound, which may be greater than one. -/
theorem exists_rightCosetInfinitesimalSum_native
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) [Countable Γ]
    (hsep : ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
        rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0 →
        rightCosetInfinitesimalZeroExtension θ Γ s v ζ ≠ 0 → u = v) :
    ∃ ν : GammaMeasurableBeltrami.Space Γ,
      (ν.val : ℍ → ℂ) =ᵐ[volume]
        (fun z : ℍ => rightCosetInfinitesimalSum θ Γ s (z : ℂ)) ∧
      ‖ν‖ ≤ 1 / (4 * (θ : ℝ)) := by
  obtain ⟨hm, hb, _⟩ := rightCosetCauchySeries_hasSum θ Γ s hsep
  have hμ : LiZhongQC.IsBeltramiCoeff (rightCosetInfinitesimalSum θ Γ s)
      LiZhongQC.upperHalf (1 / (4 * (θ : ℝ))) :=
    ⟨hm.aestronglyMeasurable.restrict, Filter.Eventually.of_forall hb⟩
  have hΓ : LiZhongQC.IsGammaCompatible Γ (rightCosetInfinitesimalSum θ Γ s) :=
    isGammaCompatible_rightCosetInfinitesimalSum θ Γ s
  refine ⟨GammaMeasurableBeltrami.ofCoefficient hμ hΓ,
    GammaMeasurableBeltrami.ofCoefficient_coe_ae hμ hΓ, ?_⟩
  exact GammaMeasurableBeltrami.norm_ofCoefficient_le
    (one_div_nonneg.mpr (mul_nonneg (by norm_num) θ.property.1.le)) hμ hΓ

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
