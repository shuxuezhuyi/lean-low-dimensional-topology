module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCanonicalCoefficientCurve
public import LowDimensionalTopology.Geometry.Teichmuller.CoefficientRealMobiusIsometry
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The actual angular coefficient sums satisfy the original deck tensor law

Right multiplication permutes the genuine projective right cosets. The
existing Mobius phase cocycle identifies the corresponding actual pullbacks,
so reindexing the same raw infinitesimal sum proves its pointwise deck law.
The literal coefficient curve inherits this law from its exact scalar formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

private def rightCosetMulEquiv (Γ : Subgroup Deck) (s : ℝ) (δ : Γ) :
    Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)) ≃
      Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)) where
  toFun := Quotient.map' (fun γ : Γ => γ * δ) (by
    intro a b hab
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using
      (QuotientGroup.rightRel_apply.mp hab))
  invFun := Quotient.map' (fun γ : Γ => γ * δ⁻¹) (by
    intro a b hab
    apply QuotientGroup.rightRel_apply.mpr
    simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using
      (QuotientGroup.rightRel_apply.mp hab))
  left_inv := by
    intro u
    refine Quotient.inductionOn u ?_
    intro γ
    change Quotient.mk _ ((γ * δ) * δ⁻¹) = Quotient.mk _ γ
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  right_inv := by
    intro u
    refine Quotient.inductionOn u ?_
    intro γ
    change Quotient.mk _ ((γ * δ⁻¹) * δ) = Quotient.mk _ γ
    simp only [mul_assoc, inv_mul_cancel, mul_one]

private theorem rightCosetInfinitesimalZeroExtension_mulEquiv
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) (δ : Γ)
    (u : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))) (z : ℍ) :
    rightCosetInfinitesimalZeroExtension θ Γ s (rightCosetMulEquiv Γ s δ u) (z : ℂ) =
      rightCosetInfinitesimalZeroExtension θ Γ s u ((δ.val • z : ℍ) : ℂ) *
        GammaMeasurableBeltrami.phase δ.val z := by
  refine Quotient.inductionOn u ?_
  intro γ
  change pullbackInfinitesimalZeroExtension θ (γ.val * δ.val) (z : ℂ) =
    pullbackInfinitesimalZeroExtension θ γ.val ((δ.val • z : ℍ) : ℂ) *
      GammaMeasurableBeltrami.phase δ.val z
  simp only [pullbackInfinitesimalZeroExtension_coe, mul_smul,
    GammaMeasurableBeltrami.phase_mul, mul_assoc]

/-- The same raw infinitesimal sum satisfies the actual tensor law at every
upper-half-plane point, including the angular boundary rays. -/
theorem rightCosetInfinitesimalSum_deck
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) (δ : Γ) (z : ℍ) :
    (∑' u : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
      rightCosetInfinitesimalZeroExtension θ Γ s u (z : ℂ)) =
      (∑' u : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
        rightCosetInfinitesimalZeroExtension θ Γ s u ((δ.val • z : ℍ) : ℂ)) *
          GammaMeasurableBeltrami.phase δ.val z := by
  let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
  let e : C ≃ C := rightCosetMulEquiv Γ s δ
  calc
    (∑' u : C, rightCosetInfinitesimalZeroExtension θ Γ s u (z : ℂ)) =
        ∑' u : C, rightCosetInfinitesimalZeroExtension θ Γ s (e u) (z : ℂ) :=
      (e.tsum_eq (fun u : C => rightCosetInfinitesimalZeroExtension θ Γ s u (z : ℂ))).symm
    _ = ∑' u : C,
        rightCosetInfinitesimalZeroExtension θ Γ s u ((δ.val • z : ℍ) : ℂ) *
          GammaMeasurableBeltrami.phase δ.val z := by
      apply tsum_congr
      intro u
      exact rightCosetInfinitesimalZeroExtension_mulEquiv θ Γ s δ u z
    _ = _ := tsum_mul_right

/-- The original raw infinitesimal coefficient is genuinely Gamma-compatible.
No countability, summability or one-support premise is required for this law. -/
theorem isGammaCompatible_rightCosetInfinitesimalSum
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) :
    LiZhongQC.IsGammaCompatible Γ
      (fun ζ : ℂ =>
        ∑' u : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
          rightCosetInfinitesimalZeroExtension θ Γ s u ζ) := by
  intro δ hδ
  apply GammaMeasurableBeltrami.ae_plane_iff.mpr
  exact Filter.Eventually.of_forall fun z : ℍ => by
    simpa only [LiZhongQC.h23l_b_coe_smul, LiZhongQC.mobiusFn,
      GammaMeasurableBeltrami.phase, GammaMeasurableBeltrami.denominator] using
      rightCosetInfinitesimalSum_deck θ Γ s ⟨δ, hδ⟩ z

/-- For every real parameter the literal coefficient sum satisfies that same
Gamma tensor law, before any marked-surface interpretation. -/
theorem isGammaCompatible_rightCosetCoefficientSum
    (θ : Width) (Γ : Subgroup Deck) (s t : ℝ) :
    LiZhongQC.IsGammaCompatible Γ (rightCosetCoefficientSum θ Γ s t) := by
  intro δ hδ
  filter_upwards [isGammaCompatible_rightCosetInfinitesimalSum θ Γ s δ hδ] with ζ hζ
  simp only [rightCosetCoefficientSum_eq_scalar]
  rw [hζ, mul_assoc]

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
