module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Real Möbius changes of the genuine compatible coefficient spaces

The operator is the already existing hyperbolic L-infinity linear isometry:
actual measure-preserving deck composition and its literal unit Beltrami phase.
The denominator cocycle proves its contravariant composition law. The exact
matrix conjugate group's compatibility equations then give a genuine complex
linear isometric equivalence on all native vectors and on their entire unit
balls. No range condition or coefficient-transport operator is assumed.

The coefficient convention and normalized source groups use Wu Xiaobin's
Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0).
See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

/-- The actual real Möbius denominator cocycle in the existing upper-half-plane action. -/
theorem denominator_mul (A B : Deck) (z : ℍ) :
    denominator (A * B) z = denominator A (B • z) * denominator B z := by
  have h := UpperHalfPlane.denom_cocycle
    (Matrix.SpecialLinearGroup.mapGL ℝ A) (Matrix.SpecialLinearGroup.mapGL ℝ B) z.im_ne_zero
  change denominator (A * B) z =
    ((A 1 0 : ℂ) * LiZhongQC.utm_b_mob B z + A 1 1) * denominator B z at h
  rw [LiZhongQC.utm_b_mob_coe] at h
  exact h

/-- The genuine Beltrami phases have the same cocycle as the derivatives. -/
theorem phase_mul (A B : Deck) (z : ℍ) :
    phase (A * B) z = phase A (B • z) * phase B z := by
  simp only [phase, denominator_mul, mul_pow, map_mul, mul_div_mul_comm]

theorem phase_one (z : ℍ) : phase 1 z = 1 := by
  simp [phase, denominator]

/-- The actual weighted deck operators compose in the contravariant order. -/
theorem pullback_comp (A B : Deck) (μ : Ambient) :
    pullback A (pullback B μ) = pullback (B * A) μ := by
  apply Lp.ext
  filter_upwards [pullback_coe_ae A (pullback B μ),
    (measurePreserving_deck A).quasiMeasurePreserving.ae (pullback_coe_ae B μ),
    pullback_coe_ae (B * A) μ] with z hA hB hBA
  rw [hA, hB, hBA, phase_mul, mul_smul]
  ring

/-- Pullback by the identity preserves the actual a.e. class. -/
theorem pullback_one (μ : Ambient) : pullback 1 μ = μ := by
  apply Lp.ext
  filter_upwards [pullback_coe_ae 1 μ] with z hz
  simpa only [phase_one, one_smul, one_mul] using hz

/-- The actual inverse matrix is the true inverse on the whole ambient Banach space. -/
theorem pullback_inv (M : Deck) (μ : Ambient) : pullback M⁻¹ (pullback M μ) = μ := by
  rw [pullback_comp, mul_inv_cancel, pullback_one]

/-- Every equation for the actual conjugate group gives the original deck law after pullback. -/
theorem pullback_mem_original (Γ : Subgroup Deck) (M : Deck)
    (μ : Space (LiZhongQC.conjGroup Γ M)) : pullback M μ.val ∈ compatibleSubmodule Γ := by
  intro γ hγ
  let δ : Deck := M * γ * M⁻¹
  have hδ : δ ∈ LiZhongQC.conjGroup Γ M := Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩
  have hfix : pullback δ μ.val = μ.val :=
    (show ∀ δ ∈ LiZhongQC.conjGroup Γ M, pullback δ μ.val = μ.val from μ.property) δ hδ
  calc
    pullback γ (pullback M μ.val) = pullback (M * γ) μ.val := pullback_comp γ M μ.val
    _ = pullback (δ * M) μ.val := by simp [δ, mul_assoc]
    _ = pullback M (pullback δ μ.val) := (pullback_comp M δ μ.val).symm
    _ = pullback M μ.val := congrArg (pullback M) hfix

/-- Pullback by the inverse matrix proves every actual conjugate compatibility equation. -/
theorem pullback_inv_mem_conjugate (Γ : Subgroup Deck) (M : Deck) (μ : Space Γ) :
    pullback M⁻¹ μ.val ∈ compatibleSubmodule (LiZhongQC.conjGroup Γ M) := by
  intro δ hδ
  obtain ⟨γ, hγ, hγδ⟩ := Subgroup.mem_map.mp hδ
  have hfix : pullback γ μ.val = μ.val :=
    (show ∀ γ ∈ Γ, pullback γ μ.val = μ.val from μ.property) γ hγ
  calc
    pullback δ (pullback M⁻¹ μ.val) = pullback (M⁻¹ * δ) μ.val := pullback_comp δ M⁻¹ μ.val
    _ = pullback (γ * M⁻¹) μ.val := by
      rw [← hγδ]
      simp [MulAut.conj_apply, mul_assoc]
    _ = pullback M⁻¹ (pullback γ μ.val) := (pullback_comp M⁻¹ γ μ.val).symm
    _ = pullback M⁻¹ μ.val := congrArg (pullback M⁻¹) hfix

/-- Restrict the existing, unchanged ambient linear isometry to the actual compatible spaces. -/
def coefficientMobiusPullback (Γ : Subgroup Deck) (M : Deck) :
    Space (LiZhongQC.conjGroup Γ M) →ₗᵢ[ℂ] Space Γ :=
  { (((pullback M).domRestrict (compatibleSubmodule (LiZhongQC.conjGroup Γ M))).codRestrict
      (compatibleSubmodule Γ) (pullback_mem_original Γ M)).toLinearMap with
    norm_map' := fun μ => by
      change ‖pullback M μ.val‖ = ‖μ.val‖
      exact norm_pullback M μ.val }

@[simp] theorem coefficientMobiusPullback_val (Γ : Subgroup Deck) (M : Deck)
    (μ : Space (LiZhongQC.conjGroup Γ M)) :
    (coefficientMobiusPullback Γ M μ).val = pullback M μ.val := rfl

theorem coefficientMobiusPullback_surjective (Γ : Subgroup Deck) (M : Deck) :
    Function.Surjective (coefficientMobiusPullback Γ M) := by
  intro μ
  let κ : Space (LiZhongQC.conjGroup Γ M) :=
    ⟨pullback M⁻¹ μ.val, pullback_inv_mem_conjugate Γ M μ⟩
  refine ⟨κ, ?_⟩
  apply Subtype.ext
  change pullback M (pullback M⁻¹ μ.val) = μ.val
  simpa only [inv_inv] using pullback_inv M⁻¹ μ.val

/-- The genuine coefficient-space isometry for the exact matrix conjugate group, on ALL vectors. -/
def coefficientRealMobiusIsometry (Γ : Subgroup Deck) (M : Deck) :
    Space (LiZhongQC.conjGroup Γ M) ≃ₗᵢ[ℂ] Space Γ :=
  LinearIsometryEquiv.ofSurjective (coefficientMobiusPullback Γ M)
    (coefficientMobiusPullback_surjective Γ M)

@[simp] theorem coefficientRealMobiusIsometry_val (Γ : Subgroup Deck) (M : Deck)
    (μ : Space (LiZhongQC.conjGroup Γ M)) :
    (coefficientRealMobiusIsometry Γ M μ).val = pullback M μ.val := rfl

/-- The full coefficient transport retains the literal unit-phase formula almost everywhere. -/
theorem coefficientRealMobiusIsometry_coe_ae (Γ : Subgroup Deck) (M : Deck)
    (μ : Space (LiZhongQC.conjGroup Γ M)) :
    (coefficientRealMobiusIsometry Γ M μ).val =ᵐ[volume]
      fun z : ℍ => phase M z * μ.val (M • z) :=
  pullback_coe_ae M μ.val

/-- The inverse equivalence is exactly the inverse matrix's actual weighted pullback. -/
theorem coefficientRealMobiusIsometry_symm_val (Γ : Subgroup Deck) (M : Deck) (μ : Space Γ) :
    ((coefficientRealMobiusIsometry Γ M).symm μ).val = pullback M⁻¹ μ.val := by
  have h := congrArg (fun κ : Space Γ => κ.val)
    ((coefficientRealMobiusIsometry Γ M).apply_symm_apply μ)
  rw [coefficientRealMobiusIsometry_val] at h
  have hi := congrArg (pullback M⁻¹) h
  rw [pullback_inv] at hi
  exact hi

/-- The actual inverse also has its literal, representative-independent phase formula. -/
theorem coefficientRealMobiusIsometry_symm_coe_ae (Γ : Subgroup Deck) (M : Deck) (μ : Space Γ) :
    ((coefficientRealMobiusIsometry Γ M).symm μ).val =ᵐ[volume]
      fun z : ℍ => phase M⁻¹ z * μ.val (M⁻¹ • z) := by
  rw [coefficientRealMobiusIsometry_symm_val]
  exact pullback_coe_ae M⁻¹ μ.val

/-- The norm-preserving coefficient equivalence restricts to a bijection of the ENTIRE unit balls. -/
def coefficientRealMobiusBallEquiv (Γ : Subgroup Deck) (M : Deck) :
    Ball (LiZhongQC.conjGroup Γ M) ≃ Ball Γ where
  toFun μ := ⟨coefficientRealMobiusIsometry Γ M μ.val, by
    rw [Metric.mem_ball, dist_zero_right, (coefficientRealMobiusIsometry Γ M).norm_map]
    exact Ball.norm_lt_one μ⟩
  invFun μ := ⟨(coefficientRealMobiusIsometry Γ M).symm μ.val, by
    rw [Metric.mem_ball, dist_zero_right, (coefficientRealMobiusIsometry Γ M).symm.norm_map]
    exact Ball.norm_lt_one μ⟩
  left_inv μ := by
    apply Subtype.ext
    exact (coefficientRealMobiusIsometry Γ M).symm_apply_apply μ.val
  right_inv μ := by
    apply Subtype.ext
    exact (coefficientRealMobiusIsometry Γ M).apply_symm_apply μ.val

@[simp] theorem coefficientRealMobiusBallEquiv_val (Γ : Subgroup Deck) (M : Deck)
    (μ : Ball (LiZhongQC.conjGroup Γ M)) :
    (coefficientRealMobiusBallEquiv Γ M μ).val = coefficientRealMobiusIsometry Γ M μ.val := rfl

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
