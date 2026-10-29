module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientPullback

/-!
# Actual coefficient translations between the original and deformed groups

The deformed group is the genuine conjugate by the normalized solution of
an original coefficient. Its two conjugacy laws prove that actual translated
and pulled-back coefficients satisfy the respective native deck laws. Thus
both nonlinear maps take values in the existing closed compatible spaces,
with the original essential norms unchanged.

The normalized conjugacy and coefficient compatibility proofs reuse Wu
Xiaobin's LiZhongQC source, Apache-2.0, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The actual normalized conjugate Fuchsian group. -/
def deformedGroup (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) : Subgroup Deck :=
  Classical.choose (LiZhongQC.exists_deformation_group hΓ (toSourceGamma ν))

theorem deformedGroup_spec (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    LiZhongQC.IsFuchsian (deformedGroup hΓ ν) ∧
      (∀ γ ∈ Γ, ∃ γ' ∈ deformedGroup hΓ ν, ∀ z ∈ LiZhongQC.upperHalf,
        normalizedMap ν (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
          LiZhongQC.mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (normalizedMap ν z)) ∧
      ∀ γ' ∈ deformedGroup hΓ ν, ∃ γ ∈ Γ, ∀ z ∈ LiZhongQC.upperHalf,
        normalizedMap ν (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
          LiZhongQC.mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (normalizedMap ν z) :=
  Classical.choose_spec (LiZhongQC.exists_deformation_group hΓ (toSourceGamma ν))

/-- The literal translated source coefficient obeys the actual deformed group law. -/
theorem translatedSource_compatible (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    LiZhongQC.IsGammaCompatible (deformedGroup hΓ ν)
      (LiZhongQC.b33_t_tb (toSourceGamma ν).val (toSourceGamma μ).val).val := by
  intro γ' hγ'
  obtain ⟨γ, hγ, hrel⟩ := (deformedGroup_spec hΓ ν).2.2 γ' hγ'
  obtain ⟨A, hA⟩ := LiZhongQC.b33_d_def (toSourceGamma μ) hγ
  obtain ⟨K, hK, _, _, _, _⟩ :=
    LiZhongQC.b33_t_tb_comp_spec (toSourceGamma ν).val (toSourceGamma μ).val
  obtain ⟨_, _, hleft, hright, _⟩ := normalizedInverse_spec ν
  have hHU : ∀ z ∈ LiZhongQC.upperHalf,
      (normalizedMap μ ∘ normalizedInverse ν) z ∈ LiZhongQC.upperHalf := by
    intro z hz
    exact normalizedMap_mapsTo_upper μ (normalizedInverse_mapsTo_upper ν hz)
  apply LiZhongQC.b33_t_compat_of_conj hK hHU (A := A)
  intro z hz
  have hw := normalizedInverse_mapsTo_upper ν hz
  have he : normalizedInverse ν
      (LiZhongQC.mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) z) =
        LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (normalizedInverse ν z) := by
    have hh := congrArg (normalizedInverse ν) (hrel (normalizedInverse ν z) hw)
    rw [hleft, hright] at hh
    exact hh.symm
  change normalizedMap μ
      (normalizedInverse ν (LiZhongQC.mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) z)) =
    LiZhongQC.mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1)
      (normalizedMap μ (normalizedInverse ν z))
  rw [he]
  exact hA _ hw

/-- The actual translated source element, with its compatibility proved. -/
def translatedSource (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    LiZhongQC.BeltramiGamma (deformedGroup hΓ ν) :=
  ⟨LiZhongQC.b33_t_tb (toSourceGamma ν).val (toSourceGamma μ).val,
    translatedSource_compatible hΓ ν μ⟩

/-- The actual inverse composition coefficient obeys the original group law. -/
theorem pulledBackSource_compatible (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Ball (deformedGroup hΓ ν)) :
    LiZhongQC.IsGammaCompatible Γ
      (LiZhongQC.b33_t_pb (toSourceGamma ν).val (toSourceGamma κ).val).val := by
  apply LiZhongQC.b33_t_pb_compat (toSourceGamma ν).val (toSourceGamma κ).val
    (deformedGroup_spec hΓ ν).2.1
  intro γ' hγ'
  exact LiZhongQC.b33_d_def (toSourceGamma κ) hγ'

/-- The actual pulled-back source element, with its compatibility proved. -/
def pulledBackSource (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Ball (deformedGroup hΓ ν)) : LiZhongQC.BeltramiGamma Γ :=
  ⟨LiZhongQC.b33_t_pb (toSourceGamma ν).val (toSourceGamma κ).val,
    pulledBackSource_compatible hΓ ν κ⟩

/-- The ambient translation has the genuine deformed compatible class on every input ball. -/
theorem translation_mem_compatible_ball (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ) :
    translation ν μ.val.val ∈ compatibleSubmodule (deformedGroup hΓ ν) := by
  have he : translation ν μ.val.val = sourceAmbient (translatedSource hΓ ν μ).val := by
    apply Lp.ext
    filter_upwards [translation_eq_actual_composite_ae ν μ,
      sourceAmbient_coe_ae (translatedSource hΓ ν μ).val] with z ht hs
    exact ht.trans hs.symm
  rw [he]
  exact sourceAmbient_mem_compatible (translatedSource hΓ ν μ)

/-- Every value of the zero-extended translation is still deformed compatible. -/
theorem translation_mem_compatible (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (μ : Space Γ) : translation ν μ.val ∈ compatibleSubmodule (deformedGroup hΓ ν) := by
  classical
  by_cases hμ : ‖μ.val‖ < 1
  · exact translation_mem_compatible_ball hΓ ν
      ⟨μ, by
        rw [Metric.mem_ball, dist_zero_right, ← ClosedSubmodule.norm_coe]
        exact hμ⟩
  · rw [translation, dite_eq_right hμ]
    exact (compatibleSubmodule _).zero_mem

/-- Every actual pulled-back class is originally compatible, including the extension. -/
theorem pullback_mem_compatible (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Space (deformedGroup hΓ ν)) : pullback ν κ.val ∈ compatibleSubmodule Γ := by
  classical
  by_cases hκ : ‖κ.val‖ < 1
  · let κB : Ball (deformedGroup hΓ ν) :=
      ⟨κ, by
        rw [Metric.mem_ball, dist_zero_right, ← ClosedSubmodule.norm_coe]
        exact hκ⟩
    rw [pullback, dite_eq_left hκ]
    exact sourceAmbient_mem_compatible (pulledBackSource hΓ ν κB)
  · rw [pullback, dite_eq_right hκ]
    exact ν.val.property

/-- The actual normalized coefficient translation with its exact compatible codomain. -/
def gammaTranslation (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) (μ : Space Γ) :
    Space (deformedGroup hΓ ν) :=
  ⟨translation ν μ.val, translation_mem_compatible hΓ ν μ⟩

@[simp] theorem gammaTranslation_val (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (μ : Space Γ) : (gammaTranslation hΓ ν μ).val = translation ν μ.val := rfl

/-- The actual inverse normalized composition with its exact original codomain. -/
def gammaPullback (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Space (deformedGroup hΓ ν)) : Space Γ :=
  ⟨pullback ν κ.val, pullback_mem_compatible hΓ ν κ⟩

@[simp] theorem gammaPullback_val (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Space (deformedGroup hΓ ν)) : (gammaPullback hΓ ν κ).val = pullback ν κ.val := rfl

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
