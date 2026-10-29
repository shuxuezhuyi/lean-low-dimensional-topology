module

public import LowDimensionalTopology.Geometry.Teichmuller.BersTranslationRecentring
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslationGlobalAnalytic
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# The genuine derivative of the normalized recentering cocycle

The whole-image nonlinear identity is differentiated on the actual open Bers
image. The two target automorphic subspaces are included in their unchanged
common weighted target; their chosen SL lift groups are not identified.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν μ : Ball Γ)

local notation "Δ" => deformedGroup hΓ ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "κ" => translatedBall hΓ ν μ
local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν

/-- The genuine first translation sends the actual source centre to the
actual centre for the recentered translation. -/
theorem bersTranslation_recentring_center :
    bersTranslation hΓ ν (baseBersValue hΓ μ) = baseBersValue hΔ κ :=
  bersTranslation_automorphicProjection hΓ ν μ

/-- Chain rule for the exact nonlinear cocycle, in the common original
weighted target. Both centred derivatives are the already proved genuine
inverse-coordinate derivatives. -/
theorem bersTranslation_recentring_fderiv :
    ((BersWeighted.automorphicSubmodule (deformedGroup hΔ κ)).subtypeL.comp
      (inverseBersDerivativeEquiv Y hpY hg hY hΔ κ).symm.toContinuousLinearMap).comp
        (fderiv ℂ (bersTranslation hΓ ν) (baseBersValue hΓ μ)) =
      (BersWeighted.automorphicSubmodule (deformedGroup hΓ μ)).subtypeL.comp
        (inverseBersDerivativeEquiv R hp hg hgenus hΓ μ).symm.toContinuousLinearMap := by
  let b := baseBersValue hΓ μ
  have hν :=
    (differentiableAt_bersTranslation_everyCoefficient R hp hg hgenus hΓ ν μ).hasFDerivAt
  have hκ : HasFDerivAt (bersTranslation hΔ κ)
      (inverseBersDerivativeEquiv Y hpY hg hY hΔ κ).symm.toContinuousLinearMap
      (bersTranslation hΓ ν b) := by
    rw [bersTranslation_recentring_center hΓ ν μ]
    exact hasFDerivAt_bersTranslation Y hpY hg hY hΔ κ
  have hleft :=
    (((BersWeighted.automorphicSubmodule (deformedGroup hΔ κ)).subtypeL.hasFDerivAt).comp
      (bersTranslation hΓ ν b) hκ).comp b hν
  have hright :=
    ((BersWeighted.automorphicSubmodule (deformedGroup hΓ μ)).subtypeL.hasFDerivAt).comp b
      (hasFDerivAt_bersTranslation R hp hg hgenus hΓ μ)
  have hmem : b ∈ coefficientBersImage hΓ :=
    (mem_coefficientBersImage_iff_coefficient hΓ b).mpr ⟨μ, rfl⟩
  have heq :
      (fun φ : BersWeighted.Automorphic Γ =>
        (bersTranslation hΔ κ (bersTranslation hΓ ν φ)).val) =ᶠ[𝓝 b]
      (fun φ : BersWeighted.Automorphic Γ => (bersTranslation hΓ μ φ).val) := by
    filter_upwards [(isOpen_coefficientBersImage R hp hg hgenus hΓ).mem_nhds hmem]
      with φ hφ
    exact bersTranslation_translatedBall_recentring hΓ ν μ φ hφ
  exact (hleft.congr_of_eventuallyEq heq.symm).unique hright

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
