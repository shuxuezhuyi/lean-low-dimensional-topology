module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalWPVectorFieldCoordinates
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Smoothness of the original WP Cartan coordinate expression

The expression uses the whole original two-form and the literal coordinates
of the supplied native smooth vector field on the same open chart target.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3*g-3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "c" => nativeWeilPeterssonCoordinateChart
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)

/-- The actual coordinate exterior derivatives and contraction form a smooth
whole two-form expression for every native smooth vector field. -/
theorem nativeWP_cartanCoordinateRHS_contDiffOn
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ W : FormInterior.SmoothVectorField RI (M := T),
      ContDiffOn ℝ ∞
        (fun z : E =>
          extDerivWithin
            (fun y : E => (Ω y).curryLeft
              (D ((c).symm y) (W ((c).symm y)))) (c).target z +
          (extDerivWithin Ω (c).target z).curryLeft
            (D ((c).symm z) (W ((c).symm z)))) (c).target := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro W
  let ξ : E → E := fun z => D ((c).symm z) (W ((c).symm z))
  let η : E → E [⋀^Fin 1]→L[ℝ] ℝ := fun z => (Ω z).curryLeft (ξ z)
  have hξ : ContDiffOn ℝ ∞ ξ (c).target :=
    nativeWP_vectorFieldCoordinates_contDiffOn R hp hg hgenus hΓ hfree hsmooth W
  have hΩ := contDiffOn_nativeWeilPeterssonFundamentalRealCoordinateForm_of_localSmoothness
    R hp hg hgenus hΓ hfree hsmooth hWP (basePoint R)
  let curry₁ : (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ :=
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (n := 1)).toContinuousLinearMap
  have hη : ContDiffOn ℝ ∞ η (c).target := by
    change ContDiffOn ℝ ∞ (fun z => curry₁ (Ω z) (ξ z)) (c).target
    have hc : ContDiffOn ℝ ∞ (fun z => curry₁ (Ω z)) (c).target :=
      (ContinuousLinearMap.contDiff (𝕜 := ℝ) («E» := E [⋀^Fin 2]→L[ℝ] ℝ)
        (F := E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ) (n := ∞) curry₁).fun_comp_contDiffOn hΩ
    exact hc.clm_apply hξ
  have hdη : ContDiffOn ℝ ∞ (extDerivWithin η (c).target) (c).target := by
    change ContDiffOn ℝ ∞
      (fun z => ContinuousAlternatingMap.alternatizeUncurryFin
        (fderivWithin ℝ η (c).target z)) (c).target
    simpa only [Function.comp_def,
      ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply] using
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := 1) ℝ E ℝ).contDiff).comp_contDiffOn
        (hη.fderivWithin (m := ∞) (c).open_target.uniqueDiffOn (by simp))
  have hdΩ : ContDiffOn ℝ ∞ (extDerivWithin Ω (c).target) (c).target := by
    change ContDiffOn ℝ ∞
      (fun z => ContinuousAlternatingMap.alternatizeUncurryFin
        (fderivWithin ℝ Ω (c).target z)) (c).target
    simpa only [Function.comp_def,
      ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply] using
      ((ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := 2) ℝ E ℝ).contDiff).comp_contDiffOn
        (hΩ.fderivWithin (m := ∞) (c).open_target.uniqueDiffOn (by simp))
  let curry₂ : (E [⋀^Fin 3]→L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ :=
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (n := 2)).toContinuousLinearMap
  have hi : ContDiffOn ℝ ∞
      (fun z => (extDerivWithin Ω (c).target z).curryLeft (ξ z)) (c).target := by
    change ContDiffOn ℝ ∞
      (fun z => curry₂ (extDerivWithin Ω (c).target z) (ξ z)) (c).target
    have hc : ContDiffOn ℝ ∞
        (fun z => curry₂ (extDerivWithin Ω (c).target z)) (c).target :=
      (ContinuousLinearMap.contDiff (𝕜 := ℝ) («E» := E [⋀^Fin 3]→L[ℝ] ℝ)
        (F := E →L[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ) (n := ∞) curry₂).fun_comp_contDiffOn hdΩ
    exact hc.clm_apply hξ
  simpa only [ξ, η] using hdη.add hi

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
