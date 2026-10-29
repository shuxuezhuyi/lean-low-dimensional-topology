module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNNativeCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonLocalCoefficients
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNMarkedGluing
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Smooth local inverse compatibility for the same native FN map

The classical obligation concerns smooth local inverses of the literal
original marked length and rescaled real twist map in the existing Bers
chart, retaining the same original phase, branch and marked realization.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Surfaces.HandlePresentation
open Geometry.Teichmuller Geometry.Teichmuller.TeichmullerSpace
open Geometry.Teichmuller.GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0,0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3*g-3) → ℂ
local notation "F" => (Fin (3*g-3) → ℝ) × (Fin (3*g-3) → ℝ)
local notation "RI" => 𝓘(ℝ, E)
local notation "FI" => 𝓘(ℝ, F)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "c" => nativeWeilPeterssonCoordinateChart
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

/-- The same original FN map has smooth local inverses in the native real
Bers chart, retaining its original phase, branch and marked realization data. -/
def OriginalFNNativeSmoothInverse
    (_hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3*g-3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3*g-3) → ℝ))
    (_hφ : ∀ (m : MarkedRiemannSurface.{0,0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3*g-3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m,rfl⟩⟩ j = D.phase j)
    (_hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (_hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (_hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)
    : Prop := by
  let := C
  let FN := originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
  let K : E → F := FN ∘ (c).symm
  exact ∀ z ∈ (c).target,
    ∃ f : OpenPartialHomeomorph E F,
      z ∈ f.source ∧ f.source ⊆ (c).target ∧
      (∀ y ∈ f.source, f y = K y) ∧
      ContDiffOn ℝ ∞ (f : E → F) f.source ∧
      ContDiffOn ℝ ∞ (f.symm : F → E) f.target

end LowDimensionalTopology.Unproved.Teichmuller
