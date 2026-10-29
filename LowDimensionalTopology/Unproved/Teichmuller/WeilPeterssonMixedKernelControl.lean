module

public import LowDimensionalTopology.Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
public import Mathlib.LinearAlgebra.Basis.Basic

/-! Explicit mixed-kernel analytic control for the original WP directions. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller.TeichmullerSpace
open Geometry.Teichmuller.GammaMeasurableBeltrami
open Geometry.Teichmuller.NormalizedCoefficientTransport
open Geometry.Teichmuller.WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth

/-- First-slot linearity, mixed square-integrability and vertical continuity
of the literal source kernel. Finite basis expansion and strict signs are
proved consumers; none is included in this analytic obligation. -/
def WeilPeterssonMixedKernelControl : Prop :=
  ∀ (ν : Ball Γ)
    (P : Geometry.Fuchsian.HalfPlaneFuchsianGroup
      ((deformedGroup hΓ ν).map Geometry.Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Geometry.Fuchsian.IsHalfPlaneFundamentalRegion P F) (v : E),
    IsLinearMap ℂ (fun u : E =>
      SourceKernel.sesquilinear (μ ν P F hF u) (μ ν P F hF v)) ∧
    ∀ u : E,
      let e := fun ζ z : ℍ =>
        ‖SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF v) ζ z +
          SourceKernel.bilinear (μ ν P F hF v) (μ ν P F hF u) ζ z‖ ^ 2 +
          2 * ‖SourceKernel.sesquilinear (μ ν P F hF u) (μ ν P F hF v) ζ z‖ ^ 2
      (∀ ζ : ℍ, Integrable (e ζ) flatArea) ∧
      IntegrableOn (fun ζ => ∫ z : ℍ, e ζ z ∂flatArea) F flatArea ∧
      ∀ ζ : ℍ, Continuous
        (SourceKernel.sesquilinear (μ ν P F hF u) (μ ν P F hF v) ζ)

end LowDimensionalTopology.Unproved.Teichmuller
