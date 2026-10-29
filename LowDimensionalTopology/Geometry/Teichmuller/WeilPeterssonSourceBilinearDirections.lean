module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonPVLinearDirections
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonInnerPrincipalValue
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonOuterPrincipalValue

/-!
# The actual source A kernel in the original coordinate directions

The genuine inner and lower outer principal-value producers supply every
basis limit needed for the finite expansion of the actual tangent directions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth

/-- The actual source A kernel is the double coordinate sum of its original
basis values, with all singular limits supplied by the actual PV producers. -/
theorem nativeWeilPeterssonSourceBilinear_coordinate_expansion
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup
      ((NormalizedCoefficientTransport.deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (u v : E) (ζ z : ℍ) :
    SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF v) ζ z =
      ∑ j : I, ∑ k : I, u j * v k *
        SourceKernel.bilinear (μ ν P F hF (Pi.single j 1))
          (μ ν P F hF (Pi.single k 1)) ζ z := by
  exact nativeWeilPeterssonSourceBilinear_finset
    R hp hg hgenus hΓ hfree hsmooth ν P F hF u v ζ z
    (fun k ξ => nativeWeilPetersson_inner_principalValueExists
      R hp hg hgenus hΓ hfree hsmooth ν P F hF (Pi.single k 1) z ξ)
    (fun j k => nativeWeilPetersson_outer_principalValueExists
      R hp hg hgenus hΓ hfree hsmooth ν P F hF (Pi.single j 1) (Pi.single k 1) z ζ)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
