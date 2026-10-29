module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeNonzeroTangentNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.HarmonicHermitianCompatibility

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller
open LowDimensionalTopology.Geometry
open LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Teichmuller
open GammaMeasurableBeltrami NormalizedCoefficientTransport
universe u
variable {X : Type u} [TopologicalSpace X] (R : Surfaces.ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)

/-- Same-point harmonic identification preserves the literal Petersson integral,
for every genuine region and every pair of original harmonic coefficients. -/
def SamePointPeterssonIntegralNaturality : Prop :=
  let Y := deformedNativeSurface R hgenus hΓ hp
  let pY := deformedTargetCover R hgenus hΓ hp
  let hpY := deformedNativeSurface_uniformization R hgenus hΓ hp
  ∀ (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
      (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν')
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (P' : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν').map Hyperbolic.realSLMobius))
    (F' : Set ℍ) (hF' : Fuchsian.IsHalfPlaneFundamentalRegion P' F')
    (η ξ : NativePetersson.Harmonic (Y ν) P (pY ν) (hpY ν) F hF),
    WeilPetersson.beltramiPairing F η.val.val ξ.val.val =
      WeilPetersson.beltramiPairing F'
        (nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
          P F hF P' F' hF' η).val.val
        (nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
          P F hF P' F' hF' ξ).val.val

end LowDimensionalTopology.Unproved.Teichmuller
