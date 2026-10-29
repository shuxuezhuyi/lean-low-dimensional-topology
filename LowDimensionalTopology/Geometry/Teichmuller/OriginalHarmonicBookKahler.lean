module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicIntegralFirstVariation
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonBookKahler

/-!
# The original WP Kähler criterion from the actual integral variation

The proved integral-variation interface is applied separately to each
actual deformed reference surface. The original local smoothness input
is retained only for the fixed original surface.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami LiZhongQC NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)

/-- The same original positive Hermitian WP metric and fundamental form
satisfy the book's Kähler criterion, with the actual integral variation
constructed on every actual deformed reference. -/
theorem nativeWeilPeterssonIsBookKahler
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0}) :
    NativeWeilPeterssonIsBookKahler R hp hg hgenus hΓ hfree hsmooth hWP := by
  refine nativeWeilPeterssonIsBookKahler_of_harmonicVariation
    R hp hg hgenus hΓ hfree hsmooth hWP ?_ hjets
  intro ν
  exact nativeWeilPeterssonHarmonicIntegralFirstVariation
    (deformedNativeSurface R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hg
    (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) (deformedGroup_spec hΓ ν).1
    (deformedNativeSurface_actsFreely R hgenus hΓ hp ν) hsmooth hjets

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
