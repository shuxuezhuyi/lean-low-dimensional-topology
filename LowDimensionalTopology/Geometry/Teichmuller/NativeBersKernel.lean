module

public import LowDimensionalTopology.Geometry.Teichmuller.BersDirectionalKernel
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.RegionIntegral
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedTeichmuller

/-!
# The actual Bers kernel paired on a native open fundamental region

The native open fundamental region and the source measurable integration
domain are related by their null boundary. The matrix group, its actual Möbius
image, original complex atlas, measurable coefficient class and scalar family
are retained throughout the comparison.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergman

open Surfaces LiZhongQC
universe u

/-- The actual native Bers first variation vanishes precisely when its pairing
with every original quadratic differential vanishes on the original open region. -/
theorem nativeBersDirectional_iff_nativeRegionAnnihilator
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {F : Set ℍ} (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    (∀ z ∈ lowerHalf, deriv (fun t : ℂ => nativeBersLine μ t z) 0 = 0) ↔
      ∀ q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
        ∫ z in UpperHalfPlane.coe '' F,
          GammaMeasurableBeltrami.planeRepresentative μ.val z *
            uniformizedQuadratic R p q z = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  have hΓ : IsFuchsian Γ := utm_x_isFuchsian hp
  have hs := Fuchsian.closedPlanarRegion_isFundamentalDomainH P hF
  have hkernel := bersDirectional_iff_nativeQuadraticAnnihilator R p hΓ hp hs μ
  have ho : IsOpen F := hF.1
  have hn : (volume : Measure ℂ) (UpperHalfPlane.coe '' frontier F) = 0 := hF.2.2.2
  have he (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    Fuchsian.integral_openPlanarRegion_eq_closedPlanarRegion ho hn
      (fun z => GammaMeasurableBeltrami.planeRepresentative μ.val z *
        uniformizedQuadratic R p q z)
  constructor
  · intro hzero q
    exact (he q).trans (hkernel.mp hzero q)
  · intro hnative
    exact hkernel.mpr fun q => (he q).symm.trans (hnative q)

end LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergman
