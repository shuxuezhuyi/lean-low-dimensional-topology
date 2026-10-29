module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNRescaledRealTwistCoordinate
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonLocalCoefficients
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNMarkedGluing

/-!
# The same original FN coordinates on the native quotient

The two blocks are the actual marked cuff lengths and the same full real
branch rescaled by cuff length. The value agrees with the existing original
Fricke-coordinate function at the literal finite coordinate vector.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami

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

/-- The actual native marked lengths and the same rescaled full real branch. -/
def originalFNNativeRescaledCoordinateMap
    (Θ : C(nativeFrickeImage hA, Fin (3*g-3) → ℝ)) :
    TeichmullerSpace R → (Fin (3*g-3) → ℝ) × (Fin (3*g-3) → ℝ) :=
  fun q =>
    ((fun l => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus (D₀.cuff l).toLoop q),
      originalFNRescaledRealTwistCoordinate R hg hgenus hA hAlt D₀ Θ
        ⟨finiteFrickeCoordinates hA q,⟨q,rfl⟩⟩)

/-- The native map is the same original Fricke length map with the same
rescaled real branch at the literal finite coordinate vector of the point. -/
theorem originalFNNativeRescaledCoordinateMap_eq_original
    (Θ : C(nativeFrickeImage hA, Fin (3*g-3) → ℝ)) (q : TeichmullerSpace R) :
    originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ q =
      ((fun l => ((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ
          ⟨finiteFrickeCoordinates hA q,⟨q,rfl⟩⟩).1 l : ℝ)),
        originalFNRescaledRealTwistCoordinate R hg hgenus hA hAlt D₀ Θ
          ⟨finiteFrickeCoordinates hA q,⟨q,rfl⟩⟩) := by
  apply Prod.ext
  · funext l
    refine Quotient.inductionOn q ?_
    intro m
    exact (frickeGeodesicLength_coordinates R hg hgenus hA hAlt (D₀.cuff l).toLoop m).symm
  · rfl

end LowDimensionalTopology.Geometry.Teichmuller
