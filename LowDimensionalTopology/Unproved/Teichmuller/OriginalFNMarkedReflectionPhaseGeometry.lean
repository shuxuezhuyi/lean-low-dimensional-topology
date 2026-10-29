module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNContinuousPhase
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalNativeMarkedReflection
public import LowDimensionalTopology.Geometry.Teichmuller.MarkedGeodesicLength

/-!
# The lower original FN reflection geometry

Only actual marked cuff length and the doubled original BV circle phase occur.
The whole compatible geometric family and its actual intrinsic cuff incidence
are retained. There is no real branch, integer, differential, frame or WP input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Teichmuller Geometry.Surfaces Geometry.Surfaces.HandlePresentation
open Geometry.Teichmuller.GeneralQC

/-- The same global reflection preserves actual cuff length and inverts the
    doubled original geometric BV circle phase. -/
def OriginalFNMarkedReflectionPhaseGeometry
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (hA : CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0,0} R,
      CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc) (J : X ≃ₜ X)
    (hJ : @LiZhongQC.IsAnticonformalInvolution X inferInstance
      R.toRiemannAtlas.toChartedSpace J)
    (_hJcuffs : ∀ j, J '' Set.range (D₀.cuff j).curve = Set.range (D₀.cuff j).curve)
    (_hJpants : ∀ a, J '' (D₀.component a).val = (D₀.component a).val) : Prop :=
  ∀ A : OriginalFNGeometricFamily hA D₀,
    (∀ m n : MarkedRiemannSurface.{0,0} R, MarkedRiemannSurface.Equivalent m n →
      ∀ j, (A m).1.phase j = (A n).1.phase j) →
    (∀ (m : MarkedRiemannSurface.{0,0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D),
      ∀ j, (A m).1.phase j = D.phase j) →
    let rN := originalNativeTeichmullerReflection R hg hgenus J hJ
    ∀ (q : TeichmullerSpace.{0,0} R) (j : Fin (3 * g - 3)),
      markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus (D₀.cuff j).toLoop (rN q) =
        markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus (D₀.cuff j).toLoop q ∧
      (originalFNFamilyPhase hA hAlt D₀ A
        ⟨finiteFrickeCoordinates hA (rN q), ⟨rN q, rfl⟩⟩ j) ^ 2 =
        ((originalFNFamilyPhase hA hAlt D₀ A
          ⟨finiteFrickeCoordinates hA q, ⟨q, rfl⟩⟩ j) ^ 2)⁻¹

end LowDimensionalTopology.Unproved.Teichmuller
