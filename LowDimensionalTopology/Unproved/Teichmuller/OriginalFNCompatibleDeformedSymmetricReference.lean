module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceChangeDerivative

/-!
# A matching symmetric reference for the specified ordered original pants

The actual normalized deformed target retains a positive smooth representative
of its actual QC marking. Its full original pants incidence is transported,
and the global anticonformal involution preserves those actual cuffs and pants.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped UpperHalfPlane

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Surfaces.HandlePresentation Geometry.Teichmuller
open Geometry.Teichmuller.GammaMeasurableBeltrami
open Geometry.Teichmuller.NormalizedCoefficientTransport

/-- A symmetric target for this full ordered pants system, on an actual
normalized deformed surface with the same marking homotopy and cuff copies. -/
def OriginalFNCompatibleDeformedSymmetricReference
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (_hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ)
    {M : HyperbolicSurfaceModel R.toRiemannSurface}
    {inc : OriginalFNCuffIncidence g}
    (D₀ : OriginalFNRealization M inc) : Prop :=
  ∃ ν : Ball Γ,
    let Yν := deformedNativeSurface R hgenus hΓ hp ν
    let eν := deformedTargetMarking R hgenus hΓ hp ν
    ∃ (F : SmoothSurfaceEquiv R.toRiemannSurface Yν.toRiemannSurface)
      (hF : PreservesComplexOrientation
        R.toRiemannAtlas Yν.toRiemannAtlas F.toHomeomorph),
      ContinuousMap.Homotopic (_root_.toContinuousMap F.toHomeomorph)
        (_root_.toContinuousMap eν) ∧
      let mν : MarkedRiemannSurface.{0, 0} R :=
        { carrier := (deformedTargetSource R hgenus hΓ hp ν).carrier
          topology := inferInstance
          surface := Yν
          marking := F
          orientation_preserving := hF }
      ∃ (N : HyperbolicSurfaceModel Yν.toRiemannSurface)
        (D' : OriginalFNRealization N inc)
        (_transport : OriginalFNMarkedTransport D₀ mν D')
        (J : (deformedTargetSource R hgenus hΓ hp ν).carrier ≃ₜ
          (deformedTargetSource R hgenus hΓ hp ν).carrier),
        @LiZhongQC.IsAnticonformalInvolution
          (deformedTargetSource R hgenus hΓ hp ν).carrier inferInstance
          Yν.toRiemannAtlas.toChartedSpace J ∧
        (∀ j, J '' Set.range (D'.cuff j).curve = Set.range (D'.cuff j).curve) ∧
        (∀ a, J '' (D'.component a).val = (D'.component a).val)

end LowDimensionalTopology.Unproved.Teichmuller
