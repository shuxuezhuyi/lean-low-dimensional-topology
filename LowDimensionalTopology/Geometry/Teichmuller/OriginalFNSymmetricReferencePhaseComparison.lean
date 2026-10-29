module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNCompatibleDeformedSymmetricReference
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNMarkedTransportComposition

/-!
# Actual marked circle-phase comparison from a matching symmetric reference

The concrete geometric input selects the actual deformed reference and full
ordered pants transport. Every further compatible final realization is read
with the genuine composite marking. Its prescribed original circle phases
then agree by the complete transport construction and the existing phase laws.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami
open NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ)
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (D₀ : OriginalFNRealization M inc)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_t : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)

include hφ in
/-- A matching symmetric reference gives genuine same-final-realization
circle-phase comparison for every further actual compatible marked target. -/
theorem exists_originalFN_symmetric_reference_circlePhase_comparison
    (hSym : Unproved.Teichmuller.OriginalFNCompatibleDeformedSymmetricReference
      R hp hg hgenus hΓ D₀) :
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
          (_t₀₁ : OriginalFNMarkedTransport D₀ mν D')
          (J : (deformedTargetSource R hgenus hΓ hp ν).carrier ≃ₜ
            (deformedTargetSource R hgenus hΓ hp ν).carrier),
          @LiZhongQC.IsAnticonformalInvolution
            (deformedTargetSource R hgenus hΓ hp ν).carrier inferInstance
            Yν.toRiemannAtlas.toChartedSpace J ∧
          (∀ j, J '' range (D'.cuff j).curve = range (D'.cuff j).curve) ∧
          (∀ a, J '' (D'.component a).val = (D'.component a).val) ∧
          ∀ {e₁ : mν.carrier ≃ₜ PolygonQuotient g}
            (hA₁ : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable mν.surface hg e₁)
            (φ₁ : C(nativeFrickeImage hA₁, Fin (3 * g - 3) → Circle)),
            (∀ (k : MarkedRiemannSurface.{0, 0} mν.surface)
              (P : HyperbolicSurfaceModel k.surface.toRiemannSurface)
              (D : OriginalFNRealization P inc) (_t : OriginalFNMarkedTransport D' k D)
              (j : Fin (3 * g - 3)),
              φ₁ ⟨finiteFrickeCoordinates hA₁ (TeichmullerSpace.mk k),
                ⟨TeichmullerSpace.mk k, rfl⟩⟩ j = D.phase j) →
            ∀ (n : MarkedRiemannSurface.{0, 0} mν.surface)
              (P : HyperbolicSurfaceModel n.surface.toRiemannSurface)
              (D₂ : OriginalFNRealization P inc) (_t₁₂ : OriginalFNMarkedTransport D' n D₂)
              (j : Fin (3 * g - 3)),
              φ ⟨finiteFrickeCoordinates hA
                  (TeichmullerSpace.mk (originalFNComposedMarkedSurface mν n)),
                ⟨TeichmullerSpace.mk (originalFNComposedMarkedSurface mν n), rfl⟩⟩ j =
                φ₁ ⟨finiteFrickeCoordinates hA₁ (TeichmullerSpace.mk n),
                  ⟨TeichmullerSpace.mk n, rfl⟩⟩ j := by
  rcases hSym with ⟨ν, F, hF, hhom, N, D', t₀₁, J, hJ, hcuffs, hpants⟩
  refine ⟨ν, F, hF, hhom, N, D', t₀₁, J, hJ, hcuffs, hpants, ?_⟩
  intro e₁ hA₁ φ₁ hφ₁ n P D₂ t₁₂ j
  exact originalFN_circlePhase_composed_marking
    D₀ _ D' t₀₁ hA hA₁ φ φ₁ hφ hφ₁ n P D₂ t₁₂ j

end LowDimensionalTopology.Geometry.Teichmuller
