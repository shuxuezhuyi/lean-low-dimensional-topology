module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNMarkedTransportComposition
public import LowDimensionalTopology.Geometry.Teichmuller.NativeReferenceChange

/-!
# Original circle phases under the actual reference change

The reference map is the existing inverse-precomposition equivalence.
The actual smooth reference marking is homotopic to its supplied QC map.
The quotient square follows from that homotopy, and the complete marked
geometric family supplies the same final realization at every point.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (m : MarkedRiemannSurface.{0, 0} R) (hgenus₁ : m.surface.HasGenus g)
    (e : X ≃ₜ m.carrier)
    (he : letI := R.toRiemannAtlas.toChartedSpace
      letI := m.surface.toRiemannAtlas.toChartedSpace; LiZhongQC.IsQCRS e)
    (hmark : ContinuousMap.Homotopic m.markingMap (_root_.toContinuousMap e))

include hmark in
/-- The actual inverse reference change cancels the supplied reference marking
up to its true homotopy on the same final marked target. -/
theorem originalFN_referenceChange_composed_marking
    (n : MarkedRiemannSurface.{0, 0} m.surface) :
    TeichmullerSpace.referenceChangeEquiv R m.surface hg hgenus hgenus₁ e he
      (TeichmullerSpace.mk (originalFNComposedMarkedSurface m n)) =
        TeichmullerSpace.mk n := by
  let := R.toRiemannAtlas.toChartedSpace
  let := m.surface.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := m.surface.toRiemannAtlas.isManifold
  apply TeichmullerSpace.toSource_injective m.surface
  rw [TeichmullerSpace.toSource_referenceChangeEquiv]
  change Quot.mk _ (SourceReferenceChange.marked e he
    (originalFNComposedMarkedSurface m n).toSource) = Quot.mk _ n.toSource
  apply Quot.sound
  refine ⟨Homeomorph.refl n.carrier, LiZhongQC.isBiholomorphic_id, ?_⟩
  have h := (ContinuousMap.Homotopic.refl n.markingMap).comp
    (hmark.comp (ContinuousMap.Homotopic.refl (_root_.toContinuousMap e.symm)))
  have hcancel : n.markingMap.comp
      ((_root_.toContinuousMap e).comp (_root_.toContinuousMap e.symm)) = n.markingMap := by
    ext y
    exact congrArg n.markingMap (e.apply_symm_apply y)
  change ContinuousMap.Homotopic
    (n.markingMap.comp (m.markingMap.comp (_root_.toContinuousMap e.symm))) n.markingMap
  simpa only [hcancel] using h

variable {e₀ : X ≃ₜ PolygonQuotient g}
    {e₁ : m.carrier ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (D₀ : OriginalFNRealization M inc)
    {N : HyperbolicSurfaceModel m.surface.toRiemannSurface}
    (D₁ : OriginalFNRealization N inc) (t₀₁ : OriginalFNMarkedTransport D₀ m D₁)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e₀)
    (hA₁ : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable m.surface hg e₁)
    (A₁ : OriginalFNGeometricFamily hA₁ D₁)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (φ₁ : C(nativeFrickeImage hA₁, Fin (3 * g - 3) → Circle))
    (hφ : ∀ (k : MarkedRiemannSurface.{0, 0} R)
      (P : HyperbolicSurfaceModel k.surface.toRiemannSurface)
      (D : OriginalFNRealization P inc) (_t : OriginalFNMarkedTransport D₀ k D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk k),
        ⟨TeichmullerSpace.mk k, rfl⟩⟩ j = D.phase j)
    (hφ₁ : ∀ (k : MarkedRiemannSurface.{0, 0} m.surface)
      (P : HyperbolicSurfaceModel k.surface.toRiemannSurface)
      (D : OriginalFNRealization P inc) (_t : OriginalFNMarkedTransport D₁ k D)
      (j : Fin (3 * g - 3)),
      φ₁ ⟨finiteFrickeCoordinates hA₁ (TeichmullerSpace.mk k),
        ⟨TeichmullerSpace.mk k, rfl⟩⟩ j = D.phase j)

include hmark t₀₁ A₁ hφ hφ₁ in
/-- The two original prescribed circle phases commute with the SAME actual
reference change at every native point, using its actual marked family. -/
theorem originalFN_circlePhase_referenceChange
    (q : TeichmullerSpace.{0, 0} R) (j : Fin (3 * g - 3)) :
    φ ⟨finiteFrickeCoordinates hA q, ⟨q, rfl⟩⟩ j =
      φ₁ ⟨finiteFrickeCoordinates hA₁
          (TeichmullerSpace.referenceChangeEquiv R m.surface hg hgenus hgenus₁ e he q),
        ⟨TeichmullerSpace.referenceChangeEquiv R m.surface hg hgenus hgenus₁ e he q, rfl⟩⟩ j := by
  let A := TeichmullerSpace.referenceChangeEquiv R m.surface hg hgenus hgenus₁ e he
  obtain ⟨n, hn⟩ : ∃ n : MarkedRiemannSurface.{0, 0} m.surface,
      TeichmullerSpace.mk n = A q := ⟨Quotient.out (A q), Quotient.out_eq _⟩
  have hpre : TeichmullerSpace.mk (originalFNComposedMarkedSurface m n) = q := by
    apply A.injective
    exact (originalFN_referenceChange_composed_marking
      R hg hgenus m hgenus₁ e he hmark n).trans hn
  obtain ⟨D₂, t₁₂⟩ := A₁ n
  have h := originalFN_circlePhase_composed_marking D₀ m D₁ t₀₁ hA hA₁ φ φ₁ hφ hφ₁
    n (chosenCanonicalModel hA₁ n).model D₂ t₁₂ j
  rw [hpre, hn] at h
  exact h

end LowDimensionalTopology.Geometry.Teichmuller
