module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic
public import LowDimensionalTopology.Geometry.Teichmuller.MappingClass

/-!
# Composing the actual original pants transports

The same final marked target is read from the two successive references.
The maps, marking homotopies, oriented full cuffs, ordered components and
intrinsic closed cuff copies all compose in the existing transport record.
The two prescribed circle phases are then evaluated on that one realization.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- Read the same final target with the actual composite smooth marking. -/
def originalFNComposedMarkedSurface (m : MarkedRiemannSurface.{0, 0} R)
    (n : MarkedRiemannSurface.{0, 0} m.surface) : MarkedRiemannSurface.{0, 0} R where
  carrier := n.carrier
  topology := n.topology
  surface := n.surface
  marking := SmoothSurfaceEquiv.trans m.marking n.marking
  orientation_preserving := n.orientation_preserving.comp
    m.orientation_preserving m.marking.toHomeomorph.continuous

namespace OriginalFNMarkedTransport

variable {g : ℕ} {inc : OriginalFNCuffIncidence g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface}
    {D₀ : OriginalFNRealization M inc}
    {m : MarkedRiemannSurface.{0, 0} R}
    {N : HyperbolicSurfaceModel m.surface.toRiemannSurface}
    {D₁ : OriginalFNRealization N inc}
    {n : MarkedRiemannSurface.{0, 0} m.surface}
    {P : HyperbolicSurfaceModel n.surface.toRiemannSurface}
    {D₂ : OriginalFNRealization P inc}

/-- The full ordered transport composes through its actual intermediate
pants, retaining the oriented cuff homotopy and both intrinsic projections. -/
def comp (t₀₁ : OriginalFNMarkedTransport D₀ m D₁)
    (t₁₂ : OriginalFNMarkedTransport D₁ n D₂) :
    OriginalFNMarkedTransport D₀ (originalFNComposedMarkedSurface m n) D₂ where
  map := t₀₁.map.trans t₁₂.map
  marking_homotopy := by
    change ContinuousMap.Homotopic
      ((_root_.toContinuousMap t₁₂.map).comp (_root_.toContinuousMap t₀₁.map))
      (n.markingMap.comp m.markingMap)
    exact t₁₂.marking_homotopy.comp t₀₁.marking_homotopy
  cuff_orientation := by
    intro j
    exact LiZhongQC.s30b_fh_trans
      (LiZhongQC.s30b_fh_map n.markingMap.continuous (t₀₁.cuff_orientation j))
      (t₁₂.cuff_orientation j)
  component_image := by
    intro a
    change (t₁₂.map ∘ t₀₁.map) '' (D₀.component a).val = (D₂.component a).val
    rw [Set.image_comp, t₀₁.component_image a, t₁₂.component_image a]
  closureMap := fun a => (t₀₁.closureMap a).trans (t₁₂.closureMap a)
  closure_projection := by
    intro a x
    change (D₂.pants a).projection ((t₁₂.closureMap a) ((t₀₁.closureMap a) x)).val =
      t₁₂.map (t₀₁.map ((D₀.pants a).projection x.val))
    rw [t₁₂.closure_projection, t₀₁.closure_projection]
  closure_cuff := by
    intro a i
    change ((t₁₂.closureMap a) ∘ (t₀₁.closureMap a)) ''
      {x : ↥(closure (D₀.pants a).kernel) |
        x.val ∈ range ((D₀.pants a).cuff i).curve} =
      {x : ↥(closure (D₂.pants a).kernel) |
        x.val ∈ range ((D₂.pants a).cuff i).curve}
    rw [Set.image_comp, t₀₁.closure_cuff a i, t₁₂.closure_cuff a i]

end OriginalFNMarkedTransport

variable {g : ℕ} {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (D₀ : OriginalFNRealization M inc) (m : MarkedRiemannSurface.{0, 0} R)
    {N : HyperbolicSurfaceModel m.surface.toRiemannSurface}
    (D₁ : OriginalFNRealization N inc) (t₀₁ : OriginalFNMarkedTransport D₀ m D₁)
    {e₁ : m.carrier ≃ₜ PolygonQuotient g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hA₁ : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable m.surface hg e₁)
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

include t₀₁ hφ hφ₁ in
/-- The two existing prescribed circle phases have the same literal value
on the same final realization after the full ordered transport is composed. -/
theorem originalFN_circlePhase_composed_marking
    (n : MarkedRiemannSurface.{0, 0} m.surface)
    (P : HyperbolicSurfaceModel n.surface.toRiemannSurface)
    (D₂ : OriginalFNRealization P inc) (t₁₂ : OriginalFNMarkedTransport D₁ n D₂)
    (j : Fin (3 * g - 3)) :
    φ ⟨finiteFrickeCoordinates hA
        (TeichmullerSpace.mk (originalFNComposedMarkedSurface m n)),
      ⟨TeichmullerSpace.mk (originalFNComposedMarkedSurface m n), rfl⟩⟩ j =
      φ₁ ⟨finiteFrickeCoordinates hA₁ (TeichmullerSpace.mk n),
        ⟨TeichmullerSpace.mk n, rfl⟩⟩ j := by
  exact (hφ (originalFNComposedMarkedSurface m n) P D₂ (t₀₁.comp t₁₂) j).trans
    (hφ₁ n P D₂ t₁₂ j).symm

end LowDimensionalTopology.Geometry.Teichmuller
