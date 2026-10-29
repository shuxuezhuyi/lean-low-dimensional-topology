module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNMarkedTransportComposition
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNBookLeftCopyTransport

/-!
# The same geometric book-left labels across the actual reference transport

The supplied reference's actual fixed labels remain valid on the intermediate
reference and on every further compatible final realization. The complete
ordered pants transports are composed before using the existing geometric
left-copy coherence, so no independent equality of chosen labels is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
    {g : ℕ} {inc : OriginalFNCuffIncidence g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface}
    (D₀ : OriginalFNRealization M inc) (m : MarkedRiemannSurface.{0, 0} R)
    {N : HyperbolicSurfaceModel m.surface.toRiemannSurface}
    (D₁ : OriginalFNRealization N inc) (t₀₁ : OriginalFNMarkedTransport D₀ m D₁)

include t₀₁ in
/-- The very same supplied reference's chosen left labels have actual inward
germ coherence on the new reference and every further marked realization. -/
theorem originalFN_same_bookLeft_under_reference_transport
    (hBook : Unproved.Teichmuller.OriginalFNBookLeftCopyTransport D₀) :
    (∀ j, OriginalFNCopyLeftGerm D₁ j (Classical.choose hBook j)) ∧
      ∀ (n : MarkedRiemannSurface.{0, 0} m.surface)
        (P : HyperbolicSurfaceModel n.surface.toRiemannSurface)
        (D₂ : OriginalFNRealization P inc) (_t₁₂ : OriginalFNMarkedTransport D₁ n D₂)
        (j : Fin (3 * g - 3)),
        OriginalFNCopyLeftGerm D₂ j (Classical.choose hBook j) := by
  constructor
  · exact (Classical.choose_spec hBook).2 m N D₁ t₀₁
  · intro n P D₂ t₁₂ j
    exact (Classical.choose_spec hBook).2
      (originalFNComposedMarkedSurface m n) P D₂ (t₀₁.comp t₁₂) j

include t₀₁ in
/-- The already supplied geometric left-copy input yields the corresponding
input for the new actual reference by the SAME witnessed left labels. -/
theorem originalFN_bookLeftCopyTransport_of_reference_transport
    (hBook : Unproved.Teichmuller.OriginalFNBookLeftCopyTransport D₀) :
    Unproved.Teichmuller.OriginalFNBookLeftCopyTransport D₁ := by
  exact ⟨Classical.choose hBook,
    originalFN_same_bookLeft_under_reference_transport D₀ m D₁ t₀₁ hBook⟩

end LowDimensionalTopology.Geometry.Teichmuller
