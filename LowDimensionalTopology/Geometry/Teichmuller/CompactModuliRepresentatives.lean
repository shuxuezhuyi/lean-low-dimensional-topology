module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricModuliQuotientRealization
public import LowDimensionalTopology.Unproved.Teichmuller.PositiveSmoothMarkability

/-!
# Compact targets for the book's fixed-reference moduli quotient

The two metric quotient equivalences are already proved and are reused as-is.
Here the explicit classical marking assumption supplies representatives with
exactly the original compact target, in Type 0. No new moduli space is defined.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

variable {X : Type} [TopologicalSpace X]

/-- Every original compact same-genus target is represented by its own surface;
equality with any native moduli representative is exactly biholomorphism. -/
theorem compact_sameGenus_moduli_representative_of_markability
    (R : ClosedRiemannSurface X)
    (hmark : LowDimensionalTopology.Unproved.Teichmuller.PositiveSmoothMarkability R)
    {Y : Type} [TopologicalSpace Y] (S : ClosedRiemannSurface Y) (g : ℕ)
    (hR : R.HasGenus g) (hS : S.HasGenus g) :
    ∃ (F : SmoothSurfaceEquiv R.toRiemannSurface S.toRiemannSurface)
      (hF : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas F.toHomeomorph),
      let M : MarkedRiemannSurface.{0, 0} R :=
        { carrier := Y
          topology := inferInstance
          surface := S
          marking := F
          orientation_preserving := hF }
      ∀ N : MarkedRiemannSurface.{0, 0} R,
        N.surface.HasGenus g ∧
          (ModuliSpace.mk M = ModuliSpace.mk N ↔
            ∃ h : Y ≃ₜ N.carrier,
              RiemannAnalyticMap S.toRiemannAtlas N.surface.toRiemannAtlas h) := by
  obtain ⟨F, hF⟩ := hmark S g hR hS
  refine ⟨F, hF, ?_⟩
  intro M N
  constructor
  · obtain ⟨e⟩ := hR
    exact ⟨N.marking.toHomeomorph.symm.trans e⟩
  · exact ModuliSpace.mk_eq_mk_iff _ N

end LowDimensionalTopology.Geometry.Teichmuller
