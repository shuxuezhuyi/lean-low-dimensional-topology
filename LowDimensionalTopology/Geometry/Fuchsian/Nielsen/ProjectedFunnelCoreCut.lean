module

public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.QuotientSurface
public import LowDimensionalTopology.Geometry.Fuchsian.PantsCoreCarrier

/-! Projected Nielsen complementary pieces and the retained closed core.
The constructions use the original whole-group quotient. No genus or
three-boundary hypothesis is used; finite generation is displayed only where
the existing theorem identifies a complementary piece as a closed cylinder. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- The actual projected closed half-plane opposite the chosen core point. -/
def projectedNielsenClosedFunnel
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (L : Hyperbolic.DiscLine) (w : P.domain.carrier) :
    Set (Surfaces.MobiusDomainQuotient P.domain) :=
  Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P L w

/-- Remove the projected axis, retaining exactly the off-axis part of the
closed complementary piece. Its cylinder interpretation is a separate theorem. -/
def projectedNielsenFunnelInterior
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (L : Hyperbolic.DiscLine) (w : P.domain.carrier) :
    Set (Surfaces.MobiusDomainQuotient P.domain) :=
  projectedNielsenClosedFunnel P L w \
    (Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' L.carrier))

/-- Every original boundary axis, including all its quotient points, is retained. -/
theorem projectedNielsenClosedFunnel_inter_core
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (L : Hyperbolic.DiscLine)
    (hL : L ∈ nielsenBoundaryDiscLineFamily P hNE) (w : P.domain.carrier)
    (hw : w ∈ fuchsianNielsenCore P hNE) :
    projectedNielsenClosedFunnel P L w ∩ threeBoundaryClosedCore P hNE =
      Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' L.carrier) :=
  nielsenOriginalClosedFunnel_projection_inter_core P hNE L hL w hw

/-- The original closed convex core is precisely what remains after all the
projected off-axis complementary pieces have been removed. -/
theorem projectedNielsenCore_eq_compl_funnelInteriors
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (w : P.domain.carrier)
    (hw : w ∈ fuchsianNielsenCore P hNE) :
    threeBoundaryClosedCore P hNE =
      (⋃ L : nielsenBoundaryDiscLineFamily P hNE,
        projectedNielsenFunnelInterior P L.val w)ᶜ := by
  ext q
  constructor
  · intro hcore hremoved
    obtain ⟨L, hL⟩ := mem_iUnion.mp hremoved
    apply hL.2
    have h : q ∈ projectedNielsenClosedFunnel P L.val w ∩
        threeBoundaryClosedCore P hNE := ⟨hL.1, hcore⟩
    rwa [projectedNielsenClosedFunnel_inter_core P hNE L.val L.property w hw] at h
  · intro hretained
    by_contra hcore
    obtain ⟨x, hxq⟩ := Surfaces.mobiusDomainProjection_surjective P.domain q
    have hx : x ∈ (univ : Set P.domain.carrier) := mem_univ x
    rw [nielsenOriginalClosedFunnels_cover P hNE w hw] at hx
    rcases hx with hx | hx
    · exact hcore ⟨x, hx, hxq⟩
    · obtain ⟨L, hxL⟩ := mem_iUnion.mp hx
      apply hretained
      apply mem_iUnion.mpr
      refine ⟨L, ⟨⟨x, hxL, hxq⟩, ?_⟩⟩
      intro haxis
      have h : q ∈ projectedNielsenClosedFunnel P L.val w ∩
          threeBoundaryClosedCore P hNE := by
        rwa [projectedNielsenClosedFunnel_inter_core P hNE L.val L.property w hw]
      exact hcore h.2

/-- Finite generation yields a genuine semi-infinite closed cylinder whose
entire boundary is exactly the projected original axis. -/
theorem projectedNielsenClosedFunnel_puncturedCap
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    (L : Hyperbolic.DiscLine) (hL : L ∈ nielsenBoundaryDiscLineFamily P hNE)
    (w : P.domain.carrier) (hw : w ∈ fuchsianNielsenCore P hNE) :
    IsClosed (projectedNielsenClosedFunnel P L w) ∧
      ∃ B : ↥(projectedNielsenClosedFunnel P L w) ≃ₜ NielsenPuncturedClosedDisc,
        ∀ x : nielsenOriginalClosedFunnel P L w,
          ‖((B (nielsenClosedFunnelRangeProjection P L w x)).val : ℂ)‖ = 1 ↔
            x.val ∈ P.finiteCoordinate.symm '' L.carrier :=
  finitelyGenerated_originalClosedFunnel_puncturedCap P hNE hFG L hL w hw

end LowDimensionalTopology.Geometry.Fuchsian
