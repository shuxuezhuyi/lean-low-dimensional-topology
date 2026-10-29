module

public import LowDimensionalTopology.Geometry.Fuchsian.PantsCoreCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.QuotientSignature
public import Mathlib.Data.Set.Card

/-!
# The actual Nielsen cycles are precisely the projected core frontier components

The projected frontier and all cycle carriers are those of the original group
and its original orbit quotient. The existing first-return/class equivalence
supplies the count; no new polygon or classification data is introduced.
-/

@[expose] public section
noncomputable section
open Set

namespace LowDimensionalTopology.Geometry.Fuchsian

section ActualBoundaryCycles
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
variable {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
  {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
  (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
  (hfin : {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w : P.domain.carrier) (hwD : w ∈ D) (hwN : w ∈ fuchsianNielsenCore P hNE)
  (J : PolygonalCircle)
  (hc : J.carrier = Polygon.discPolygonKleinPlane ''
    (⋃ s : NielsenBoundarySide hD hNE, s.carrier))
  (hv : ∀ p, J.IsVertexPoint p ↔ p ∈ Polygon.discPolygonKleinPlane ''
    nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "F" => frontier (threeBoundaryOpenCore P hNE)

theorem nielsenProjectedBoundaryCycles_eq_openCore_frontier :
    (⋃ c : C, cycleCarrier c) = F := by
  rw [frontier_threeBoundaryOpenCore]
  exact nielsenProjectedBoundaryCycles_cover hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenProjectedBoundaryCycle_class_circle (c : C) :
    Nonempty (↥(cycleCarrier c) ≃ₜ Circle) := by
  induction c using Quotient.inductionOn with
  | h b => exact nielsenProjectedBoundaryCycle_circle hD hNE hFG hfin w hwD hwN J hc hv b

theorem nielsenProjectedBoundaryCycle_isConnected (c : C) :
    IsConnected (cycleCarrier c) := by
  obtain ⟨e⟩ := nielsenProjectedBoundaryCycle_class_circle hD hNE hFG hfin w hwD hwN J hc hv c
  let : ConnectedSpace (cycleCarrier c) := e.symm.surjective.connectedSpace e.symm.continuous
  exact isConnected_iff_connectedSpace.mpr inferInstance

/-- A point of a genuine cycle has that entire cycle as its component in the
actual frontier of the original projected open Nielsen core. -/
theorem nielsenProjectedBoundaryCycle_eq_connectedComponentIn
    (c : C) {x : Surfaces.MobiusDomainQuotient P.domain} (hx : x ∈ cycleCarrier c) :
    connectedComponentIn F x = cycleCarrier c := by
  let : T2Space (Surfaces.MobiusDomainQuotient P.domain) :=
    Surfaces.mobiusDomainQuotient_t2 P.domain P.discontinuous
  let T : Set (Surfaces.MobiusDomainQuotient P.domain) :=
    ⋃ d : {d : C // d ≠ c}, cycleCarrier d.val
  have hcompact (d : C) : IsCompact (cycleCarrier d) :=
    nielsenProjectedBoundaryCycle_isCompact hD hNE hFG hfin w hwD hwN J hc hv d
  have hS : IsClosed (cycleCarrier c) := (hcompact c).isClosed
  have hT : IsClosed T := isClosed_iUnion_of_finite (fun d => (hcompact d.val).isClosed)
  have hdisj : Disjoint (cycleCarrier c) T := by
    apply disjoint_left.mpr
    intro p hp hpt
    obtain ⟨d, hpd⟩ := mem_iUnion.mp hpt
    exact disjoint_left.mp
      (nielsenProjectedBoundaryCycle_pairwise_disjoint hD hNE hFG hfin w hwD hwN J hc hv
        d.property.symm) hp hpd
  have hsub (d : C) : cycleCarrier d ⊆ F := by
    rw [← nielsenProjectedBoundaryCycles_eq_openCore_frontier hD hNE hFG hfin w hwD hwN J hc hv]
    exact subset_iUnion (fun e : C => cycleCarrier e) d
  have hcover : F ⊆ cycleCarrier c ∪ T := by
    intro p hp
    rw [← nielsenProjectedBoundaryCycles_eq_openCore_frontier hD hNE hFG hfin w hwD hwN J hc hv] at hp
    obtain ⟨d, hpd⟩ := mem_iUnion.mp hp
    by_cases he : d = c
    · exact Or.inl (he ▸ hpd)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨d, he⟩, hpd⟩)
  apply subset_antisymm
  · intro p hp
    by_contra hpn
    have hpt : p ∈ T := (hcover (connectedComponentIn_subset F x hp)).resolve_left hpn
    have hconn : IsPreconnected (connectedComponentIn F x) := isPreconnected_connectedComponentIn
    obtain ⟨z, _hz, hzS, hzT⟩ := isPreconnected_closed_iff.mp
      hconn
      _ _ hS hT (fun y hy => hcover (connectedComponentIn_subset F x hy))
      ⟨x, mem_connectedComponentIn (hsub c hx), hx⟩ ⟨p, hp, hpt⟩
    exact disjoint_left.mp hdisj hzS hzT
  · have hconn := (nielsenProjectedBoundaryCycle_isConnected hD hNE hFG hfin w hwD hwN J hc hv c).2
    exact hconn.subset_connectedComponentIn hx (hsub c)

theorem nielsenProjectedBoundaryCycle_injective : Function.Injective cycleCarrier := by
  intro c d he
  by_contra hne
  obtain ⟨x, hx⟩ := nielsenProjectedBoundaryCycle_nonempty hD hNE hFG hfin w hwD hwN J hc hv c
  exact disjoint_left.mp
    (nielsenProjectedBoundaryCycle_pairwise_disjoint hD hNE hFG hfin w hwD hwN J hc hv hne)
    hx (he ▸ hx)

theorem threeBoundaryOpenCore_frontierComponents_eq_range :
    {S : Set (Surfaces.MobiusDomainQuotient P.domain) |
      ∃ x ∈ F, connectedComponentIn F x = S} = range cycleCarrier := by
  ext S
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← nielsenProjectedBoundaryCycles_eq_openCore_frontier hD hNE hFG hfin w hwD hwN J hc hv] at hx
    obtain ⟨c, hxc⟩ := mem_iUnion.mp hx
    exact ⟨c, (nielsenProjectedBoundaryCycle_eq_connectedComponentIn hD hNE hFG hfin w hwD hwN J hc hv c hxc).symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨x, hx⟩ := nielsenProjectedBoundaryCycle_nonempty hD hNE hFG hfin w hwD hwN J hc hv c
    refine ⟨x, ?_, nielsenProjectedBoundaryCycle_eq_connectedComponentIn hD hNE hFG hfin w hwD hwN J hc hv c hx⟩
    rw [← nielsenProjectedBoundaryCycles_eq_openCore_frontier hD hNE hFG hfin w hwD hwN J hc hv]
    exact mem_iUnion.mpr ⟨c, hx⟩

include hD hNE hFG hfin w hwD hwN J hc hv in
theorem threeBoundaryOpenCore_frontierComponents_ncard_eq_classes :
    {S : Set (Surfaces.MobiusDomainQuotient P.domain) |
      ∃ x ∈ F, connectedComponentIn F x = S}.ncard =
        Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc) := by
  rw [threeBoundaryOpenCore_frontierComponents_eq_range hD hNE hFG hfin w hwD hwN J hc hv,
    Set.ncard_range_of_injective (nielsenProjectedBoundaryCycle_injective hD hNE hFG hfin w hwD hwN J hc hv)]
  exact nielsenBoundaryCycleClassCount_eq hD hNE hFG hfin w hwD hwN J hc hv

end ActualBoundaryCycles

/-- The actual original projected Nielsen-core frontier has three components
for the existing three-boundary-end signature. -/
theorem threeBoundaryOpenCore_frontierComponents_ncard
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {hNE : DiscreteGroups.IsNonElementary H} {hFG : H.FG}
    (h : HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3) :
    {S : Set (Surfaces.MobiusDomainQuotient P.domain) |
      ∃ x ∈ frontier (threeBoundaryOpenCore P hNE),
        connectedComponentIn (frontier (threeBoundaryOpenCore P hNE)) x = S}.ncard = 3 := by
  obtain ⟨w, hw, hwN, J, hc, hv, n, S, hr, hg, ho, hp, hb⟩ := h
  calc
    _ = Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc) :=
      threeBoundaryOpenCore_frontierComponents_ncard_eq_classes
        (dirichletDomain_isConvexFuchsianPolygon P w hw) hNE hFG
        (finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw) w
        (dirichletDomain_center_mem P w hw) hwN J hc hv
    _ = 3 := hb.symm

end LowDimensionalTopology.Geometry.Fuchsian
