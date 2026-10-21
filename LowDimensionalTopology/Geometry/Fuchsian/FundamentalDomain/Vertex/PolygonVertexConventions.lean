module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSelfPairedSides
public import Mathlib.Tactic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology
open scoped Complex.UnitDisc Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Surfaces

/-- The optional convention counts all original vertices and every actual elliptic fixed point in the closed polygon. -/
def IsEllipticConventionFuchsianVertex {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (x : P.domain.carrier) : Prop :=
  IsFuchsianPolygonVertex P D x ∨ (x ∈ closure D ∧ ¬ IsAccidentalFuchsianPoint P x)

/-- Every actual elliptic fixed point which is not an original vertex has its literal self-paired side. -/
theorem IsConvexFuchsianPolygon.nonvertex_elliptic_self_paired
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {x : P.domain.carrier} (hx : x ∈ closure D)
    (hn : ¬ IsFuchsianPolygonVertex P D x) (he : ¬ IsAccidentalFuchsianPoint P x) :
    ∃ s : FuchsianPolygonSides P D, x ∈ s.val ∧ fuchsianPairedSide hD s = s ∧
      IsFuchsianPolygonSideInterior P D x ∧ fuchsianSideElement hD s • x = x ∧
      fuchsianPointOrder P x = 2 ∧ fuchsianPolygonCycle P D x = {x} := by
  classical
  have hnd : x ∉ D := fun hd => he (hD.locallyFinite.fundamental.interior_point_accidental hd)
  have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hf : x ∈ frontier D := by rw [hDo.frontier_eq]; exact ⟨hx,hnd⟩
  have hi := hD.nonvertex_is_side_interior hf hn
  obtain ⟨S,hS,hxS⟩ := hD.boundary_mem_side hf
  let s : FuchsianPolygonSides P D := ⟨S,hS⟩
  obtain ⟨g,hg,hfix⟩ := not_not.mp he
  have hg0 : g ≠ 1 := fun h => hg.1 (congrArg Subtype.val h)
  have hge := hD.side_interior_fixing_eq_pairing s hxS hi g hg0 hfix
  have hsfix : fuchsianSideElement hD s • x = x := hge ▸ hfix
  exact ⟨s,hxS,fuchsianPairedSide_eq_self_of_fixed_interior hD s hxS hi hsfix,
    hi,hsfix,hD.side_interior_fixed_order_two s hxS hi hsfix,
    hD.side_interior_fixed_cycle_singleton s hxS hi hsfix⟩

/-- The optional convention differs from the original one precisely at order-two singleton-cycle points. -/
theorem IsConvexFuchsianPolygon.ellipticConvention_extra_iff_order_two_singleton
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (x : P.domain.carrier) :
    (IsEllipticConventionFuchsianVertex P D x ∧ ¬ IsFuchsianPolygonVertex P D x) ↔
      (x ∈ closure D ∧ fuchsianPointOrder P x = 2 ∧
        fuchsianPolygonCycleLength P (fuchsianPolygonCycle P D x) = 1) := by
  constructor
  · rintro ⟨hv,hn⟩
    rcases hv with hv | ⟨hx,he⟩
    · exact False.elim (hn hv)
    obtain ⟨s,_hxS,_hs,_hi,_hfix,ho,hc⟩ := hD.nonvertex_elliptic_self_paired hx hn he
    exact ⟨hx,ho,by rw [hc]; exact Set.ncard_singleton x⟩
  · rintro ⟨hx,ho,hc⟩
    have hi := hD.order_two_singleton_cycle_side_interior hx ho hc
    refine ⟨Or.inr ⟨hx,?_⟩,(hD.side_interior_iff_boundary_nonvertex x).mp hi |>.2⟩
    intro ha
    have hone := (isAccidentalFuchsianPoint_iff_pointOrder_one P x).mp ha
    omega

/-- The optional vertex set consists of the original vertices and precisely the fixed interior points of self-paired sides. -/
theorem IsConvexFuchsianPolygon.ellipticConvention_iff_vertex_or_self_paired
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (x : P.domain.carrier) :
    IsEllipticConventionFuchsianVertex P D x ↔ IsFuchsianPolygonVertex P D x ∨
      ∃ s : FuchsianPolygonSides P D, fuchsianPairedSide hD s = s ∧ x ∈ s.val ∧
        fuchsianSideElement hD s • x = x ∧ IsFuchsianPolygonSideInterior P D x := by
  classical
  constructor
  · intro he
    by_cases hv : IsFuchsianPolygonVertex P D x
    · exact Or.inl hv
    · rcases he with hx | ⟨hx,hacc⟩
      · exact False.elim (hv hx)
      obtain ⟨s,hxS,hs,hi,hfix,_⟩ := hD.nonvertex_elliptic_self_paired hx hv hacc
      exact Or.inr ⟨s,hs,hxS,hfix,hi⟩
  · rintro (hv | ⟨s,_hs,hxS,hfix,hi⟩)
    · exact Or.inl hv
    · refine Or.inr ⟨frontier_subset_closure (hi.mem_frontier hD.locallyFinite.fundamental),?_⟩
      intro ha
      exact (fuchsianSideElement_spec hD s).1
        ((isAccidentalFuchsianPoint_iff_no_stabilizer P x).mp ha _ hfix)

/-- The geometric two vertex conventions agree exactly when no literal original side is self-paired. -/
theorem IsConvexFuchsianPolygon.vertex_conventions_agree_iff_no_self_paired
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) :
    (∀ x, IsEllipticConventionFuchsianVertex P D x ↔ IsFuchsianPolygonVertex P D x) ↔
      ∀ s : FuchsianPolygonSides P D, fuchsianPairedSide hD s ≠ s := by
  constructor
  · intro he s hs
    obtain ⟨x,hx,hfix,hi⟩ := (fuchsianPairedSide_eq_self_iff_fixed_interior hD s).mp hs
    have hv := (he x).mp ((hD.ellipticConvention_iff_vertex_or_self_paired x).mpr
      (Or.inr ⟨s,hs,hx,hfix,hi⟩))
    exact hD.vertex_not_side_interior hv hi
  · intro hn x
    rw [hD.ellipticConvention_iff_vertex_or_self_paired x]
    constructor
    · rintro (hv | ⟨s,hs,_⟩)
      · exact hv
      · exact False.elim (hn s hs)
    · exact Or.inl

end LowDimensionalTopology.Geometry.Fuchsian
