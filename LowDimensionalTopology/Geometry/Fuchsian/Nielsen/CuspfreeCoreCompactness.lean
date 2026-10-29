module
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.QuotientSignature
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.ThreeBoundaryEndSignature

@[expose] public section
set_option autoImplicit false
open Set
namespace LowDimensionalTopology.Geometry.Fuchsian
/-- A genuine signature with no cusps has compact projected closed Nielsen core. -/
theorem HasNielsenFuchsianSignature.isCompact_projected_closedCore
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {hNE : DiscreteGroups.IsNonElementary H} {hFG : H.FG}
    {g : ℕ} {orders : List ℕ} {boundaryEnds : ℕ}
    (h : HasNielsenFuchsianSignature P hNE hFG g orders 0 boundaryEnds) :
    IsCompact (Surfaces.mobiusDomainProjection P.domain '' closure (fuchsianNielsenCore P hNE)) := by
  obtain ⟨w, hw, hwN, J, hc, hv, n, S, hr, _hg, _ho, hcusps, _hb⟩ := h
  let hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  let hfin := finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
  let hwD := dirichletDomain_center_mem P w hw
  have hf := finite_sided_polygon_parabolic_classes_finite hD hfin
  let : IsEmpty (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) :=
    (Nat.card_eq_zero.mp hcusps.symm).resolve_right hf.not_infinite
  let K := Hyperbolic.discClosedModelClosure
    (P.finiteCoordinate '' (dirichletDomain P w ∩ fuchsianNielsenCore P hNE))
  let : CompactSpace ↥K :=
    isCompact_iff_compactSpace.mp (Hyperbolic.isCompact_discClosedModelClosure _)
  have hcpt := isCompact_range
    (continuous_nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv)
  have he := nielsenWholeCoreCappedEmbedding_isEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr
  apply isCompact_iff_isCompact_univ.mpr
  apply he.isCompact_iff.mpr
  rw [Set.image_univ,
    nielsenWholeCoreCappedEmbedding_range hD hNE hFG hfin w hwD hwN J hc hv S hr]
  simpa only [Set.range_eq_empty, Set.sdiff_empty] using hcpt

/-- A genuine three-end signature is realized with compact projected closed core
and an actual Dirichlet fundamental domain of Nielsen-core area twice pi. -/
theorem exists_three_boundary_end_signature_with_compact_core_and_dirichlet_area :
    ∃ H : Subgroup Mobius.complexMobiusGroup, ∃ P : UnitDiscFuchsianGroup H,
      ∃ hNE : DiscreteGroups.IsNonElementary H, ∃ hFG : H.FG,
        HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3 ∧
          IsCompact (Surfaces.mobiusDomainProjection P.domain '' closure (fuchsianNielsenCore P hNE)) ∧
            ∃ w : P.domain.carrier, IsDirichletCenter P w ∧ w ∈ fuchsianNielsenCore P hNE ∧
              IsFuchsianFundamentalDomain P (dirichletDomain P w) ∧
                (fuchsianNielsenCoreArea P hNE (dirichletDomain P w)).toReal = 2 * Real.pi := by
  obtain ⟨H, P, hNE, hFG, h, w, hw, hwN, hD, ha⟩ := exists_three_boundary_end_signature_with_dirichlet_area
  exact ⟨H, P, hNE, hFG, h, h.isCompact_projected_closedCore, w, hw, hwN, hD, ha⟩

end LowDimensionalTopology.Geometry.Fuchsian
