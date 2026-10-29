module

public import LowDimensionalTopology.Geometry.Fuchsian.PantsCoreBoundaryComponents
public import LowDimensionalTopology.Geometry.Fuchsian.PantsPrimitiveAxisGeodesic

/-!
# Actual single-traversal geodesics on the original Nielsen-core frontier

The existing boundary-axis theorem supplies a full stabilizer generator. Its
actual axis is transported through the canonical Cayley chart, then the same
primitive matrix's whole period supplies the original closed geodesic.
-/

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups Pointwise

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces

/-- Every actual finitely generated Nielsen boundary line projects to a
single-traversal original closed geodesic on the unchanged quotient. -/
theorem nielsenBoundaryLine_original_simple_closed_geodesic
    {H : Subgroup complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hno : ∀ g ∈ H, g ≠ 1 → ¬ MobiusElliptic g)
    (hNE : DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    (L : DiscLine) (hL : L ∈ nielsenBoundaryDiscLineFamily P hNE) :
    ∃ q : OriginalClosedGeodesic (threeBoundaryQuotientModel P hno),
      Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → MobiusDomainQuotient P.domain) ∧
      range q.curve = mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' L.carrier) := by
  obtain ⟨f, hf, M₀, hM₀⟩ :=
    finitelyGenerated_nielsen_boundary_line_boundaryHyperbolic P hNE hFG L hL
  obtain ⟨⟨g, hg, hgen⟩, _⟩ := boundaryHyperbolic_axis_quotient_circle hNE hf M₀
  have hgK : g ∈ mobiusSetStabilizer H M₀.carrier := by
    rw [hgen]
    exact Subgroup.mem_zpowers g
  have hgH : g ∈ H := hgK.1
  obtain ⟨M₁⟩ := P.asFuchsianDisc.axisModel_exists g hgH hg
  have hfix : g.val '' ((Subtype.val : P.domain.carrier → ExtendedComplex) ''
      (P.finiteCoordinate.symm '' L.carrier)) =
        (Subtype.val : P.domain.carrier → ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier) := by
    rw [← hM₀]
    exact hgK.2
  have hM₁ := nielsenBoundary_hyperbolic_invariant_line_axis P hNE ⟨g, hgH⟩ hg M₁ L hL hfix
  let c := cayleyMobius⁻¹
  have hc : c.val '' P.asFuchsianDisc.carrier = openHalfPlaneSet := by
    change cayleyMobius.val.symm '' extendedUnitDisc = openHalfPlaneSet
    rw [← cayleyMobius_image_openHalfPlane, cayleyMobius.val.symm_image_image]
  have hpres : (c * g * c⁻¹).val '' openHalfPlaneSet = openHalfPlaneSet := by
    rw [← hc, Mobius.stableAxis_conjugate_image, c.val.injective.image_injective.eq_iff]
    exact P.image_eq ⟨g, hgH⟩
  obtain ⟨A, hAproj⟩ := mobius_preserves_halfPlane_exists_SL _ hpres
  have hAH : MobiusHyperbolic (realSLMobius A) := by
    rw [hAproj]
    exact Mobius.mobiusHyperbolic_conjugation_forward g c hg
  have hAn := hAH.1.1
  have ht := (realSLMobius_hyperbolic_iff A hAn).mp hAH
  have hcanon : cayleyMobius * realSLMobius A * cayleyMobius⁻¹ = g := by
    rw [hAproj]
    dsimp only [c]
    group
  have hchart : c.val '' M₁.carrier =
      halfPlaneBoundaryPoint '' (hHyperbolicAxis A hAn ht).carrier :=
    boundary_axis_carrier_image_in_chart M₁ c hc A hAproj hAn ht
  have hphysical : cayleyMobius.val ''
      (halfPlaneBoundaryPoint '' (hHyperbolicAxis A hAn ht).carrier) =
        (Subtype.val : P.domain.carrier → ExtendedComplex) '' (P.finiteCoordinate.symm '' L.carrier) := by
    rw [← hchart]
    change cayleyMobius.val '' (cayleyMobius.val.symm '' M₁.carrier) = _
    rw [cayleyMobius.val.image_symm_image]
    exact hM₁
  have hstable : MobiusStableSet H (cayleyMobius.val ''
      (halfPlaneBoundaryPoint '' (hHyperbolicAxis A hAn ht).carrier)) := by
    rw [hphysical, ← hM₀]
    exact boundaryHyperbolic_axis_stable hNE hf M₀
  have hprimitive : mobiusSetStabilizer H (cayleyMobius.val ''
      (halfPlaneBoundaryPoint '' (hHyperbolicAxis A hAn ht).carrier)) =
        Subgroup.zpowers (cayleyMobius * realSLMobius A * cayleyMobius⁻¹) := by
    rw [hphysical, hcanon, ← hM₀]
    exact hgen
  obtain ⟨q, _hcov, hcircle, htrace⟩ :=
    exists_original_simple_closed_geodesic_of_physical_primitive_axis P hno A hAn ht
      (by rw [hcanon]; exact hgH) hstable hprimitive
  have hline : P.finiteCoordinate.symm ''
      (halfPlaneToDisc '' (hHyperbolicAxis A hAn ht).carrier) = P.finiteCoordinate.symm '' L.carrier := by
    apply Subtype.val_injective.image_injective
    calc
      _ = cayleyMobius.val '' (halfPlaneBoundaryPoint '' (hHyperbolicAxis A hAn ht).carrier) := by
        simp only [image_image]
        apply image_congr
        intro z _hz
        have he := discFiniteHomeomorph_symm_coe (halfPlaneToDisc z)
        change _ = cayleyMobius.val (((z : ℂ) : ExtendedComplex))
        rw [cayleyMobius_apply, extendedCayley_halfPlane]
        exact he
      _ = _ := hphysical
  exact ⟨q, hcircle, htrace.trans (congrArg (Set.image (mobiusDomainProjection P.domain)) hline)⟩

/-- The actual three-end signature gives simple original closed geodesics on
every entire frontier component of its own projected open Nielsen core. -/
theorem threeBoundaryOpenCore_geodesicFrontier
    {H : Subgroup complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {hNE : DiscreteGroups.IsNonElementary H} {hFG : H.FG}
    (h : HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3) :
    ∀ x ∈ frontier (threeBoundaryOpenCore P hNE),
      ∃ q : OriginalClosedGeodesic
          (threeBoundaryQuotientModel P (noElliptic_of_threeBoundarySignature h)),
        Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → MobiusDomainQuotient P.domain) ∧
        range q.curve = connectedComponentIn (frontier (threeBoundaryOpenCore P hNE)) x := by
  let hno := noElliptic_of_threeBoundarySignature h
  intro x hx
  obtain ⟨w, hw, hwN, J, hc, hv, _n, _S, _hr, _hg, _ho, _hp, _hb⟩ := h
  let hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  let hfin := finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
  let hwD := dirichletDomain_center_mem P w hw
  rw [← nielsenProjectedBoundaryCycles_eq_openCore_frontier hD hNE hFG hfin w hwD hwN J hc hv] at hx
  obtain ⟨c, hxc⟩ := mem_iUnion.mp hx
  obtain ⟨b, rfl⟩ := Quotient.exists_rep c
  let side := nielsenCyclicBoundaryUnpairedSide hD hNE hFG hfin w hwD hwN J hc hv b
  obtain ⟨q, hcircle, htrace⟩ :=
    nielsenBoundaryLine_original_simple_closed_geodesic P hno hNE hFG side.val side.property.1
  refine ⟨q, hcircle, htrace.trans ?_⟩
  exact (nielsenProjectedBoundaryCycle_eq_completeLine hD hNE hFG hfin w hwD hwN J hc hv b).symm.trans
    (nielsenProjectedBoundaryCycle_eq_connectedComponentIn hD hNE hFG hfin w hwD hwN J hc hv
      (Quotient.mk _ b) hxc).symm

end LowDimensionalTopology.Geometry.Fuchsian
