module
public import LowDimensionalTopology.Geometry.Fuchsian.LimitSet.Approximation.ApproximationRays
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonIdealBoundary
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
open scoped Pointwise

theorem fuchsian_pointOfApproximation_not_polygon_idealBoundary {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (ξ : ℂ) (hA : IsFuchsianPointOfApproximation P ξ) :
    ξ ∉ fuchsianPolygonIdealBoundary P D := by
  intro hξ
  obtain ⟨z, hz⟩ := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  obtain ⟨g, hg, hrate⟩ := hA.2 0
  have hnorm := fuchsian_limit_finite_norm_one P ξ hA.1
  let R := approximationCanonicalRay (P.finiteCoordinate z) ξ hnorm
  have hR := approximationCanonicalRay_endpoint (P.finiteCoordinate z) ξ hnorm
  have hsub := hD.ideal_ray_subset z hz R ξ hξ hR
  have hall := (disc_orbit_matrix_rate_all_basepoints_iff P g ξ).mpr hrate
  obtain ⟨K, hK, hmeet⟩ := (orbitMatrixRate_iff_rayBound_and_compactRayIntersection P g hg ξ hA.1).2.mp hall
    (P.finiteCoordinate z) R hR
  let K₀ := P.finiteCoordinate.symm '' K
  have hK₀ : IsCompact K₀ := hK.image P.finiteCoordinate.symm.continuous
  have hf := hD.locallyFinite.compact_hits_finite K₀ hK₀
  have hhit : range (fun n => (g n)⁻¹) ⊆
      {a : H | (fuchsianDomainTile P D a ∩ K₀).Nonempty} := by
    rintro a ⟨n, rfl⟩
    obtain ⟨x, hxR, hxK⟩ := hmeet n
    let X := P.finiteCoordinate.symm x
    have hgX : (g n) • X ∈ D := by
      have he : P.finiteCoordinate ((g n) • X) ∈ P.finiteCoordinate '' D := hsub hxR
      obtain ⟨y, hy, hyX⟩ := he
      exact P.finiteCoordinate.injective hyX ▸ hy
    refine ⟨X, ?_, ⟨x, hxK, rfl⟩⟩
    change X ∈ (g n)⁻¹ • closure D
    exact ⟨(g n) • X, subset_closure hgX, inv_smul_smul (g n) X⟩
  exact (infinite_range_of_injective (inv_injective.comp hg)) (hf.subset hhit)

/-- excludes the actual ambient Euclidean closure, hence its genuine boundary. -/
theorem fuchsian_pointOfApproximation_not_polygon_closure {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (ξ : ℂ) (hA : IsFuchsianPointOfApproximation P ξ) :
    (ξ : OnePoint ℂ) ∉ closure ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' D) := by
  intro hcl
  exact fuchsian_pointOfApproximation_not_polygon_idealBoundary P hD ξ hA
    ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D ξ).mpr
      ⟨fuchsian_limit_finite_norm_one P ξ hA.1, hcl⟩)

theorem pointOfApproximation_not_mem_convexPolygon_frontier {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (ξ : ℂ) (hA : IsFuchsianPointOfApproximation P ξ) :
    (ξ : OnePoint ℂ) ∉ frontier ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' D) :=
  fun h => fuchsian_pointOfApproximation_not_polygon_closure P hD ξ hA (frontier_subset_closure h)

end LowDimensionalTopology.Geometry.Fuchsian
