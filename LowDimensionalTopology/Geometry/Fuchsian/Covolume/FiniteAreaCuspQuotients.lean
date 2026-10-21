/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaCuspCompactness
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspCompactPolygonQuotient
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped OnePoint UpperHalfPlane Complex.UnitDisc MatrixGroups Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance cuspQuotientSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance cuspQuotientSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual original finite-area Fuchsian action admits a literal finite geodesic polygon whose restricted original whole-group sphere orbit quotient is homeomorphic to its unchanged genuine all-cusp completion. The finite model, actual quotient relation, admissibility, chart estimates and orbit coverage are all derived from the original hypotheses. -/
theorem finite_area_fuchsianCuspCompletion_finite_polygon_quotient {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (F : Set (fuchsianGeometricDomain D).carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) F)
    (harea : geometricModelArea D F≠⊤) :
    ∃w : (geometricDiscData
      D).domain.carrier,∃n : ℕ,∃S : _root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n,
      IsDirichletCenter (geometricDiscData D) w∧
      IsConvexFuchsianPolygon (geometricDiscData D) (dirichletDomain (geometricDiscData D) w)∧
      S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein (geometricDiscData D)
        (dirichletDomain (geometricDiscData D) w)∧
      S.toDiscPolygon.interior=(geometricDiscData D).finiteCoordinate ''
        dirichletDomain (geometricDiscData D) w∧
      Nonempty (SphereSubsetOrbitQuotient H (originalFiniteClosedHull (geometricDiscNormalizer D) S.vertices)≃ₜ
        FuchsianCuspCompletion D) := by
  let P:=geometricDiscData D
  obtain ⟨w₀,hw₀,ha₀⟩:=finite_area_geometricDisc_dirichlet D F hF harea
  have hF₀:=dirichletDomain_fundamental P w₀ hw₀
  obtain ⟨w,hw,hpoly,ha,hpar⟩:=finite_area_exists_dirichlet_all_ideal_parabolic hF₀ ha₀
  let L:=dirichletDomain P w
  obtain ⟨n,S,hregion,hint⟩:=finite_area_polygon_actual_cyclic_model hpoly ha
  let K:=originalFiniteClosedHull (geometricDiscNormalizer D) S.vertices
  have hK:=finite_cyclic_hull_original_cusp_admissible D L S hregion hpar
  refine ⟨w,n,S,hw,hpoly,hregion,hint,?_⟩
  exact ⟨fuchsianCuspSubsetOrbitHomeomorph D K
    (originalFiniteClosedHull_isCompact _ _) hK
    (originalFiniteClosedHull_cusp_bounds D _ (geometricDiscNormalizer_image D) S.vertices)
    (finite_cyclic_hull_meets_original_augmented_orbit D hpoly.locallyFinite S hregion)⟩

end LowDimensionalTopology.Geometry.Fuchsian
