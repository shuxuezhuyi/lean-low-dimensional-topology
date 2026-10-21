/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicCompletionMap
/-!
# A word model mapping onto the finite-area completion

A finite-area quotient supplies a refined Dirichlet boundary word with genus
and Euler data. Its realization maps continuously and surjectively onto the
original cusp completion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces.Moise
local instance completionWordSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance completionWordSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- Every actual original finite-area Fuchsian quotient admits an unchanged finite side-word realization of genuine genus, with a continuous surjection onto its unique all-cusp completion. All actual polygon, ideal-fixer and side-compatibility inputs are derived; no completion homeomorphism is asserted here. -/
theorem finite_area_original_word_completion_map {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D₀:FuchsianDisc H) (F:Set (fuchsianGeometricDomain D₀).carrier)
    (hF:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D₀).carrier (geometricModelArea D₀) F)
    (harea:geometricModelArea D₀ F≠⊤) :
    ∃w:(geometricDiscData D₀).domain.carrier,∃hL:IsConvexFuchsianPolygon (geometricDiscData D₀)
        (dirichletDomain (geometricDiscData D₀) w),∃J:PolygonalCircle,
      ∃e:ZMod J.n≃OriginalRefinedSide hL,
      IsDirichletCenter (geometricDiscData D₀) w∧
      J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
        hL,v.carrier)∧
      (∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
        originalRefinedEndpointSet hL)∧
      (∀i,J.edgeSegment i=(e i).planeCarrier)∧
      ∃g,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus ((originalCyclicPresentation J
        e).presentation.PolygonalRealization
          (originalCyclicPresentation J e).valid) g∧
        _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic (originalCyclicPresentation J
          e).presentation=2-2*(g:ℤ)∧
        ∃f:C((originalCyclicPresentation J e).presentation.PolygonalRealization
          (originalCyclicPresentation J e).valid,FuchsianCuspCompletion D₀),Function.Surjective f := by
  let P:=geometricDiscData D₀
  obtain ⟨w₀,hw₀,ha₀⟩:=finite_area_geometricDisc_dirichlet D₀ F hF harea
  obtain ⟨w,hw,hL,ha,hpar⟩:=finite_area_exists_dirichlet_all_ideal_parabolic
    (dirichletDomain_fundamental P w₀ hw₀) ha₀
  obtain ⟨J,e,hc,hv,hs⟩:=finite_area_original_cyclic_side_model hL ha
  obtain ⟨n,S,hr,_hint⟩:=finite_area_polygon_actual_cyclic_model hL ha
  obtain ⟨g,hg,hχ⟩:=originalCyclicPresentation_genus J e
  exact ⟨w,hL,J,e,hw,hc,hv,hs,g,hg,hχ,
    ⟨originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar,
      continuous_originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar⟩,
    originalCyclicCompletionMap_surjective D₀ hL ha J hc hv e hs S hr hpar⟩

end LowDimensionalTopology.Geometry.Fuchsian
