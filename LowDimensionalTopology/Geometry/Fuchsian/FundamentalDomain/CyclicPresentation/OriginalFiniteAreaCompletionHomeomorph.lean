/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalWordCompletionHomeomorph
/-!
# Finite-area quotients and their word completions

Finite-area fundamental-domain data construct a Dirichlet polygon, its
refined boundary word and all required parabolic fixers. The word realization
is homeomorphic to the original cusp completion, with the same genus identity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Filter Topology
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
local instance completionHomeomorphSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance completionHomeomorphSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- The actual original finite-area hypotheses construct all geometric witnesses, the unchanged faithful side-word completion homeomorphism and its genuine genus/Euler identity. Every witness is retained for subsequent actual angle and signature accounting. -/
theorem finite_area_original_word_completion_homeomorph {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D₀:FuchsianDisc H) (F:Set (fuchsianGeometricDomain D₀).carrier)
    (hF:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D₀).carrier (geometricModelArea D₀) F)
    (harea:geometricModelArea D₀ F≠⊤) :
    ∃w:(geometricDiscData D₀).domain.carrier,IsDirichletCenter (geometricDiscData D₀) w∧
    ∃hL:IsConvexFuchsianPolygon (geometricDiscData D₀) (dirichletDomain (geometricDiscData D₀) w),
    ∃_ha:(geometricDiscData D₀).area (dirichletDomain (geometricDiscData D₀) w)≠⊤,
    ∃J:PolygonalCircle,∃e:ZMod J.n≃OriginalRefinedSide hL,
    ∃_hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hL,v.carrier),
    ∃_hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hL,
    ∃_hs:∀i,J.edgeSegment i=(e
      i).planeCarrier,∃n:ℕ,∃S:_root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n,
    ∃_hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein (geometricDiscData D₀)
        (dirichletDomain (geometricDiscData D₀) w),
    ∃_hpar:∀u:Circle,(u:ℂ)∈fuchsianPolygonIdealBoundary (geometricDiscData D₀)
        (dirichletDomain (geometricDiscData D₀) w)→
      ∃f:geometricDiscGroup D₀,f≠1∧_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val∧
        f.val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),
      Nonempty ((originalCyclicPresentation J e).presentation.PolygonalRealization
        (originalCyclicPresentation J e).valid≃ₜFuchsianCuspCompletion D₀)∧
      ∃g,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (FuchsianCuspCompletion D₀) g∧
        _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic (originalCyclicPresentation J e).presentation=2-2*(g:ℤ) := by
  let P:=geometricDiscData D₀
  obtain ⟨w₀,hw₀,ha₀⟩:=finite_area_geometricDisc_dirichlet D₀ F hF harea
  obtain ⟨w,hw,hL,ha,hpar⟩:=finite_area_exists_dirichlet_all_ideal_parabolic
    (dirichletDomain_fundamental P w₀ hw₀) ha₀
  obtain ⟨J,e,hc,hv,hs⟩:=finite_area_original_cyclic_side_model hL ha
  obtain ⟨n,S,hr,_hint⟩:=finite_area_polygon_actual_cyclic_model hL ha
  exact ⟨w,hw,hL,ha,J,e,hc,hv,hs,n,S,hr,hpar,
    ⟨originalCyclicCompletionHomeomorph D₀ hL ha J hc hv e hs S hr hpar⟩,
    originalCyclicCompletion_genus_euler D₀ hL ha J hc hv e hs S hr hpar⟩

end LowDimensionalTopology.Geometry.Fuchsian
