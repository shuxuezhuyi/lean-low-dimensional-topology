/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalWordCompletionHomeomorph
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Area.OriginalRawWeightedEuler
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
open LeanEval.Topology.ClassificationOfSurfaces.Moise
local instance completionWeightedAreaSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance completionWeightedAreaSphereBorel : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩

/-- Actual area of the original domain equals the actual area of every genuine normalized fundamental polygon. -/
theorem geometricDisc_fundamental_area_eq_original
    {H : Subgroup Mobius.complexMobiusGroup}
    (D₀ : FuchsianDisc H) (F : Set (fuchsianGeometricDomain D₀).carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D₀).carrier (geometricModelArea D₀) F)
    {L : Set (geometricDiscData D₀).domain.carrier}
    (hL : IsFuchsianFundamentalDomain (geometricDiscData D₀) L) :
    (geometricDiscData D₀).area L=geometricModelArea D₀ F := by
  rw [fuchsianFundamentalDomain_area_eq hL (finite_area_geometricDisc_fundamental_image D₀ F hF),
    (geometricDiscData D₀).area_apply _
      ((geometricDiscHomeomorph D₀).measurableEmbedding.measurableSet_image.mpr hF.isOpen.measurableSet),
    ←geometricModelArea_apply D₀ F hF.isOpen.measurableSet]

/-- The original true all-cusp completion, not merely a side word model, has the genus appearing in the actual weighted Euler area formula. -/
theorem originalCyclicCompletion_weightedEuler
    {H : Subgroup Mobius.complexMobiusGroup}
    (D₀ : FuchsianDisc H) {L : Set (geometricDiscData D₀).domain.carrier}
    (hL : IsConvexFuchsianPolygon (geometricDiscData D₀) L)
    (ha : (geometricDiscData D₀).area L≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide hL,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hL)
    (e : ZMod J.n≃OriginalRefinedSide hL) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier)
    {n : ℕ} (S : _root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n)
    (hr : S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein (geometricDiscData D₀) L)
    (hpar : ∀u : Circle,(u : ℂ)∈fuchsianPolygonIdealBoundary (geometricDiscData D₀) L→
      ∃f : geometricDiscGroup D₀,f≠1∧_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val∧
        f.val.val ((u : ℂ) : Mobius.ExtendedComplex)=((u : ℂ) : Mobius.ExtendedComplex)) :
    ∃g : ℕ,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (FuchsianCuspCompletion D₀) g ∧
      ((geometricDiscData D₀).area L).toReal=2*Real.pi*(2*(g : ℝ)-2+
        ∑q : Quotient (originalRawCornerSetoid J e),
          (1-originalRawCornerClassWeight hL ha J hc hv e hs q)) := by
  obtain ⟨g,hg,hχZ⟩:=originalCyclicPresentation_genus J e
  have hχ : (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic (originalCyclicPresentation J e).presentation : ℝ)=2-2*(g : ℝ):=
    by exact_mod_cast hχZ
  obtain ⟨G⟩:=hg
  refine ⟨g,⟨(originalCyclicCompletionHomeomorph D₀ hL ha J hc hv e hs S hr hpar).symm.trans G⟩,?_⟩
  rw [originalRawCornerClasses_weightedEuler hL ha J hc hv e hs,hχ]
  ring

/-- Original finite density area constructs an actual normalized polygon and the true completion genus together with its exact weighted corner formula. -/
theorem finite_area_original_completion_weightedEuler
    {H : Subgroup Mobius.complexMobiusGroup}
    (D₀ : FuchsianDisc H) (F : Set (fuchsianGeometricDomain D₀).carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D₀).carrier (geometricModelArea D₀) F)
    (harea : geometricModelArea D₀ F≠⊤) :
    ∃w : (geometricDiscData D₀).domain.carrier,
    ∃hL : IsConvexFuchsianPolygon (geometricDiscData D₀) (dirichletDomain (geometricDiscData D₀) w),
    ∃ha : (geometricDiscData D₀).area (dirichletDomain (geometricDiscData D₀) w)≠⊤,
    ∃J : PolygonalCircle,∃e : ZMod J.n≃OriginalRefinedSide hL,
    ∃hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide hL,v.carrier),
    ∃hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hL,
    ∃hs : ∀i,J.edgeSegment i=(e i).planeCarrier,
    ∃g : ℕ,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (FuchsianCuspCompletion D₀) g ∧
      (geometricModelArea D₀ F).toReal=2*Real.pi*(2*(g : ℝ)-2+
        ∑q : Quotient (originalRawCornerSetoid J e),
          (1-originalRawCornerClassWeight hL ha J hc hv e hs q)) := by
  let P:=geometricDiscData D₀
  obtain ⟨w₀,hw₀,ha₀⟩:=finite_area_geometricDisc_dirichlet D₀ F hF harea
  obtain ⟨w,_hw,hL,ha,hpar⟩:=finite_area_exists_dirichlet_all_ideal_parabolic
    (dirichletDomain_fundamental P w₀ hw₀) ha₀
  obtain ⟨J,e,hc,hv,hs⟩:=finite_area_original_cyclic_side_model hL ha
  obtain ⟨n,S,hr,_hint⟩:=finite_area_polygon_actual_cyclic_model hL ha
  obtain ⟨g,hg,hA⟩:=originalCyclicCompletion_weightedEuler D₀ hL ha J hc hv e hs S hr hpar
  refine ⟨w,hL,ha,J,e,hc,hv,hs,g,hg,?_⟩
  rwa [geometricDisc_fundamental_area_eq_original D₀ F hF hL.locallyFinite.fundamental] at hA

end LowDimensionalTopology.Geometry.Fuchsian
