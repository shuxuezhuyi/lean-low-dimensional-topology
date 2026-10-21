/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawCornerWeights
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicRawArea
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Topology
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
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical

theorem originalRawCornerClasses_weightedEuler
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    (P.area D).toReal=2*Real.pi*(-(_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic
      (originalCyclicPresentation J e).presentation : ℝ)+
      ∑q : Quotient (originalRawCornerSetoid J e),
        (1-originalRawCornerClassWeight hD ha J hc hv e hs q)) := by
  have h:=originalCyclicDiscPolygon_area_rawCorners hD ha J hv e hs
  rw [originalRawCornerClasses_total_angle hD ha J hc hv e hs] at h
  have hCard : (∑q : Quotient (originalRawCornerSetoid J e),(1 : ℝ))=
      (Nat.card (Quotient (originalRawCornerSetoid J e)) : ℝ) := by
    simp [Nat.card_eq_fintype_card]
  rw [Finset.sum_sub_distrib,hCard]
  linear_combination h

/-- The actual original polygon supplies its own faithful word genus and the exact weighted Euler area formula, without assigned signature or genus data. -/
theorem finite_area_original_raw_weightedEuler
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) :
    ∃J : PolygonalCircle,∃e : ZMod J.n≃OriginalRefinedSide hD,
    ∃hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide hD,v.carrier),
    ∃hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD,
    ∃hs : ∀i,J.edgeSegment i=(e i).planeCarrier,
    ∃g : ℕ,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus
      ((originalCyclicPresentation J e).presentation.PolygonalRealization
        (originalCyclicPresentation J e).valid) g ∧
      (P.area D).toReal=2*Real.pi*(2*(g : ℝ)-2+
        ∑q : Quotient (originalRawCornerSetoid J e),
          (1-originalRawCornerClassWeight hD ha J hc hv e hs q)) := by
  obtain ⟨J,e,hc,hv,hs,g,hg,hχZ⟩:=finite_area_original_cyclic_word_genus hD ha
  have hχ : (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic (originalCyclicPresentation J e).presentation : ℝ)=2-2*(g : ℝ) :=
    by exact_mod_cast hχZ
  refine ⟨J,e,hc,hv,hs,g,hg,?_⟩
  rw [originalRawCornerClasses_weightedEuler hD ha J hc hv e hs,hχ]
  ring

end LowDimensionalTopology.Geometry.Fuchsian
