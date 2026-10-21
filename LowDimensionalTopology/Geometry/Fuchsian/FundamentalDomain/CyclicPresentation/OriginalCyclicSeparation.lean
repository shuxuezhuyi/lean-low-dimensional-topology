/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation
/-!
# Separation and compactness of the word realization

The genus theorem for the cyclic presentation gives its polygonal realization
a Hausdorff topology and compactness.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise

theorem originalCyclicPresentation_t2Space {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) :
    T2Space ((originalCyclicPresentation J e).presentation.PolygonalRealization
      (originalCyclicPresentation J e).valid) := by
  obtain ⟨g,hg,_hχ⟩ := originalCyclicPresentation_genus J e
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.hasTopologicalGenus_t2Space hg

theorem originalCyclicPresentation_compactSpace {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    {hD : IsConvexFuchsianPolygon P D} (J : PolygonalCircle)
    (e : ZMod J.n≃OriginalRefinedSide hD) :
    CompactSpace ((originalCyclicPresentation J e).presentation.PolygonalRealization
      (originalCyclicPresentation J e).valid) := by
  obtain ⟨g,hg,_hχ⟩ := originalCyclicPresentation_genus J e
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.hasTopologicalGenus_compactSpace hg

end LowDimensionalTopology.Geometry.Fuchsian
