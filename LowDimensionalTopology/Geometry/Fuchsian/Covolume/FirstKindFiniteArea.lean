/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreFiniteness
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenConvexity
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

set_option backward.isDefEq.respectTransparency false in
theorem firstKind_finitelyGenerated_area_ne_top {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hfirst : P.asFuchsianDisc.IsFirstKind) (hFG : H.FG)
    {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D) : P.area D≠⊤ := by
  have hNE:=P.asFuchsianDisc.firstKind_nonElementary hfirst
  have hCore : fuchsianNielsenCore P hNE=univ := by
    ext x
    simp only [mem_univ,iff_true]
    change (x : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈P.asFuchsianDisc.nielsenRegion hNE
    rw [P.asFuchsianDisc.nielsenRegion_firstKind hNE hfirst]
    exact x.property
  have hArea:=finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD
  simpa only [fuchsianNielsenCoreArea,hCore,inter_univ] using hArea

end LowDimensionalTopology.Geometry.Fuchsian
