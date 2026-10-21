/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleEllipticAxisSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Hyperbolic.NonsimpleHyperbolicDisplacement
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/--
For the actual original geometric disc and the actual
whole-disc displacement infimum. Both the simple and nonsimple axis cases are proved.
-/
theorem hyperbolic_elliptic_pair_displacement_ge_inv_sqrt_eight {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/Real.sqrt 8≤_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D f g := by
  by_cases hs:IsSimple H f.val
  · exact fuchsian_simple_hyperbolic_elliptic_displacementM_eighth D f g hf hg hs hne
  · exact fuchsian_nonsimple_displacementM_eighth D f g hf hs

end LowDimensionalTopology.Geometry.Fuchsian
