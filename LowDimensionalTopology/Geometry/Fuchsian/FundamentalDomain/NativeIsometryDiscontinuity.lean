/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Every actual discrete full half-plane group has a genuine discrete conformal part,
including elementary groups. -/
theorem fullHalfPlanePositiveData (H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexGeneralMobiusGroup)
    (hpres:∀f:H,f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) [DiscreteTopology H] :
    HalfPlaneFuchsianGroup (_root_.LowDimensionalTopology.Geometry.Mobius.fullGroupPositivePart H) where
  preserves f:=hpres ⟨_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusToFull f.val,f.property⟩
  discrete:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.full_discrete_iff_positivePart H).mp inferInstance

/-- Compact-set discontinuity of the actual full discrete group needs no non-elementarity
hypothesis. Its finite-index positive part and the whole compact-hit action are derived. -/
theorem fullHalfPlane_discrete_discontinuous (H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexGeneralMobiusGroup)
    (hpres:∀f:H,f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) [DiscreteTopology H] :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsFullMobiusDiscontinuousOn H _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  have hi:∀(g:H) x,x∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet→g • x∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    intro g x hx
    rw [←hpres g]
    exact mem_image_of_mem _ hx
  have hip:∀(g:_root_.LowDimensionalTopology.Geometry.Mobius.fullGroupPositivePart H) x,x∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet→g • x∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    intro g x hx
    exact hi ⟨_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusToFull g.val,g.property⟩ x hx
  let fullInvariantAction:MulAction H _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.invariantSubsetMulAction _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet hi
  let positiveInvariantAction:MulAction (_root_.LowDimensionalTopology.Geometry.Mobius.fullGroupPositivePart
    H) _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.invariantSubsetMulAction _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet hip
  have hpos:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn (_root_.LowDimensionalTopology.Geometry.Mobius.fullGroupPositivePart H) _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=
    (fullHalfPlanePositiveData H hpres).discontinuous
  have hposD:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous (_root_.LowDimensionalTopology.Geometry.Mobius.fullGroupPositivePart H) _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_iff_subtype _ _ hip).mp hpos
  have hk:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous (_root_.LowDimensionalTopology.Geometry.Mobius.fullGroupPositiveKernel H) _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=
    hposD.transport (_root_.LowDimensionalTopology.Geometry.Mobius.fullGroupPositivePartEquiv
      H).toEquiv (Homeomorph.refl _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) (fun _ _=>rfl)
  have hc(g:H):Continuous (fun x:_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=>g • x):=by
    apply Continuous.subtype_mk
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.fullMobiusContinuousMap
      g.val).continuous.comp continuous_subtype_val
  exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isFullMobiusDiscontinuousOn_iff_subtype H _ hi).mpr
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discontinuous_of_finiteIndex
      (_root_.LowDimensionalTopology.Geometry.Mobius.fullGroupPositiveKernel H) hc hk)

/-- Every actual discrete native hyperbolic-plane isometry subgroup has finite compact
transporters, allowing reflections and elementary groups without a supplied domain. -/
theorem nativeIsometrySubgroup_discontinuous (H:Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous H ℍ := by
  let : DiscreteTopology (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneImage
    H):=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlane_subgroup_discrete_iff H).mp inferInstance
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlane_discontinuous_iff H).mpr
    (fullHalfPlane_discrete_discontinuous (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneImage H)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneImage_preserves H))

theorem nativeIsometrySubgroup_properlyDiscontinuous (H:Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] :
    ProperlyDiscontinuousSMul H ℍ :=
  (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.isDiscontinuous_iff_properlyDiscontinuousSMul H
    ℍ).mp (nativeIsometrySubgroup_discontinuous H)

end LowDimensionalTopology.Geometry.Fuchsian
