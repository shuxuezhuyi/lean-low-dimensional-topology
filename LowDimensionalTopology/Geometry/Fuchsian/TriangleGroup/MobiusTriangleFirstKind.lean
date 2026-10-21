module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleNonElementary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
open scoped UpperHalfPlane

/-- The entire faithful Mobius image of any actual native triangle group is non-elementary. -/
theorem triangleMobiusImage_nonElementary (K:Subgroup (ℍ≃ᵢℍ))
    (hK:K≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) (ht:IsTriangleGroup K)
    (P:HalfPlaneFuchsianGroup (nativeConformalSubgroupMobiusHom K hK).range) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (nativeConformalSubgroupMobiusHom K hK).range := by
  obtain ⟨p,q,r,hp,hq,hr,T,ha,hb,hc,hEq⟩:=ht
  subst K
  exact closedTriangle_nonElementary T
    (ha ▸ triangleOrderAngle_isIntegral p hp)
    (hb ▸ triangleOrderAngle_isIntegral q hq)
    (hc ▸ triangleOrderAngle_isIntegral r hr) P

/-- Any original whole Mobius group geometrically conjugate to a triangle group is non-elementary, without an additional group-theoretic premise. -/
theorem mobiusTriangleGroup_nonElementary {H:Subgroup Mobius.complexMobiusGroup}
    (ht:IsMobiusTriangleGroup H) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H := by
  obtain ⟨K,hK,hTri,q,hq⟩:=ht
  let triangleFirstKindTriangleDiscrete:DiscreteTopology K:=by
    obtain ⟨p,r,s,hT⟩:=hTri
    exact hT.discrete
  let P:=nativeConformalSubgroup_halfPlaneData K hK
  have hNE:=triangleMobiusImage_nonElementary K hK hTri P
  intro he
  exact hNE (hq ▸ (_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_finiteOrbit_conjugation H q).mpr he)

/-- Every genuine geometric triangle group is of the first kind on every original invariant Fuchsian disc. -/
theorem mobiusTriangleGroup_actual_firstKind
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (ht:IsMobiusTriangleGroup H) : D.IsFirstKind :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.mobiusTriangleGroup_firstKind D (mobiusTriangleGroup_nonElementary ht) ht

end LowDimensionalTopology.Geometry.Fuchsian
