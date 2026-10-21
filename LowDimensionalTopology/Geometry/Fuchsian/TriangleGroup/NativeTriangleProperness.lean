/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleIntegralDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane
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

/-- A native conformal subgroup's actual boundary homomorphism intertwines every physical point. -/
theorem nativeConformalSubgroupMobiusHom_action (H : Subgroup (ℍ≃ᵢℍ))
    (hH : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) (f : H) (z : ℍ) :
    (nativeConformalSubgroupMobiusHom H hH f).val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)=
      _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (f.val z) := by
  obtain ⟨A,hA⟩:=hH f.property
  have hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A∈H:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom A∈H
    rw [hA]
    exact f.property
  have he : f=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,hmem⟩:=Subtype.ext hA.symm
  rw [he,nativeConformalSubgroupMobiusHom_matrix]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A z

/-- Discrete genuine native conformal groups satisfy the compact-hit discontinuity condition,
including all elementary groups and every actual stabilizer. -/
theorem nativeConformalSubgroup_discontinuous (H : Subgroup (ℍ≃ᵢℍ))
    (hH : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) [DiscreteTopology H] : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous H ℍ := by
  let F:=nativeConformalSubgroupMobiusHom H hH
  let P:=nativeConformalSubgroup_halfPlaneData H hH
  intro K hK
  have hk:=P.discontinuous (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' K)
    (hK.image _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.continuous) (by
      rintro _ ⟨z,_,rfl⟩
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_range]
      exact mem_range_self z)
  let E : H→F.range:=F.rangeRestrict
  have hi : Function.Injective E:=by
    intro f g he
    exact (nativeConformalSubgroupMobiusHom_isometry H hH).injective (congrArg Subtype.val he)
  apply (Set.Finite.preimage hi.injOn hk).subset
  rintro f ⟨_,⟨z,hz,rfl⟩,hgz⟩
  refine ⟨_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (f.val z),⟨_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z,⟨z,hz,rfl⟩,?_⟩,
    ⟨f.val z,hgz,rfl⟩⟩
  exact nativeConformalSubgroupMobiusHom_action H hH f z

/-- The original even subgroup acts by the same physical isometries after changing its subtype labels. -/
def triangleConformalKernelEquiv (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    triangleConformalKernel T≃*triangleConformalGroup T where
  toFun f:=⟨f.val.val,⟨f.val.property,f.property⟩⟩
  invFun f:=⟨⟨f.val,f.property.1⟩,f.property.2⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_mul' _ _:=rfl

/-- A discrete original full reflection triangle group acts genuinely discontinuously,
without a non-elementarity or finite-area assumption. -/
theorem triangleReflectionGroup_discontinuous (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    [DiscreteTopology (triangleReflectionGroup T)] :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous (triangleReflectionGroup T) ℍ := by
  let : DiscreteTopology (triangleConformalGroup T):=
    (triangle_discrete_full_iff_conformal T).mp inferInstance
  have hd:=nativeConformalSubgroup_discontinuous (triangleConformalGroup T) inf_le_right
  have hk : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous (triangleConformalKernel T) ℍ:=
    hd.transport (triangleConformalKernelEquiv T).symm.toEquiv (Homeomorph.refl ℍ) (by
      intro f z
      rfl)
  let : (triangleConformalKernel T).FiniteIndex:=Subgroup.finiteIndex_iff.mpr
    (by rw [triangleConformalKernel_index_two];norm_num)
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discontinuous_of_finiteIndex (triangleConformalKernel T)
    (fun g=>g.val.continuous) hk

end LowDimensionalTopology.Geometry.Fuchsian
