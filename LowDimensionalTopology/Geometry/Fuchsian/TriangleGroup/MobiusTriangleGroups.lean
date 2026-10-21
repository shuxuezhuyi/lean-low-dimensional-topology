/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ModularTriangleExample
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteDilationGroups
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
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

/-- A genuine geometric triangle group in the original Mobius group: a Mobius
conjugate of the entire actual native conformal triangle group image. -/
def IsMobiusTriangleGroup (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  ∃K : Subgroup (ℍ≃ᵢℍ),∃hK : K≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup,
    IsTriangleGroup K ∧ ∃q : Mobius.complexMobiusGroup,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H=(nativeConformalSubgroupMobiusHom K hK).range

theorem isMobiusTriangleGroup_native_image (K : Subgroup (ℍ≃ᵢℍ))
    (hK : K≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (ht : IsTriangleGroup K) :
    IsMobiusTriangleGroup (nativeConformalSubgroupMobiusHom K hK).range := by
  refine ⟨K,hK,ht,1,?_⟩
  ext f
  simp [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff]

theorem IsMobiusTriangleGroup.conjugation
    {H : Subgroup Mobius.complexMobiusGroup}
    (ht : IsMobiusTriangleGroup H) (q : Mobius.complexMobiusGroup) :
    IsMobiusTriangleGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) := by
  obtain ⟨K,hK,ht,r,hr⟩:=ht
  refine ⟨K,hK,ht,r*q⁻¹,?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose]
  have he : (r*q⁻¹)*q=r := by group
  rwa [he]

theorem isMobiusTriangleGroup_of_conjugate
    (H : Subgroup Mobius.complexMobiusGroup)
    (q : Mobius.complexMobiusGroup) (ht : IsMobiusTriangleGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H)) :
    IsMobiusTriangleGroup H := by
  obtain ⟨K,hK,ht,r,hr⟩:=ht
  refine ⟨K,hK,ht,r*q,?_⟩
  rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose]
  exact hr

end LowDimensionalTopology.Geometry.Fuchsian
