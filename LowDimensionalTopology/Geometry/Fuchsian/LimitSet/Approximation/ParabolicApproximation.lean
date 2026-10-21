module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.ParabolicDirichletBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.ApproximationPolygons
@[expose] public section
noncomputable section
open Set
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
/-- The actual original parabolic fixed point is on a genuine Dirichlet boundary
and therefore is not a point of approximation. -/
theorem parabolic_fixedPoint_on_dirichlet_frontier_and_not_pointOfApproximation
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (ξ : ℂ) (hξ : f.val.val (ξ : OnePoint ℂ) = (ξ : OnePoint ℂ)) :
    (∃ w : P.domain.carrier, IsDirichletCenter P w ∧
      (ξ : OnePoint ℂ) ∈ frontier ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' dirichletDomain P w)) ∧
        ¬IsFuchsianPointOfApproximation P ξ := by
  obtain ⟨w, hw, hbound⟩ := parabolic_fixedPoint_dirichlet_boundary P f hf (ξ : OnePoint ℂ) hξ
  exact ⟨⟨w, hw, hbound⟩, fun hA =>
    pointOfApproximation_not_mem_convexPolygon_frontier P (dirichletDomain_isConvexFuchsianPolygon P w hw) ξ hA hbound⟩
end LowDimensionalTopology.Geometry.Fuchsian
