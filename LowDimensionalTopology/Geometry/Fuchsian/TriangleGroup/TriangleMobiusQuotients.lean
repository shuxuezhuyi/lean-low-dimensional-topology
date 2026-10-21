/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleOrbitDouble
public import LowDimensionalTopology.Geometry.Fuchsian.Geodesic.SimpleClosedCurves
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDiscreteness
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
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set
  Topology
open scoped UpperHalfPlane

def closedTriangleMobiusGroup (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : Subgroup Mobius.complexMobiusGroup:=
  (nativeConformalSubgroupMobiusHom (triangleConformalGroup T) inf_le_right).range

def closedTriangleMobiusEquiv (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : triangleConformalGroup T≃*closedTriangleMobiusGroup T :=
  MonoidHom.ofInjective (nativeConformalSubgroupMobiusHom_isometry _ _).injective

theorem closedTriangleMobiusData (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) : HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T) := by
  let : DiscreteTopology (triangleConformalGroup T):=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.conformal_discrete_of_integral_angles T ha hb hc
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.nativeConformalSubgroup_halfPlaneData _ _

/-- The actual native and original sphere actions coincide through the faithful full group image. -/
theorem closedTriangleMobiusEquiv_action
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (g:triangleConformalGroup T)
    (z:ℍ) :
    (closedTriangleMobiusEquiv T g).val.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)=
      _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (g•z) :=
  nativeConformalSubgroupMobiusHom_action _ _ g z

/-- The genuine native triangle orbit and the actual full Mobius open-domain quotient have the same topology. -/
def closedTriangleMobiusOrbitHomeomorph (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (triangleConformalGroup T) ℍ≃ₜ_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.asFuchsianDisc.domain :=
  Homeomorph.Quotient.congr _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneOpenModelHomeomorph (by
    intro x y
    constructor
    · rintro ⟨g,hg⟩
      refine ⟨closedTriangleMobiusEquiv T g,Subtype.ext ?_⟩
      exact (closedTriangleMobiusEquiv_action T g y).trans (congrArg _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint hg)
    · rintro ⟨g,hg⟩
      refine ⟨(closedTriangleMobiusEquiv T).symm g,?_⟩
      apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
      have h:=congrArg (fun p:P.asFuchsianDisc.domain.carrier=>p.val) hg
      change g.val.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint y)=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint x at h
      have he:=closedTriangleMobiusEquiv_action T ((closedTriangleMobiusEquiv T).symm g) y
      rw [(closedTriangleMobiusEquiv T).apply_symm_apply] at he
      exact he.symm.trans h)

end LowDimensionalTopology.Geometry.Fuchsian
