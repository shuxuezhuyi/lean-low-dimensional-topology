/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleDeveloping
public import LowDimensionalTopology.Geometry.Polygon.Development.ReflectionChamberDouble
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleProperness
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
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set
  Topology
open scoped UpperHalfPlane Pointwise

def closedTriangleConformalKernel (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    Subgroup (closedTrianglePoincarePairing T).Generated:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup.subgroupOf (closedTrianglePoincarePairing T).Generated

theorem closedTriangleConformalKernel_index (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (closedTriangleConformalKernel T).index=2 := by
  unfold closedTriangleConformalKernel
  rw [closedTrianglePoincarePairing_generated]
  exact triangleConformalKernel_index_two T

theorem closedTriangle_generators_odd (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (s : (closedTrianglePoincarePolygon T).Side) :
    (closedTrianglePoincarePairing T).generator s∉closedTriangleConformalKernel T := by
  change closedTrianglePoincareElement T s∉_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup
  exact halfPlaneLineReflectionIsometry_not_conformal _

theorem closedTriangle_generators_fix_side (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (s : (closedTrianglePoincarePolygon T).Side) (x : ℍ) (hx : x∈s.val) :
    (closedTrianglePoincarePairing T).generator s • x=x :=
  closedTrianglePoincareElement_fixed T s hx

/-- The original finite or ideal reciprocal-angle triangle's conformal-kernel orbit surface is the literal
boundary double of its actual physical closed chamber, excluding its ideal endpoints. No orbit, covering or FD premise is added. -/
def closedTriangleKernelOrbitDoubleHomeomorph (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) :
    (closedTrianglePoincarePairing T).ChamberDouble≃ₜ
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (closedTriangleConformalKernel T) ℍ := by
  let S:=closedTrianglePoincarePairing T
  let E:=closedTriangle_developingHomeomorph T ha hb hc
  let s:(closedTrianglePoincarePolygon T).Side:=closedTrianglePoincareSideEquiv T 0
  exact S.reflectionChamberOrbitHomeomorph (closedTriangleConformalKernel T)
    (closedTriangleConformalKernel_index T) (closedTriangle_generators_odd T)
    (closedTriangle_generators_fix_side T) (S.generator s)
    (closedTriangle_generators_odd T s) E (closedTriangle_developingHomeomorph_apply T ha hb hc)

/-- Changing only the nested subtype labels identifies the kernel with the original actual conformal group. -/
def closedTriangleConformalKernelEquiv (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    closedTriangleConformalKernel T≃*triangleConformalGroup T where
  toFun f:=⟨f.val.val,⟨by rw [←closedTrianglePoincarePairing_generated];exact f.val.property,f.property⟩⟩
  invFun f:=⟨⟨f.val,by rw [closedTrianglePoincarePairing_generated];exact f.property.1⟩,f.property.2⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_mul' _ _:=rfl

/-- The two genuine orbit relations coincide because the action-compatible actual groups differ only in subtype labels. -/
def closedTriangleKernelOrbitHomeomorph (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (closedTriangleConformalKernel T) ℍ≃ₜ
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (triangleConformalGroup T) ℍ :=
  Homeomorph.Quotient.congrRight (by
    intro x y
    constructor
    · rintro ⟨g,hg⟩
      exact ⟨closedTriangleConformalKernelEquiv T g,hg⟩
    · rintro ⟨g,hg⟩
      exact ⟨(closedTriangleConformalKernelEquiv T).symm g,hg⟩)

def closedTriangleConformalOrbitDoubleHomeomorph (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) :
    (closedTrianglePoincarePairing T).ChamberDouble≃ₜ
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (triangleConformalGroup T) ℍ :=
  (closedTriangleKernelOrbitDoubleHomeomorph T ha hb hc).trans
    (closedTriangleKernelOrbitHomeomorph T)

end LowDimensionalTopology.Geometry.Fuchsian
