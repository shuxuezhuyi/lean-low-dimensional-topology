/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleCompactDouble
public import Mathlib.Analysis.Convex.Strict.Extreme
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
  Set
  Topology
open scoped UpperHalfPlane Complex.UnitDisc

/-- Strict convexity of the actual closed Klein disc leaves only original vertices on the ideal circle. -/
theorem closedDiscTriangle_ideal_point_is_vertex
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle)
    (p:𝕔𝔻)
    (hp:p∈T.closedCarrier) (hi:‖(p:ℂ)‖=1) : p=T.a ∨p=T.b ∨p=T.c := by
  let V:Set ℂ:={_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.b,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.c}
  have hpH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈convexHull ℝ V:=by
    have h:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' T.closedCarrier:=mem_image_of_mem _ hp
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.closedCarrier,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvexHull_klein_image] at h
    simpa only [image_insert_eq,image_singleton] using h
  have hV:V⊆Metric.closedBall (0:ℂ) 1:=by
    intro z hz
    rcases hz with rfl|rfl|rfl
    all_goals exact mem_closedBall_zero_iff.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein _).norm_le_one
  have hHull:convexHull ℝ V⊆Metric.closedBall (0:ℂ) 1:=convexHull_min hV (convex_closedBall _ _)
  have hNorm:‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p‖=1:=by
    change ‖(_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein p:ℂ)‖=1
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed p hi,hi]
  have hE:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈(Metric.closedBall (0:ℂ) 1).extremePoints ℝ:=
    StrictConvexSpace.sphere_subset_extremePoints_closedBall (0:ℂ) one_ne_zero (mem_sphere_zero_iff_norm.mpr hNorm)
  have hEH:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p∈(convexHull ℝ V).extremePoints ℝ:=
    ⟨hpH,fun _ hx _ hy he=>hE.2 (hHull hx) (hHull hy) he⟩
  have hMem:=extremePoints_convexHull_subset hEH
  rcases hMem with h|h|h
  · exact Or.inl (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective h)
  · exact Or.inr (Or.inl (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective h))
  · exact Or.inr (Or.inr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective h))

/-- The real ideal boundary of the original compact physical triangle is a finite subset of its actual vertices. -/
theorem closedTrianglePhysical_ideal_boundary_finite
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    {p:closedTrianglePhysicalCompactRegion T|‖p.val‖=1}.Finite := by
  have hS: {z:ℂ|z∈closedTrianglePhysicalCompactRegion T ∧‖z‖=1}⊆
      {(T.toDiscTriangle.a:ℂ),(T.toDiscTriangle.b:ℂ),(T.toDiscTriangle.c:ℂ)}:=by
    rintro z ⟨⟨p,hp,rfl⟩,hi⟩
    rcases closedDiscTriangle_ideal_point_is_vertex T.toDiscTriangle p hp hi with rfl|rfl|rfl
    all_goals simp
  have hF: {z:ℂ|z∈closedTrianglePhysicalCompactRegion T ∧‖z‖=1}.Finite:=
    (toFinite _).subset hS
  have hPre:=hF.preimage (f:=fun p:closedTrianglePhysicalCompactRegion T=>p.val) Subtype.val_injective.injOn
  exact hPre.subset (fun p hp=>⟨p.property,hp⟩)

/-- An actual ideal point belongs to the true side boundary of the compact physical region. -/
theorem closedTrianglePhysical_ideal_frontier (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p:closedTrianglePhysicalCompactRegion T) (hi:‖p.val‖=1) :
    p.val∈frontier (closedTrianglePhysicalCompactRegion T) := by
  rw [frontier,(T.toDiscTriangle.complexClosedCarrier_isCompact.isClosed).closure_eq]
  refine ⟨p.property,?_⟩
  intro hp
  have hN:=mem_ball_zero_iff.mp (T.toDiscTriangle.complexInterior_subset_disc hp)
  rw [hi] at hN
  exact lt_irrefl _ hN

/-- Each genuine ideal endpoint contributes exactly one point after the actual boundary gluing. -/
def closedTrianglePhysicalIdealPoint (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p:{p:closedTrianglePhysicalCompactRegion T|‖p.val‖=1}) : closedTrianglePhysicalCompactDouble T :=
  Quotient.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleSetoid _ _) (false,p.val)

theorem closedTrianglePhysicalIdealPoint_injective
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    Function.Injective (closedTrianglePhysicalIdealPoint T) := by
  intro p q h
  apply Subtype.ext
  exact congrArg _root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleBase h

/-- The exact complement of the actual old physical quotient consists of these genuine ideal endpoints. -/
theorem closedTrianglePhysicalDoubleInclusion_complement
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (range (closedTrianglePhysicalDoubleInclusion T))ᶜ=range (closedTrianglePhysicalIdealPoint T) := by
  rw [closedTrianglePhysicalDoubleInclusion_range]
  ext q
  induction q using Quotient.inductionOn with
  | h a =>
    constructor
    · intro h
      change ¬‖a.2.val‖<1 at h
      have hp:‖a.2.val‖=1:=le_antisymm
        (mem_closedBall_zero_iff.mp (T.toDiscTriangle.complexClosedCarrier_subset_closedBall a.2.property))
        (not_lt.mp h)
      refine ⟨⟨a.2,hp⟩,?_⟩
      apply Quotient.sound
      exact ⟨rfl,Or.inr (closedTrianglePhysical_ideal_frontier T a.2 hp)⟩
    · rintro ⟨p,hp⟩
      have he:a.2=p.val:=(congrArg _root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleBase hp).symm
      change ¬‖a.2.val‖<1
      have hn:‖a.2.val‖=1:=by
        rw [he]
        exact p.property
      rw [hn]
      exact lt_irrefl 1


theorem closedTriangleConformalOrbitCompactInclusion_complement
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) :
    (range (closedTriangleConformalOrbitCompactInclusion T ha hb hc))ᶜ=
      range (closedTrianglePhysicalIdealPoint T) := by
  rw [closedTriangleConformalOrbitCompactInclusion_range,
    ←closedTrianglePhysicalDoubleInclusion_range,closedTrianglePhysicalDoubleInclusion_complement]

theorem closedTriangleConformalOrbitCompactInclusion_complement_finite
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) :
    (range (closedTriangleConformalOrbitCompactInclusion T ha hb hc))ᶜ.Finite := by
  rw [closedTriangleConformalOrbitCompactInclusion_complement]
  let : Finite {p:closedTrianglePhysicalCompactRegion T|‖p.val‖=1}:=
    (closedTrianglePhysical_ideal_boundary_finite T).to_subtype
  exact finite_range _

end LowDimensionalTopology.Geometry.Fuchsian
