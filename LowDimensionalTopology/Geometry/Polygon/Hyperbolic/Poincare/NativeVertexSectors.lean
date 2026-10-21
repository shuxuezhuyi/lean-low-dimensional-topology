/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.Angle.PositiveCone
public import LowDimensionalTopology.Geometry.Polygon.Topology.Jordan.JordanCornerSectors
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeVertexRayGerms
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
open Set Filter Topology
open scoped UpperHalfPlane Complex.UnitDisc
/-- Every actual original Jordan geodesic vertex has the germ of a genuine
closed radial sector in its native isometric coordinate. Both reflex corners
and straight marked corners are included; no convexity or sector-shape hypothesis
is supplied by the caller. -/
theorem NativeJordanGeodesicPolygon.vertex_closed_sector_germ
    (J : NativeJordanGeodesicPolygon) (p : ℍ) (hp : p∈J.sideIntervals.vertices) :
    ∃a r : ℝ,0<r ∧r<Real.pi ∧∀ᶠz in 𝓝 (0 : 𝔻),
      z∈nativeAngularOriginChart p '' J.polygon.carrier ↔
        z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedAngularSector (a:AddCircle (2*Real.pi)) r := by
  let P:=J.polygon
  let D:=J.sideIntervals
  let F:=nativeAngularOriginChart p
  have hpB : p∈P.boundary := by
    obtain ⟨s,hs⟩:=mem_iUnion.mp hp
    exact P.side_subset_boundary s (D.endpoints_subset_side s hs)
  obtain ⟨u,v,hne,hB⟩:=D.vertex_origin_boundary_two_rays J.curve J.jordan J.boundary_eq p hp
  obtain ⟨hU,hV,hd,hUnion,h0U,h0V⟩:=J.geometry.origin_corner_regions p hpB
  have hComp : ∀ᶠz in 𝓝 (0 : 𝔻),z∈(F '' P.interior)∪(F '' P.carrierᶜ) ↔
      (z : ℂ)∉cornerNonnegativeRay u∪cornerNonnegativeRay v := by
    filter_upwards [hB] with z hz
    rw [hUnion]
    change (z∉F '' P.boundary) ↔¬(
      (∃r : ℝ,0≤r ∧(z : ℂ)=(r : ℂ)*(u : ℂ)) ∨
      (∃r : ℝ,0≤r ∧(z : ℂ)=(r : ℂ)*(v : ℂ)))
    exact not_congr hz
  obtain ⟨a,r,hr,hrπ,hGerm,_hEnds⟩:=disc_two_open_regions_corner_sector
    hU hV hd h0U h0V u v hne hComp
  refine ⟨a,r,hr,hrπ,?_⟩
  have hClosure : F '' P.carrier=closure (F '' P.interior) := by
    rw [J.geometry.carrier_closure,F.image_closure]
  filter_upwards [hGerm] with z hz
  change z∈F '' P.carrier ↔z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedAngularSector (a:AddCircle
    (2*Real.pi)) r
  rw [hClosure]
  exact hz

/-- The actual native origin chart preserves the original native hyperbolic distance. -/
theorem nativeAngularOriginChart_pathDist (p x y : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (nativeAngularOriginChart p x) (nativeAngularOriginChart p y)=dist x y := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry p.toSL2R⁻¹ x))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry p.toSL2R⁻¹ y))=dist x y
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry p.toSL2R⁻¹).dist_eq x y

/-- The genuine local closed-sector description holds on an actual positive
closed hyperbolic ball in the original polygon, with no supplied sector model. -/
theorem NativeJordanGeodesicPolygon.vertex_closed_sector_ball
    (J : NativeJordanGeodesicPolygon) (p : ℍ) (hp : p∈J.sideIntervals.vertices) :
    ∃a r R : ℝ,0<r ∧r<Real.pi ∧0<R ∧∀x : ℍ,dist x p≤R →
      (x∈J.polygon.carrier ↔
        nativeAngularOriginChart p x∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedAngularSector (a:AddCircle (2*Real.pi)) r) := by
  obtain ⟨a,r,hr,hrπ,hGerm⟩:=J.vertex_closed_sector_germ p hp
  let F:=nativeAngularOriginChart p
  have hT : Tendsto F (𝓝 p) (𝓝 (0 : 𝔻)):=
    (nativeAngularOriginChart_apply_self p) ▸F.continuous.continuousAt
  have hPull : ∀ᶠx in 𝓝 p,x∈J.polygon.carrier ↔
      F x∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedAngularSector (a:AddCircle (2*Real.pi)) r := by
    filter_upwards [hT.eventually hGerm] with x hx
    change (F x∈F '' J.polygon.carrier ↔F x∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedAngularSector
      (a:AddCircle (2*Real.pi)) r) at hx
    rwa [F.injective.mem_set_image] at hx
  obtain ⟨R,hR,hNear⟩:=Metric.eventually_nhds_iff_ball.mp hPull
  refine ⟨a,r,R/2,hr,hrπ,half_pos hR,?_⟩
  intro x hx
  exact hNear x (lt_of_le_of_lt hx (by linarith))

/-- Every neighborhood sees all and only the true directions of a radial sector,
so the genuine germ angle has its actual angular Haar measure, also for reflex sectors. -/
theorem discLocalAngularFraction_radial_sector (a : AddCircle (2*Real.pi)) (r : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngularFraction (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedAngularSector a r) 0=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure (_root_.LowDimensionalTopology.Geometry.Euclidean.polygonClosedDirectionArc a r) := by
  have hN (N : {N : Set 𝔻 //N∈𝓝 (0 : 𝔻)}) :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedAngularSector a r)∩N.val) 0=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure (_root_.LowDimensionalTopology.Geometry.Euclidean.polygonClosedDirectionArc a r) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction_zero]
    congr 1
    apply subset_antisymm
    · intro u hu
      have hs : u∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedAngularSector a r):=by
        obtain ⟨t,ht,_⟩:=hu
        exact ⟨t,ht⟩
      rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_closedAngularSector] at hs
    · intro u hu
      obtain ⟨n,hn⟩:=((_root_.LowDimensionalTopology.Geometry.Hyperbolic.tendsto_discRadialTestPoint u).eventually
        N.property).exists
      refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialTestRadius n,?_,hn⟩
      exact Or.inr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialTestRadius n,u,hu,rfl⟩
  apply le_antisymm
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngularFraction_le _ _ univ univ_mem).trans_eq (hN
    ⟨univ,univ_mem⟩)
  · apply le_iInf
    intro N
    exact (hN N).ge

/-- The width of the actual original vertex sector is exactly its original
local angular measure. It is strictly between zero and a full turn, including
nonconvex and straight original corners without a prescribed angle premise. -/
theorem NativeJordanGeodesicPolygon.vertex_localAngle_pos_lt
    (J : NativeJordanGeodesicPolygon) (p : ℍ) (hp : p∈J.sideIntervals.vertices) :
    0<nativeLocalAngle J.polygon.carrier p ∧
      nativeLocalAngle J.polygon.carrier p<2*Real.pi := by
  obtain ⟨a,r,hr,hrπ,hGerm⟩:=J.vertex_closed_sector_germ p hp
  have hEq : nativeLocalAngle J.polygon.carrier p=2*r := by
    unfold nativeLocalAngle
    rw [←nativeLocalAngularFraction_originChart,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discLocalAngularFraction_congr hGerm,discLocalAngularFraction_radial_sector]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure_closedArc_radians _ hr.le hrπ.le
  rw [hEq]
  constructor <;>linarith
end LowDimensionalTopology.Geometry.Polygon
