module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.StrongPolygonHalfPlaneGerms
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonBoundaryGerms
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- At an actual nonvertex original side point, the true Klein point is in the open segment
between its actual original endpoints, with no convexity condition on the polygon. -/
theorem finitePolygon_nonvertex_klein_openSegment
    {n : ℕ}
    (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) {i : Fin n} {x : ℍ}
    (hx : x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i)
    (hv : x∉range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x∈openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices i))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices (finRotate n i))) := by
  have hx' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (Q.vertices i) (Q.vertices (finRotate n i)):=hx
  have hseg : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x))∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (Q.vertices i) (Q.vertices (finRotate n i)) :=
    ⟨_,hx',rfl⟩
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion] at hseg
  have hne (j : Fin n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices j)≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x := by
    intro he
    apply hv
    refine ⟨j,?_⟩
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_injective
    exact (finitePolygonVertex_klein_coordinate Q hf j).trans he
  exact mem_openSegment_of_ne_left_right (hne i) (hne (finRotate n i)) hseg

/-- An actual original open Klein half-plane germ gives its genuine closed native carrier germ,
without imposing global convexity or selecting a local side by assumption. -/
theorem finitePolygon_native_closed_germ_of_open_cut
    {n : ℕ}
    (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (x : ℍ) {m : ℂ} {t : ℝ} (hm : m≠0)
    (hOpen : ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x),
      y∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' Q.interior ↔ inner ℝ m y<t) :
    ∃r : ℝ,0<r ∧ ∀w : ℍ,dist w x<r →
      (w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)≤t) := by
  have hClosed:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_closure_germ hOpen
  change ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x),
    y∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' Q.interior) ↔ y∈closure {y : ℂ|inner ℝ m y<t} at hClosed
  rw [complex_support_cut_closure hm t] at hClosed
  have hbody : closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' Q.interior)=Q.kleinBody:=Q.closedKlein_image_closedCarrier.symm
  rw [hbody] at hClosed
  have hNative:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous.continuousAt.eventually hClosed
  have hNative' : ∀ᶠw in 𝓝 x,
      w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)≤t := by
    filter_upwards [hNative] with w hw
    exact (finitePolygon_carrier_kleinBody_iff Q hf w).trans hw
  exact Metric.eventually_nhds_iff_ball.mp hNative'

/-- Every actual original side has a nonzero native supporting affine equation, independent
of convexity of the given original polygon. -/
theorem finitePolygon_native_side_equation {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) :
    ∃(m : ℂ)(t : ℝ),m≠0 ∧
      (∀w : ℍ,w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)=t) ∧
      inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices i))=t ∧
      inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices (finRotate n i)))=t := by
  let N:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i
  have hm : N.incenterNormal≠0 := by
    intro h
    have hh:=N.incenterNormal_lorentz_unit
    rw [h,norm_zero,zero_pow (by decide : 2≠0)] at hh
    nlinarith [sq_nonneg N.incenterOffset]
  have he (w : ℍ) : w∈N.carrier ↔ inner ℝ N.incenterNormal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)=N.incenterOffset := by
    rw [←N.incenter_affine_eq_zero_iff,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine,sub_eq_zero]
  refine ⟨N.incenterNormal,N.incenterOffset,hm,he,?_,?_⟩
  · rw [←finitePolygonVertex_klein_coordinate Q hf i]
    exact (he _).mp (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_left_mem Q hf i))
  · rw [←finitePolygonVertex_klein_coordinate Q hf (finRotate n i)]
    exact (he _).mp (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q i (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_right_mem Q hf i))

/-- Every genuine nonvertex original side point has an actual signed native half-plane
closed-carrier germ, for arbitrary original Jordan polygons without any global convexity hypothesis. -/
theorem finitePolygon_nonvertex_halfPlane_germ
    {n : ℕ}
    (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) {i : Fin n} {x : ℍ}
    (hx : x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i)
    (hv : x∉range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf)) :
    ∃(m : ℂ)(t : ℝ),m≠0 ∧
      (∀w : ℍ,w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)=t) ∧
      ∃r : ℝ,0<r ∧ ∀w : ℍ,dist w x<r →
        (w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)≤t) := by
  obtain ⟨m,t,hm,hLine,hleft,hright⟩:=finitePolygon_native_side_equation Q hf i
  let F : ℂ→ᵃ[ℝ]ℝ:=(innerSL ℝ m).toLinearMap.toAffineMap+AffineMap.const ℝ ℂ (-t)
  have hF (y : ℂ) : F y=inner ℝ m y-t:=by rfl
  have hopen:=finitePolygon_nonvertex_klein_openSegment Q hf hx hv
  have hB : ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x),y∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.boundary ↔ F y=0 := by
    filter_upwards [Q.klein_boundary_line_germ_edge i hopen] with y hy
    rw [hF,sub_eq_zero]
    exact hy.trans (polygonLineEquation_iff_support
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (Q.vertices_injective.ne (Q.next_ne_self i).symm))
      hm hleft hright y)
  obtain ⟨hI,hO,hd,hu,hFI,hFO⟩:=Q.klein_jordan_regions
  have hxB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.boundary := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,
      ←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (mem_iUnion.mpr ⟨i,hx⟩)
  have hxI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x∈frontier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' Q.interior):=by rwa [hFI]
  have hxO : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x∈frontier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' Q.complexOutside):=by rwa [hFO]
  rcases _root_.LowDimensionalTopology.Geometry.Polygon.complex_jordan_linear_boundary_interior_germ hI hO hd hu hxI hxO F hB with hpos | hneg
  · have hOpen : ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x),
        y∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' Q.interior ↔ inner ℝ (-m) y< -t := by
      filter_upwards [hpos] with y hy
      exact hy.trans (by rw [hF,inner_neg_left];constructor <;> intro h <;> linarith)
    refine ⟨-m,-t,neg_ne_zero.mpr hm,?_,finitePolygon_native_closed_germ_of_open_cut Q hf x
      (neg_ne_zero.mpr hm) hOpen⟩
    intro w
    rw [inner_neg_left,neg_inj,hLine]
  · have hOpen : ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x),
        y∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' Q.interior ↔ inner ℝ m y<t := by
      filter_upwards [hneg] with y hy
      rw [hF,sub_neg] at hy
      exact hy
    exact ⟨m,t,hm,hLine,finitePolygon_native_closed_germ_of_open_cut Q hf x hm hOpen⟩

end LowDimensionalTopology.Geometry.Fuchsian
