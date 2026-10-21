/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Polygon.DiscPolygonLocalConvexity
public import LowDimensionalTopology.Geometry.Polygon.Support.CyclicDiscPolygonSupports
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.LambertPolygonAdapters
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Strict.Extreme
/-! # Actual global support equations of genuine convex disc polygons

Separation at each true edge midpoint constructs genuine global supporting lines.
Distinct adjacent sides make finite vertices extreme; ideal vertices are extreme
by strict convexity of the actual closed unit disc. Extreme cyclic vertices then
supply strict support data whose resulting actual Jordan polygon equals the input.
No metric identity or numerical polygon angle is a support-data assumption.
-/
@[expose] public section
namespace LowDimensionalTopology.Geometry.Polygon
open Set InnerProductGeometry
open scoped Complex.UnitDisc Topology
noncomputable section

def DiscPolygon.kleinBody {n : ℕ} (P : DiscPolygon n) : Set ℂ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.closedCarrier

theorem DiscPolygon.vertex_mem_boundary {n : ℕ} (P : DiscPolygon n) (i : Fin n) :
    P.vertices i∈P.boundary := by
  exact Set.mem_iUnion.mpr ⟨i,closedModelDiscHSegment_left_mem _ _⟩

theorem DiscPolygon.vertex_mem_closedCarrier {n : ℕ} (P : DiscPolygon n) (i : Fin n) :
    P.vertices i∈P.closedCarrier := P.boundary_subset_closedCarrier (P.vertex_mem_boundary i)

theorem DiscPolygon.kleinBody_convex {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex) :
    Convex ℝ P.kleinBody := by
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvex_iff_klein_convex
    P.closedCarrier).mp (P.closedCarrier_hConvex_iff.mpr hc)

theorem DiscPolygon.klein_inside_frontier {n : ℕ} (P : DiscPolygon n) :
    frontier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' P.boundary := by
  rw [P.klein_image_interior,←
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_frontier,P.frontier_complexInterior]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' (((↑) : 𝕔𝔻→ℂ) '' P.boundary)=_
  rw [image_image]
  congr 1
  funext p
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph_closed p

theorem DiscPolygon.klein_inside_isOpen {n : ℕ} (P : DiscPolygon n) :
    IsOpen (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior) :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_kleinCoordinate.isOpenMap _ P.interior_isOpen

theorem DiscPolygon.klein_edge_midpoint_mem_frontier {n : ℕ} (P : DiscPolygon n) (i : Fin n) :
    midpoint ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
      i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i)))∈
      frontier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior) := by
  have hm:=midpoint_mem_segment (𝕜:=ℝ) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    (P.vertices i))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i)))
  rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment] at hm
  rcases hm with ⟨p,hp,he⟩
  rw [P.klein_inside_frontier,← he]
  exact mem_image_of_mem _ (Set.mem_iUnion.mpr ⟨i,hp⟩)

theorem DiscPolygon.exists_support_equation {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex) (i : Fin n) :
    ∃ (m : ℂ) (t : ℝ),‖m‖=1 ∧ (∀ x∈P.kleinBody,inner ℝ m x≤t) ∧
      inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i))=t ∧
      inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i)))=t := by
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i)
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i))
  let z:=midpoint ℝ a b
  let U:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' P.interior
  have hU : IsOpen U:=P.klein_inside_isOpen
  have hz : z∈frontier U:=P.klein_edge_midpoint_mem_frontier i
  have hzu : z∉U := by
    intro hu
    exact (show z∉U by simpa only [hU.interior_eq] using hz.2) hu
  obtain ⟨f,hf⟩:=geometric_hahn_banach_open_point
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex P.interior).mp hc) hU hzu
  have hbound : ∀ x∈P.kleinBody,f x≤f z := by
    have hsub : U⊆{x | f x≤f z}:=fun x hx => (hf x hx).le
    have he : P.kleinBody=closure U:=P.closedKlein_image_closedCarrier
    rw [he]
    exact closure_minimal hsub (isClosed_le f.continuous continuous_const)
  have ha:=hbound a (mem_image_of_mem _ (P.vertex_mem_closedCarrier i))
  have hb:=hbound b (mem_image_of_mem _ (P.vertex_mem_closedCarrier (finRotate n i)))
  have hmid : 2*f z=f a+f b := by
    dsimp [z]
    rw [midpoint_eq_smul_add,map_smul,map_add]
    norm_num
    ring
  have hae : f a=f z := by linarith only [ha,hb,hmid]
  have hbe : f b=f z := by linarith only [ha,hb,hmid]
  let m:=complexLinearFunctionalNormal f.toLinearMap
  have hm : m≠0 := by
    obtain ⟨w,hw⟩:=P.interior_isConnected.nonempty
    have hlt:=hf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate w) (mem_image_of_mem _ hw)
    have he (x : ℂ) : f x=inner ℝ m x:= (complexLinearFunctionalNormal_inner f.toLinearMap x).symm
    intro hm
    rw [he,he,hm,inner_zero_left,inner_zero_left] at hlt
    exact (lt_irrefl _ hlt).elim
  have hn:=norm_pos_iff.mpr hm
  refine ⟨‖m‖⁻¹ • m,f z/‖m‖,?_,?_,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  · intro x hx
    rw [real_inner_smul_left,inv_mul_eq_div,complexLinearFunctionalNormal_inner]
    exact (div_le_div_iff_of_pos_right hn).mpr (hbound x hx)
  · rw [real_inner_smul_left,inv_mul_eq_div,complexLinearFunctionalNormal_inner]
    change f a/‖m‖=f z/‖m‖
    rw [hae]
  · rw [real_inner_smul_left,inv_mul_eq_div,complexLinearFunctionalNormal_inner]
    change f b/‖m‖=f z/‖m‖
    rw [hbe]


def DiscPolygon.geodesicSide {n : ℕ} (P : DiscPolygon n) (i : Fin
  n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discLine_closedCarrier (P.vertices i) (P.vertices
    (finRotate n i))
    (P.vertices_injective.ne (P.next_ne_self i).symm)).choose

theorem DiscPolygon.geodesicSide_endpoints {n : ℕ} (P : DiscPolygon n) (i : Fin n) :
    P.vertices i∈(P.geodesicSide i).closedCarrier ∧
      P.vertices (finRotate n i)∈(P.geodesicSide i).closedCarrier :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discLine_closedCarrier (P.vertices i) (P.vertices
    (finRotate n i))
    (P.vertices_injective.ne (P.next_ne_self i).symm)).choose_spec.1

theorem discRayTowardClosed_mem_support (z : 𝔻) (q : 𝕔𝔻) (hzq :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z≠q) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z∈(discRayTowardClosed z q
      hzq).supportLine.closedCarrier ∧
      q∈(discRayTowardClosed z q hzq).supportLine.closedCarrier := by
  let R:=discRayTowardClosed z q hzq
  constructor
  · exact subset_closure (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (R.subset_support R.start_mem))
  · exact closure_mono (image_mono R.subset_support) (discRayTowardClosed_endpoint_mem z q hzq)

theorem DiscPolygon.cornerRayNext_support_geodesicSide {n : ℕ} (P : DiscPolygon n) (i : Fin n)
    (z : 𝔻) (hz : P.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    (P.cornerRayNext i z hz).supportLine=P.geodesicSide i := by
  have hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z≠P.vertices (finRotate n i) := by
    rw [← hz]
    exact P.vertices_injective.ne (P.next_ne_self i).symm
  have h:=discRayTowardClosed_mem_support z (P.vertices (finRotate n i)) hne
  apply (P.cornerRayNext i z hz).supportLine.eq_of_two_closed_points (P.geodesicSide i)
    (P.vertices_injective.ne (P.next_ne_self i).symm)
  · rw [hz]
    exact h.1
  · exact h.2
  · exact (P.geodesicSide_endpoints i).1
  · exact (P.geodesicSide_endpoints i).2

theorem DiscPolygon.cornerRayPrev_support_geodesicSide {n : ℕ} (P : DiscPolygon n) (i : Fin n)
    (z : 𝔻) (hz : P.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    (P.cornerRayPrev i z hz).supportLine=P.geodesicSide ((finRotate n).symm i) := by
  have hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z≠P.vertices ((finRotate n).symm i) := by
    rw [← hz]
    exact P.vertices_injective.ne (P.prev_ne_self i).symm
  have h:=discRayTowardClosed_mem_support z (P.vertices ((finRotate n).symm i)) hne
  apply (P.cornerRayPrev i z hz).supportLine.eq_of_two_closed_points (P.geodesicSide ((finRotate n).symm i))
    (P.vertices_injective.ne (P.prev_ne_self i).symm)
  · rw [hz]
    exact h.1
  · exact h.2
  · simpa only [Equiv.apply_symm_apply] using (P.geodesicSide_endpoints ((finRotate n).symm i)).2
  · exact (P.geodesicSide_endpoints ((finRotate n).symm i)).1

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_iff_equation_of_two (L :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (p q : 𝕔𝔻)
    (hpq : p≠q) (hp : p∈L.closedCarrier) (hq : q∈L.closedCarrier)
    (m : ℂ) (t : ℝ) (hm : ‖m‖=1)
    (he1 : inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)=t)
    (he2 : inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q)=t) (x : 𝕔𝔻) :
    x∈L.closedCarrier ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate x)=t := by
  have hm0 : m≠0 := by intro hh;rw [hh,norm_zero] at hm;norm_num at hm
  have hn0 : L.incenterNormal≠0 := by
    intro hh
    have hu:=L.toHalfPlane.incenterNormal_lorentz_unit
    change ‖L.incenterNormal‖^2-L.incenterOffset^2=1 at hu
    rw [hh,norm_zero,zero_pow (by decide : 2≠0)] at hu
    nlinarith only [hu,sq_nonneg L.incenterOffset]
  obtain ⟨k,hk,hn,ht⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.complex_affine_normals_proportional m L.incenterNormal
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) t L.incenterOffset hm0 hn0
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpq) he1 he2
    (sub_eq_zero.mp ((L.closed_incenter_affine_zero_iff p).mpr hp))
    (sub_eq_zero.mp ((L.closed_incenter_affine_zero_iff q).mpr hq))
  rw [← L.closed_incenter_affine_zero_iff]
  change inner ℝ L.incenterNormal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    x)-L.incenterOffset=0 ↔ _
  rw [hn,ht,real_inner_smul_left,← mul_sub,mul_eq_zero]
  simp only [hk,false_or,sub_eq_zero]

theorem affine_support_openSegment_endpoint (m x y v : ℂ) (t : ℝ)
    (hx : inner ℝ m x≤t) (hy : inner ℝ m y≤t) (hv : inner ℝ m v=t)
    (hseg : v∈openSegment ℝ x y) : inner ℝ m x=t := by
  rcases hseg with ⟨a,b,ha,hb,hab,he⟩
  rw [← he,inner_add_right,inner_smul_right,inner_smul_right] at hv
  have hsum : a*(t-inner ℝ m x)+b*(t-inner ℝ m y)=0 := by
    linear_combination t*hab-hv
  have hax : 0≤a*(t-inner ℝ m x):=mul_nonneg ha.le (sub_nonneg.mpr hx)
  have hby : 0≤b*(t-inner ℝ m y):=mul_nonneg hb.le (sub_nonneg.mpr hy)
  have hzero : a*(t-inner ℝ m x)=0 := by linarith only [hsum,hax,hby]
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left ha.ne')).symm

theorem DiscPolygon.vertex_extreme_of_proper {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex) (i : Fin n)
    (hne : P.geodesicSide ((finRotate n).symm i)≠P.geodesicSide i) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i)∈P.kleinBody.extremePoints ℝ := by
  obtain ⟨m,t,hm,hbound,hself,hnext⟩:=P.exists_support_equation hc i
  obtain ⟨m',t',hm',hbound',hprev,hself'⟩:=P.exists_support_equation hc ((finRotate n).symm i)
  rw [Equiv.apply_symm_apply] at hself'
  refine mem_extremePoints_iff_left.mpr ⟨mem_image_of_mem _ (P.vertex_mem_closedCarrier i),?_⟩
  intro x hx y hy hseg
  have hxe:=affine_support_openSegment_endpoint m x y _ t (hbound x hx) (hbound y hy) hself hseg
  have hxe':=affine_support_openSegment_endpoint m' x y _ t' (hbound' x hx) (hbound' y hy) hself' hseg
  rcases hx with ⟨p,hp,rfl⟩
  have hpL:=((P.geodesicSide i).closedCarrier_iff_equation_of_two _ _
    (P.vertices_injective.ne (P.next_ne_self i).symm)
    (P.geodesicSide_endpoints i).1 (P.geodesicSide_endpoints i).2 m t hm hself hnext p).mpr hxe
  have hpM:=((P.geodesicSide ((finRotate n).symm i)).closedCarrier_iff_equation_of_two _ _
    (P.vertices_injective.ne (P.next_ne_self ((finRotate n).symm i)).symm)
    (P.geodesicSide_endpoints ((finRotate n).symm i)).1
    (P.geodesicSide_endpoints ((finRotate n).symm i)).2 m' t' hm' hprev
    (by simpa only [Equiv.apply_symm_apply] using hself') p).mpr hxe'
  have he : p=P.vertices i := by
    by_contra hh
    apply hne
    apply (P.geodesicSide ((finRotate n).symm i)).eq_of_two_closed_points (P.geodesicSide i) hh hpM
    · simpa only [Equiv.apply_symm_apply] using (P.geodesicSide_endpoints ((finRotate n).symm i)).2
    · exact hpL
    · exact (P.geodesicSide_endpoints i).1
  exact congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate he

theorem DiscPolygon.kleinBody_subset_closedBall {n : ℕ} (P : DiscPolygon n) :
    P.kleinBody⊆Metric.closedBall (0 : ℂ) 1 := by
  rintro x ⟨p,hp,rfl⟩
  simpa only [Metric.mem_closedBall,dist_zero_right,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate] using (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein p).norm_le_one

theorem DiscPolygon.vertex_extreme_of_ideal {n : ℕ} (P : DiscPolygon n) (i : Fin n)
    (hi : ‖(P.vertices i : ℂ)‖=1) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i)∈P.kleinBody.extremePoints ℝ := by
  apply inter_extremePoints_subset_extremePoints_of_subset P.kleinBody_subset_closedBall
  constructor
  · exact mem_image_of_mem _ (P.vertex_mem_closedCarrier i)
  · apply StrictConvexSpace.sphere_subset_extremePoints_closedBall (0 : ℂ) (by norm_num : (1:ℝ)≠0)
    simpa only [Metric.mem_sphere,dist_zero_right,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed _ hi] using hi


theorem complex_extreme_triple_not_collinear (C : Set ℂ) (x y z : ℂ)
    (hx : x∈C.extremePoints ℝ) (hy : y∈C.extremePoints ℝ) (hz : z∈C.extremePoints ℝ)
    (hxy : x≠y) (hyz : y≠z) (hxz : x≠z) : ¬Collinear ℝ ({x,y,z} : Set ℂ) := by
  intro hc
  rcases hc.wbtw_or_wbtw_or_wbtw with h|h|h
  · exact hxy (hy.2 hx.1 hz.1 (mem_openSegment_of_ne_left_right hxy hyz.symm h.mem_segment))
  · exact hyz (hz.2 hy.1 hx.1 (mem_openSegment_of_ne_left_right hyz hxz h.mem_segment))
  · exact hxz.symm (hx.2 hz.1 hy.1 (mem_openSegment_of_ne_left_right hxz.symm hxy.symm h.mem_segment))

theorem complex_unit_affine_hyperplane_collinear_three (m a b c : ℂ) (t : ℝ)
    (hm : ‖m‖=1) (hab : a≠b) (ha : inner ℝ m a=t)
    (hb : inner ℝ m b=t) (hc : inner ℝ m c=t) : Collinear ℝ ({a,b,c} : Set ℂ) := by
  obtain ⟨s,hs⟩:=complex_affine_hyperplane_line m a b c t hm hab ha hb hc
  apply (collinear_iff_of_mem (by simp : a∈({a,b,c} : Set ℂ))).mpr
  refine ⟨b-a,?_⟩
  intro x hx
  rcases hx with rfl|rfl|rfl
  · exact ⟨0,by simp⟩
  · exact ⟨1,by simp⟩
  · refine ⟨s,?_⟩
    change x=s • (b-a)+a
    rw [hs]
    module

theorem DiscPolygon.all_vertices_extreme_of_finite_proper {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (hproper : ∀ i : Fin n,∀ z : 𝔻,∀ hz : P.vertices
      i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z,
      (P.cornerRayPrev i z hz).supportLine≠(P.cornerRayNext i z hz).supportLine) :
    ∀ i : Fin n,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i)∈P.kleinBody.extremePoints ℝ := by
  intro i
  rcases _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDisc_interior_or_ideal (P.vertices i) with ⟨z,hz⟩|hz
  · apply P.vertex_extreme_of_proper hc i
    have h:=hproper i z hz.symm
    rwa [P.cornerRayPrev_support_geodesicSide i z hz.symm,P.cornerRayNext_support_geodesicSide i z hz.symm] at h
  · exact P.vertex_extreme_of_ideal i hz

theorem DiscPolygon.support_equation_strict_of_extreme {n : ℕ} (P : DiscPolygon n)
    (hE : ∀ i : Fin n,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
      i)∈P.kleinBody.extremePoints ℝ)
    (i : Fin n) (m : ℂ) (t : ℝ) (hm : ‖m‖=1)
    (hbound : ∀ x∈P.kleinBody,inner ℝ m x≤t)
    (hi : inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i))=t)
    (hnext : inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n
      i)))=t)
    (j : Fin n) (hji : j≠i) (hjn : j≠finRotate n i) :
    inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices j))<t := by
  have hle:=hbound _ (mem_image_of_mem _ (P.vertex_mem_closedCarrier j))
  apply lt_of_le_of_ne hle
  intro he
  have ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
    i)≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n i)) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (P.vertices_injective.ne
      (P.next_ne_self i).symm)
  have hb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices (finRotate n
    i))≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices j) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (P.vertices_injective.ne
      hjn.symm)
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
    i)≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices j) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (P.vertices_injective.ne
      hji.symm)
  exact complex_extreme_triple_not_collinear P.kleinBody _ _ _ (hE i) (hE (finRotate n i)) (hE j) ha hb hc
    (complex_unit_affine_hyperplane_collinear_three m _ _ _ t hm ha hi hnext he)



theorem DiscPolygon.eq_of_vertices_eq {n : ℕ} (P Q : DiscPolygon n) (hv : P.vertices=Q.vertices) : P=Q := by
  cases P
  cases Q
  cases hv
  rfl

def DiscPolygon.supportDataOfExtreme {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (hE : ∀ i : Fin n,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
      i)∈P.kleinBody.extremePoints ℝ) :
    CyclicDiscPolygonSupportData n := by
  classical
  choose m t hm hb hi hnext using P.exists_support_equation hc
  exact {
    three_le:=P.three_le
    vertices:=P.vertices
    vertices_injective:=P.vertices_injective
    normals:=m
    normal_norm:=hm
    offsets:=t
    incident:=fun i => ⟨hi i,hnext i⟩
    nonincident:=fun i j hji hjn => P.support_equation_strict_of_extreme hE i (m i) (t i)
      (hm i) (hb i) (hi i) (hnext i) j hji hjn }

theorem DiscPolygon.supportDataOfExtreme_vertices {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (hE : ∀ i : Fin n,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
      i)∈P.kleinBody.extremePoints ℝ) :
    (P.supportDataOfExtreme hc hE).vertices=P.vertices := rfl

theorem DiscPolygon.supportDataOfExtreme_toDiscPolygon {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (hE : ∀ i : Fin n,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
      i)∈P.kleinBody.extremePoints ℝ) :
    (P.supportDataOfExtreme hc hE).toDiscPolygon=P := by
  apply DiscPolygon.eq_of_vertices_eq
  rfl

theorem DiscPolygon.supportDataOfExtreme_supportLine {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (hE : ∀ i : Fin n,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices
      i)∈P.kleinBody.extremePoints ℝ) (i : Fin n) :
    ((P.supportDataOfExtreme hc hE).toCenteredData.supportLine i)=P.geodesicSide i := by
  let S:=(P.supportDataOfExtreme hc hE).toCenteredData
  exact (S.supportLine i).eq_of_two_closed_points (P.geodesicSide i)
    (P.vertices_injective.ne (P.next_ne_self i).symm)
    (S.incident_mem_support i).1 (S.incident_mem_support i).2
    (P.geodesicSide_endpoints i).1 (P.geodesicSide_endpoints i).2



theorem DiscPolygon.vertex_finite_of_angle_pos {n : ℕ} (P : DiscPolygon n) (i : Fin n)
    (ha : 0<P.angle i) : ‖(P.vertices i : ℂ)‖<1 := by
  by_contra hn
  have hi : ‖(P.vertices i : ℂ)‖=1:=le_antisymm (P.vertices i).norm_le_one (le_of_not_gt hn)
  rw [P.angle_of_ideal i hi] at ha
  exact (lt_irrefl _ ha).elim

theorem DiscPolygon.adjacent_sides_orthogonal_of_angle_right {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (ha :
      P.angle i=Real.pi/2) :
    (P.geodesicSide ((finRotate n).symm i)).OrthogonalAt (P.geodesicSide i) z := by
  let R:=P.cornerRayPrev i z hz
  let S:=P.cornerRayNext i z hz
  have hθ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure R S=Real.pi/2 := by
    rw [P.angle_of_finite i z hz] at ha
    by_cases hminor : P.HasMinorInteriorAt i z hz
    · exact (ite_eq_left hminor).symm.trans ha
    · rw [ite_eq_right hminor] at ha
      have hle:=angle_le_pi R.tangentVector S.tangentVector
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure R S≤Real.pi at hle
      linarith [Real.pi_pos]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane] at hθ
  have hperp:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_eq_pi_div_two_iff R.toHalfPlane
    S.toHalfPlane).mp hθ
  have hpD : R.supportLine.OrthogonalAt S.supportLine z :=
    (R.supportLine.orthogonalAt_iff_halfPlane S.supportLine z).mpr
      (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.supportLine,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_toHalfPlane] using hperp)
  change (P.cornerRayPrev i z hz).supportLine.OrthogonalAt (P.cornerRayNext i z hz).supportLine z at hpD
  rwa [P.cornerRayPrev_support_geodesicSide i z hz,P.cornerRayNext_support_geodesicSide i z hz] at hpD

theorem DiscPolygon.adjacent_sides_ne_of_angle_right {n : ℕ} (P : DiscPolygon n)
    (i : Fin n) (z : 𝔻) (hz : P.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) (ha :
      P.angle i=Real.pi/2) :
    P.geodesicSide ((finRotate n).symm i)≠P.geodesicSide i := by
  have hp:=P.adjacent_sides_orthogonal_of_angle_right i z hz ha
  have hH:=((P.geodesicSide ((finRotate n).symm i)).orthogonalAt_iff_halfPlane (P.geodesicSide i) z).mp hp
  intro he
  apply (P.geodesicSide ((finRotate n).symm i)).toHalfPlane.ne_of_orthogonalAt
    (P.geodesicSide i).toHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z) hH
  exact congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane he

theorem DiscPolygon.all_vertices_extreme_of_right_angles {n : ℕ} (P : DiscPolygon n) (hc : P.IsConvex)
    (ha : ∀ i : Fin n,P.angle i=Real.pi/2) :
    ∀ i : Fin n,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (P.vertices i)∈P.kleinBody.extremePoints ℝ := by
  intro i
  have hi:=P.vertex_finite_of_angle_pos i (by rw [ha];positivity)
  let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (P.vertices i) hi
  have hz : P.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec (P.vertices i) hi).symm
  exact P.vertex_extreme_of_proper hc i (P.adjacent_sides_ne_of_angle_right i z hz (ha i))


end
end LowDimensionalTopology.Geometry.Polygon
