/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaVertexCycles
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Strict.Extreme
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Complex.UnitDisc Topology UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance kleinHullSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance kleinHullSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- The literal compact Euclidean Klein closure of the original polygon. -/
def fuchsianPolygonCompactKlein {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) : Set ℂ :=
  closure (P.kleinCoordinate '' D)

/-- The genuine Klein closure lies in the actual closed unit ball and is compact. -/
theorem fuchsianPolygonCompactKlein_compact {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) :
    IsCompact (fuchsianPolygonCompactKlein P D) := by
  apply (isCompact_closedBall (0:ℂ) 1).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  rintro z ⟨x,hx,rfl⟩
  apply Metric.ball_subset_closedBall
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (P.finiteCoordinate x)∈Metric.ball (0:ℂ) 1
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
  exact mem_range_self _

/-- The original finite closed polygon is exactly the open-disc part of its literal compact Klein closure. -/
theorem fuchsianPolygonCompactKlein_finite_part {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) :
    P.kleinCoordinate '' closure D=fuchsianPolygonCompactKlein P D∩Metric.ball (0:ℂ) 1 := by
  have he : P.kleinCoordinate '' closure D=_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (P.finiteCoordinate '' closure D):=by
    rw [image_image]
    rfl
  rw [he,P.finiteCoordinate.image_closure,_root_.LowDimensionalTopology.Geometry.Hyperbolic.klein_image_closure,image_image]
  rfl

/-- A true finite extreme point of the compact Klein closure must be an actual original polygon vertex. -/
theorem compactKlein_extreme_finite_is_vertex {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (x : P.domain.carrier)
    (hext : P.kleinCoordinate x∈(fuchsianPolygonCompactKlein P D).extremePoints ℝ) :
    IsFuchsianPolygonVertex P D x := by
  let K:=fuchsianPolygonCompactKlein P D
  have hxK : P.kleinCoordinate x∈K:=extremePoints_subset hext
  have hxcl : x∈closure D:=by
    rw [P.kleinCoordinate_isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image D]
    exact hxK
  have hxfront : x∈frontier D:=by
    rw [hD.locallyFinite.fundamental.isOpen.frontier_eq]
    refine ⟨hxcl,?_⟩
    intro hxD
    have ho:=P.kleinCoordinate_isOpenEmbedding.isOpenMap D hD.locallyFinite.fundamental.isOpen
    have hxint : P.kleinCoordinate x∈interior (P.kleinCoordinate '' D):=by
      rw [ho.interior_eq]
      exact mem_image_of_mem _ hxD
    exact disjoint_left.mp (disjoint_interior_extremePoints K) (interior_mono subset_closure hxint) hext
  by_contra hnv
  obtain ⟨S,hS,a,ha,b,hb,hab,hxab⟩:=hD.nonvertex_is_side_interior hxfront hnv
  have hKconv : Convex ℝ K:=hD.klein_convex.closure
  have hremove : Convex ℝ (K\{P.kleinCoordinate x}):=
    (hKconv.mem_extremePoints_iff_convex_sdiff).mp hext |>.2
  have himage : P.kleinCoordinate '' (closure D\{x})=
      (K\{P.kleinCoordinate x})∩Metric.ball (0:ℂ) 1 := by
    rw [image_sdiff P.kleinCoordinate_isOpenEmbedding.injective,image_singleton,
      fuchsianPolygonCompactKlein_finite_part]
    ext z
    simp only [mem_sdiff,mem_inter_iff,mem_singleton_iff]
    tauto
  have hsmall : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' (closure D\{x})):=by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mpr
    rw [image_image]
    change Convex ℝ (P.kleinCoordinate '' (closure D\{x}))
    rw [himage]
    exact hremove.inter (convex_ball (0:ℂ) 1)
  have hnormal : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (polygonPointCoordinate P x '' (closure D\{x})):=by
    have he : polygonPointCoordinate P x '' (closure D\{x})=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate x) '' (P.finiteCoordinate '' (closure D\{x})):=by
      rw [image_image]
      rfl
    rw [he]
    exact hsmall.isometry_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry _)
  have hconv : Convex ℝ (normalizedPolygonKleinCoordinate P x '' (closure D\{x})):=by
    have he : normalizedPolygonKleinCoordinate P x '' (closure D\{x})=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (polygonPointCoordinate P x '' (closure D\{x})):=by
      rw [image_image]
      rfl
    rw [he]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp hnormal
  let F:=normalizedPolygonKleinCoordinate P x
  have hFinj : Function.Injective F:=(normalizedPolygonKleinCoordinate_isOpenEmbedding P x).injective
  have hax : a≠x:=by
    intro h
    have hh : F a∈openSegment ℝ (F a) (F b):=by
      exact Eq.mpr (congrArg (fun z : ℂ=>z∈openSegment ℝ (F a) (F b)) (congrArg F h)) hxab
    exact hab (hFinj (left_mem_openSegment_iff.mp hh))
  have hbx : b≠x:=by
    intro h
    have hh : F b∈openSegment ℝ (F a) (F b):=by
      exact Eq.mpr (congrArg (fun z : ℂ=>z∈openSegment ℝ (F a) (F b)) (congrArg F h)) hxab
    exact hab (hFinj (right_mem_openSegment_iff.mp hh))
  have haC : a∈closure D:=(hS.subset_frontier hD.locallyFinite.fundamental ha).1
  have hbC : b∈closure D:=(hS.subset_frontier hD.locallyFinite.fundamental hb).1
  have hz:=hconv.segment_subset (mem_image_of_mem F ⟨haC,hax⟩)
    (mem_image_of_mem F ⟨hbC,hbx⟩) (openSegment_subset_segment ℝ _ _ hxab)
  obtain ⟨y,hy,he⟩:=hz
  exact hy.2 (hFinj he)

/-- The actual ideal boundary of the compact Klein closure is exactly the original literal ideal boundary. -/
theorem compactKlein_ideal_mem_iff {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (z : ℂ) (hz : ‖z‖=1) :
    z∈fuchsianPolygonCompactKlein P D↔z∈fuchsianPolygonIdealBoundary P D := by
  let S:=P.finiteCoordinate '' D
  have he : fuchsianPolygonCompactKlein P D=closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S):=by
    change closure (P.kleinCoordinate '' D)=_
    rw [image_image]
    rfl
  constructor
  · intro hzK
    rw [he,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_discClosedModelClosure] at hzK
    obtain ⟨p,hp,hpz⟩:=hzK
    let q:=Complex.UnitClosedDisc.mk z hz.le
    have hq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q=z:=
      congrArg (fun w : 𝕔𝔻=>(w:ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed
        q hz)
    have hpq : p=q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective (hpz.trans
      hq.symm)
    have hqC : q∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discIdealClosureTrace S:=⟨hpq ▸ hp,hz⟩
    have hm : z∈((↑) : 𝕔𝔻→ℂ) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discIdealClosureTrace S:=⟨q,hqC,rfl⟩
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discIdealClosureTrace_coe_image] at hm
    simpa only [fuchsianPolygonIdealBoundary,S,image_image,Function.comp_def] using hm
  · intro hzE
    rw [he]
    have hcl : z∈closure (((↑) : 𝔻→ℂ) '' S):=by
      change z∈closure ((fun x=>(P.finiteCoordinate x:ℂ)) '' D)∩_ at hzE
      simpa only [S,image_image,Function.comp_def] using hzE.1
    exact disc_ideal_closure_klein z hz hcl

/-- Every true extreme point is either a genuine finite vertex or a genuine ideal boundary point. -/
theorem compactKlein_extreme_subset_vertices_ideal {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) :
    (fuchsianPolygonCompactKlein P D).extremePoints ℝ⊆
      P.kleinCoordinate '' {x | IsFuchsianPolygonVertex P D x}∪fuchsianPolygonIdealBoundary P D := by
  intro z hz
  have hzK : z∈fuchsianPolygonCompactKlein P D:=extremePoints_subset hz
  have hbound : ‖z‖≤1:=by
    have hsub : fuchsianPolygonCompactKlein P D⊆Metric.closedBall (0:ℂ) 1:=by
      apply closure_minimal _ Metric.isClosed_closedBall
      rintro u ⟨x,hx,rfl⟩
      apply Metric.ball_subset_closedBall
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (P.finiteCoordinate
        x)∈Metric.ball (0:ℂ) 1
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
      exact mem_range_self _
    simpa only [Metric.mem_closedBall,dist_zero_right] using hsub hzK
  by_cases hi : ‖z‖=1
  · exact Or.inr ((compactKlein_ideal_mem_iff P D z hi).mp hzK)
  · have hlt : ‖z‖<1:=lt_of_le_of_ne hbound hi
    have hr : range P.kleinCoordinate=Metric.ball (0:ℂ) 1:=by
      change range (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ∘ P.finiteCoordinate)=_
      rw [range_comp,P.finiteCoordinate.surjective.range_eq,image_univ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
    have hzR : z∈range P.kleinCoordinate:=by
      rw [hr]
      simpa only [Metric.mem_ball,dist_zero_right] using hlt
    obtain ⟨x,rfl⟩:=hzR
    exact Or.inl ⟨x,compactKlein_extreme_finite_is_vertex hD x hz,rfl⟩

/-- Genuine finite area makes the actual compact Klein closure's extreme-point set finite. -/
theorem finite_area_compactKlein_extreme_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    ((fuchsianPolygonCompactKlein P D).extremePoints ℝ).Finite := by
  exact (((finite_area_polygon_vertices_finite hD harea).image P.kleinCoordinate).union
    (finite_area_polygon_idealBoundary_finite hD harea)).subset
      (compactKlein_extreme_subset_vertices_ideal hD)

/-- The literal compact Klein closure is the genuine Euclidean convex hull of the finite actual vertex set together with the actual ideal boundary, rather than a newly defined polygonal replacement. -/
theorem finite_area_compactKlein_eq_vertices_ideal_convexHull {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    fuchsianPolygonCompactKlein P D=convexHull ℝ
      (P.kleinCoordinate '' {x | IsFuchsianPolygonVertex P D x}∪fuchsianPolygonIdealBoundary P D) := by
  let K:=fuchsianPolygonCompactKlein P D
  let V:=P.kleinCoordinate '' {x | IsFuchsianPolygonVertex P D x}∪fuchsianPolygonIdealBoundary P D
  have hKconv : Convex ℝ K:=hD.klein_convex.closure
  have hVfin : V.Finite:=((finite_area_polygon_vertices_finite hD harea).image P.kleinCoordinate).union
    (finite_area_polygon_idealBoundary_finite hD harea)
  have hext : K.extremePoints ℝ⊆V:=compactKlein_extreme_subset_vertices_ideal hD
  have hV : V⊆K:=by
    intro z hz
    rcases hz with ⟨x,hx,rfl⟩ | hz
    · have hxcl:=frontier_subset_closure (hx.mem_frontier hD.locallyFinite.fundamental)
      have hm : P.kleinCoordinate x∈P.kleinCoordinate '' closure D:=mem_image_of_mem _ hxcl
      exact (fuchsianPolygonCompactKlein_finite_part P D ▸ hm).1
    · exact (compactKlein_ideal_mem_iff P D z
        (by simpa only [Metric.mem_sphere,dist_zero_right] using hz.2)).mpr hz
  apply subset_antisymm
  · have he:=closure_convexHull_extremePoints (fuchsianPolygonCompactKlein_compact P D) hKconv
    rw [←he]
    exact closure_minimal (convexHull_mono hext) (hVfin.isClosed_convexHull ℝ)
  · exact convexHull_min hV hKconv

end LowDimensionalTopology.Geometry.Fuchsian
