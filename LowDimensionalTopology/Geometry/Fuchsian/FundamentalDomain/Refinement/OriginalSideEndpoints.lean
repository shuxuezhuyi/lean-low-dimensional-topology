/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CompactifiedPolygonSides
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaPolygonSides
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaIdealVertices
public import Mathlib.Analysis.Convex.Strict.Extreme
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped OnePoint Complex.UnitDisc Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual endpoint of a nondegenerate segment is a genuine extreme point. -/
theorem original_segment_left_extreme (p q:ℂ) (hpq:p≠q) :
    p∈(segment ℝ p q).extremePoints ℝ := by
  have h0 : (0:ℝ)∈(Icc (0:ℝ) 1).extremePoints ℝ:=by
    rw [Set.extremePoints_Icc zero_le_one]
    simp only [mem_insert_iff,true_or]
  refine ⟨left_mem_segment ℝ p q,?_⟩
  intro a ha b hb hopen
  rw [segment_eq_image_lineMap] at ha hb
  obtain ⟨t,ht,rfl⟩:=ha
  obtain ⟨u,hu,rfl⟩:=hb
  have him : p∈AffineMap.lineMap p q '' openSegment ℝ t u:=by
    rwa [image_openSegment]
  obtain ⟨v,hv,hvp⟩:=him
  have hv0 : v=0:=(AffineMap.lineMap_injective ℝ hpq) (by simpa only [AffineMap.lineMap_apply_zero] using hvp)
  have ht0:=h0.2 ht hu (hv0 ▸ hv)
  rw [ht0,AffineMap.lineMap_apply_zero]

/-- Every actual finite endpoint of an unchanged original polygon side is an original polygon vertex. -/
theorem original_finite_side_endpoint_vertex {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (s:FuchsianPolygonSides P D)
    (p q:𝕔𝔻) (hpq:p≠q) (hs:fuchsianSideClosedModel
      s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q)
    (x:P.domain.carrier) (hxp:_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate
      x)=p) :
    IsFuchsianPolygonVertex P D x := by
  have hx : x∈s.val:=by
    apply (mem_fuchsianSideClosedModel_finite s x).mp
    rw [hxp,hs]
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact left_mem_segment ℝ _ _
  have he : closure (P.kleinCoordinate '' s.val)=segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q):=by
    rw [←fuchsianSideClosedModel_klein_image,hs,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
  have hKp : P.kleinCoordinate x=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hxp
  have hsegext:=original_segment_left_extreme (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpq)
  have hKext : P.kleinCoordinate x∈(P.kleinCoordinate '' s.val).extremePoints ℝ:=by
    refine ⟨mem_image_of_mem _ hx,?_⟩
    intro a ha b hb hopen
    rw [hKp] at hopen ⊢
    exact hsegext.2 (he ▸ subset_closure ha) (he ▸ subset_closure hb) hopen
  have hconv : Convex ℝ (P.kleinCoordinate '' s.val):=by
    have h:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp s.property.2.1.1
    rwa [image_image] at h
  by_contra hnv
  apply polygon_side_remove_nonvertex_not_convex hD s.property hx hnv
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mpr
  rw [image_image]
  change Convex ℝ (P.kleinCoordinate '' (s.val\{x}))
  rw [image_sdiff P.kleinCoordinate_isOpenEmbedding.injective,image_singleton]
  exact (hconv.mem_extremePoints_iff_convex_sdiff.mp hKext).2

/-- Both finite endpoints of every original compactified side are its genuine original vertices. -/
theorem original_finite_side_endpoint_vertices {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (s:FuchsianPolygonSides P D)
    (p q:𝕔𝔻) (hpq:p≠q) (hs:fuchsianSideClosedModel
      s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q) :
    (∀x:P.domain.carrier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate
      x)=p→IsFuchsianPolygonVertex P D x)∧
    (∀x:P.domain.carrier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)=q→IsFuchsianPolygonVertex P D x) := by
  constructor
  · exact fun x hx=>original_finite_side_endpoint_vertex hD s p q hpq hs x hx
  · exact fun x hx=>original_finite_side_endpoint_vertex hD s q p hpq.symm
      (hs.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_comm p q)) x hx

/-- Every ideal endpoint of an unchanged original finite-area polygon side is an actual proper infinite vertex with two original incident sides. -/
theorem original_ideal_side_point_isProper {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤) (s:FuchsianPolygonSides P D)
    (p:𝕔𝔻) (hp:p∈fuchsianSideClosedModel s) (hn:‖(p:ℂ)‖=1) :
    IsProperFuchsianInfiniteVertex P D (⟨(p:ℂ),mem_sphere_zero_iff_norm.mpr hn⟩:Circle) := by
  have hk:=fuchsianSideClosedModel_klein_subset_polygon s (mem_image_of_mem
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hp)
  have hkp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p=(p:ℂ):=congrArg (fun
    z:𝕔𝔻=>(z:ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed p hn)
  rw [hkp] at hk
  have hu : (p:ℂ)∈fuchsianPolygonIdealBoundary P D:=(compactKlein_ideal_mem_iff P D (p:ℂ) hn).mp hk
  exact finite_area_polygon_idealBoundary_isProper hD ha _ hu

end LowDimensionalTopology.Geometry.Fuchsian
