/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Refinement.OriginalSideEndpoints
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteConvexBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletGeometry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance compactSideBoundaryBorelMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance compactSideBoundaryBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- True finite original frontier points have exactly their actual compact Klein frontier coordinates. -/
theorem original_klein_frontier_mem {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (x:P.domain.carrier) :
    P.kleinCoordinate x∈frontier (fuchsianPolygonCompactKlein P D)↔x∈frontier D := by
  have he:=P.kleinCoordinate_isOpenEmbedding.isOpenMap.preimage_frontier_eq_frontier_preimage
    P.kleinCoordinate_isOpenEmbedding.continuous (fuchsianPolygonCompactKlein P D)
  have hp:P.kleinCoordinate ⁻¹' fuchsianPolygonCompactKlein P D=closure D:=by
    rw [P.kleinCoordinate_isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image]
    rfl
  rw [hp] at he
  have hf:frontier (closure D)=frontier D:=by
    simp only [frontier,closure_closure,hD.interior_closure,hD.locallyFinite.fundamental.isOpen.interior_eq]
  rw [hf] at he
  exact Set.ext_iff.mp he x

/-- Every unchanged original compactified side lies on the genuine compact Klein boundary. -/
theorem original_side_klein_subset_frontier {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (s:FuchsianPolygonSides P D) :
    closure (P.kleinCoordinate '' s.val)⊆frontier (fuchsianPolygonCompactKlein P D) := by
  apply closure_minimal _ isClosed_frontier
  rintro z ⟨x,hx,rfl⟩
  exact (original_klein_frontier_mem hD x).mpr
    (s.property.subset_frontier hD.locallyFinite.fundamental hx)

/-- The original compactified side has precisely the literal complex closure of its genuine points. -/
theorem original_side_closed_complex_image {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (s:FuchsianPolygonSides P D) :
    (fun z:𝕔𝔻=>(z:ℂ)) '' fuchsianSideClosedModel s=
      closure ((fun x=>(P.finiteCoordinate x:ℂ)) '' s.val) := by
  have hc:Topology.IsClosedEmbedding (fun z:𝕔𝔻=>(z:ℂ)):=
    Complex.UnitClosedDisc.isEmbedding_coe.continuous.isClosedEmbedding
      Complex.UnitClosedDisc.isEmbedding_coe.injective
  rw [fuchsianSideClosedModel,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,←hc.closure_image_eq,image_image,image_image]
  rfl

/-- The actual compact boundary is covered by the unchanged original compactified sides. No side is replaced by an extreme-hull edge and no straight original vertex is discarded. -/
theorem finite_area_original_compact_boundary {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤) :
    frontier (fuchsianPolygonCompactKlein P D)=
      ⋃s:FuchsianPolygonSides P D,closure (P.kleinCoordinate '' s.val) := by
  apply subset_antisymm
  · intro z hz
    have hzK: z∈fuchsianPolygonCompactKlein P D:=by
      have hh:=frontier_subset_closure hz
      simpa only [fuchsianPolygonCompactKlein,closure_closure] using hh
    have hzbound:‖z‖≤1:=by
      apply mem_closedBall_zero_iff.mp
      apply (show fuchsianPolygonCompactKlein P D⊆Metric.closedBall (0:ℂ) 1 from ?_) hzK
      apply closure_minimal _ Metric.isClosed_closedBall
      rintro y ⟨x,hx,rfl⟩
      exact Metric.ball_subset_closedBall (P.kleinCoordinate_range ▸ mem_range_self x)
    by_cases hlt:‖z‖<1
    · obtain ⟨x,rfl⟩:=(P.kleinCoordinate_range ▸ (mem_ball_zero_iff.mpr hlt))
      obtain ⟨S,hS,hx⟩:=hD.boundary_mem_side ((original_klein_frontier_mem hD x).mp hz)
      exact mem_iUnion.mpr ⟨⟨S,hS⟩,subset_closure (mem_image_of_mem P.kleinCoordinate hx)⟩
    · have hn:‖z‖=1:=le_antisymm hzbound (not_lt.mp hlt)
      let u:Circle:=⟨z,mem_sphere_zero_iff_norm.mpr hn⟩
      have hu:z∈fuchsianPolygonIdealBoundary P D:=(compactKlein_ideal_mem_iff P D z hn).mp hzK
      obtain ⟨_,S,T,hS,_hT,_hne,huS,_huT⟩:=finite_area_polygon_idealBoundary_isProper hD ha u hu
      let s:FuchsianPolygonSides P D:=⟨S,hS⟩
      have hcl:z∈closure ((fun x=>(P.finiteCoordinate x:ℂ)) '' s.val):=huS
      rw [←original_side_closed_complex_image s] at hcl
      obtain ⟨p,hp,hpz⟩:=hcl
      change (p:ℂ)=z at hpz
      have hpn:‖(p:ℂ)‖=1:=by rw [hpz];exact hn
      have hkp:_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p=z:=by
        change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein p:ℂ)=z
        rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed p hpn]
        exact hpz
      refine mem_iUnion.mpr ⟨s,?_⟩
      rw [←fuchsianSideClosedModel_klein_image s]
      exact ⟨p,hp,hkp⟩
  · intro z hz
    obtain ⟨s,hs⟩:=mem_iUnion.mp hz
    exact original_side_klein_subset_frontier hD s hs

/-- The genuine original-side compactification is exactly the genuine Jordan boundary of an actual finite polygon with the same interior. This identifies the whole boundary only; its original side subdivisions remain retained. -/
theorem finite_area_original_boundary_jordan_model {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤) :
    ∃n:ℕ,∃Q:_root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n,Q.interior=P.finiteCoordinate '' D ∧
      Q.boundary=⋃s:FuchsianPolygonSides P D,fuchsianSideClosedModel s := by
  obtain ⟨n,S,hregion,hint⟩:=finite_area_polygon_actual_cyclic_model hD ha
  refine ⟨n,S.toDiscPolygon,hint,?_⟩
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.image_injective
  have hb:=S.toCenteredData.boundary_image_eq_frontier
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' S.toDiscPolygon.boundary=frontier S.toCenteredData.kleinRegion at hb
  rw [hb,hregion,finite_area_original_compact_boundary hD ha,image_iUnion]
  congr 1
  funext s
  exact (fuchsianSideClosedModel_klein_image s).symm

end LowDimensionalTopology.Geometry.Fuchsian
