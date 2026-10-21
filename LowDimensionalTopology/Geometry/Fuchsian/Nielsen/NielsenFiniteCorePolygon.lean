/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenBoundaryLineFamily
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.FiniteHull
public import LowDimensionalTopology.Geometry.Polygon.Convexity.FiniteHullSupports
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaKleinHull

/-!
# Actual finite Nielsen-core polygon geometry
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc OnePoint RealInnerProductSpace
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance nielsenFiniteCorePolygonSphereMeasurableSpace : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance nielsenFiniteCorePolygonSphereBorelSpace : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩

theorem nielsenCore_finite_boundary_line_cover
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (ha:fuchsianNielsenCoreArea P hNE D≠⊤)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    ∃T:Set Hyperbolic.DiscLine,T.Finite ∧
      P.finiteCoordinate '' frontier (D∩fuchsianNielsenCore P hNE)⊆⋃L∈T,L.carrier := by
  classical
  let : Fintype (FuchsianPolygonSides P D):=hfin.fintype
  choose oldLine oldSpec using (fun s:FuchsianPolygonSides P D=>s.property.2.1.2)
  let A:={L:Hyperbolic.DiscLine | L∈nielsenBoundaryDiscLineFamily P hNE ∧
    (L.carrier∩P.finiteCoordinate '' closure (D∩fuchsianNielsenCore P hNE)).Nonempty}
  have hA:A.Finite:=finite_nielsenCore_boundary_lines hD hNE ha w hwD hwN
  refine ⟨range oldLine∪A,(Set.finite_range oldLine).union hA,?_⟩
  rintro z ⟨x,hx,rfl⟩
  rcases frontier_inter_subset D (fuchsianNielsenCore P hNE) hx with hxD|hxN
  · obtain ⟨S,hS,hxS⟩:=hD.boundary_mem_side hxD.1
    let s:FuchsianPolygonSides P D:=⟨S,hS⟩
    exact mem_iUnion₂.mpr ⟨oldLine s,Or.inl (mem_range_self s),oldSpec s (mem_image_of_mem _ hxS)⟩
  · have hxN':P.finiteCoordinate x∈P.finiteCoordinate '' frontier (fuchsianNielsenCore P hNE):=
      mem_image_of_mem _ hxN.2
    rw [nielsenBoundaryDiscLineFamily_frontier_cover P hNE] at hxN'
    obtain ⟨L,hxL⟩:=mem_iUnion.mp hxN'
    obtain ⟨hL,hxL⟩:=mem_iUnion.mp hxL
    have hLA:L∈A:=⟨hL,P.finiteCoordinate x,hxL,x,frontier_subset_closure hx,rfl⟩
    exact mem_iUnion₂.mpr ⟨L,Or.inr hLA,hxL⟩

theorem nielsenCore_klein_interior
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H)
    (w:P.domain.carrier)
    (hwD:w∈D)
    (hwN:w∈fuchsianNielsenCore P hNE) :
    interior (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))=
      P.kleinCoordinate '' (D∩fuchsianNielsenCore P hNE) := by
  have hc:Convex ℝ (P.kleinCoordinate '' (D∩fuchsianNielsenCore P hNE)) := by
    have h:=(Hyperbolic.discHConvex_iff_klein_convex _).mp (nielsenCore_inter_native_convex hD hNE)
    simpa only [image_image,Fuchsian.UnitDiscFuchsianGroup.kleinCoordinate] using h
  have ho:=P.kleinCoordinate_isOpenEmbedding.isOpenMap _
    (hD.locallyFinite.fundamental.isOpen.inter (fuchsianNielsenCore_isOpen P hNE))
  have hn:(interior (P.kleinCoordinate '' (D∩fuchsianNielsenCore P hNE))).Nonempty := by
    rw [ho.interior_eq]
    exact ⟨P.kleinCoordinate w,w,⟨hwD,hwN⟩,rfl⟩
  exact (hc.interior_closure_eq_interior_of_nonempty_interior hn).trans ho.interior_eq

theorem nielsenCore_klein_finite_frontier
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H)
    (w:P.domain.carrier)
    (hwD:w∈D)
    (hwN:w∈fuchsianNielsenCore P hNE)
    (x:P.domain.carrier) :
    P.kleinCoordinate x∈frontier (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)) ↔
      x∈frontier (D∩fuchsianNielsenCore P hNE) := by
  rw [frontier,(show IsClosed (fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)) from
    isClosed_closure).closure_eq,
    nielsenCore_klein_interior hD hNE w hwD hwN]
  rw [(hD.locallyFinite.fundamental.isOpen.inter (fuchsianNielsenCore_isOpen P hNE)).frontier_eq]
  have hc : P.kleinCoordinate x∈fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)↔
      x∈closure (D∩fuchsianNielsenCore P hNE) := by
    rw [P.kleinCoordinate_isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image]
    rfl
  change (_∧P.kleinCoordinate x∉P.kleinCoordinate '' (D∩fuchsianNielsenCore P hNE))↔_
  rw [P.kleinCoordinate_isOpenEmbedding.injective.mem_set_image]
  exact and_congr_left (fun _=>hc)

theorem nielsenCore_klein_extreme_on_line_finite
    (K:Set ℂ) (L:Hyperbolic.DiscLine) : (K.extremePoints ℝ∩Hyperbolic.kleinCoordinate '' L.carrier).Finite := by
  classical
  by_cases hpair:∃v∈K.extremePoints ℝ∩Hyperbolic.kleinCoordinate '' L.carrier,
      ∃u∈K.extremePoints ℝ∩Hyperbolic.kleinCoordinate '' L.carrier,v≠u
  · obtain ⟨v,hv,u,hu,hvu⟩:=hpair
    obtain ⟨a,t,ha,hL⟩:=L.klein_image_carrier
    have hvlev:inner ℝ a v=t:=(hL ▸ hv.2).1
    have hulev:inner ℝ a u=t:=(hL ▸ hu.2).1
    apply (Set.toFinite ({v,u}:Set ℂ)).subset
    rintro z ⟨hz,hzL⟩
    have hzlev:inner ℝ a z=t:=(hL ▸ hzL).1
    rcases _root_.LowDimensionalTopology.Geometry.Euclidean.extreme_inner_level_eq_pair K ha hv.1 hu.1 hz hvu
      (hulev.trans hvlev.symm) (hzlev.trans hvlev.symm) with h|h
    · exact Or.inl h
    · exact Or.inr h
  · apply Set.Subsingleton.finite
    intro v hv u hu
    by_contra h
    exact hpair ⟨v,hv,u,hu,h⟩

theorem finite_nielsenCore_compactKlein_extreme
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (ha:fuchsianNielsenCoreArea P hNE D≠⊤)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    ((fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)).extremePoints ℝ).Finite := by
  let Q:=D∩fuchsianNielsenCore P hNE
  let K:=fuchsianPolygonCompactKlein P Q
  obtain ⟨T,hT,hcover⟩:=nielsenCore_finite_boundary_line_cover hD hNE ha hfin w hwD hwN
  have hE: (⋃L∈T,K.extremePoints ℝ∩Hyperbolic.kleinCoordinate '' L.carrier).Finite :=
    hT.biUnion (fun L _=>nielsenCore_klein_extreme_on_line_finite K L)
  have hI: (fuchsianPolygonIdealBoundary P Q).Finite:=finite_nielsenCore_idealBoundary hD hNE ha
  apply (hI.union hE).subset
  intro z hz
  have hzK:z∈K:=extremePoints_subset hz
  have hbound:‖z‖≤1:=by
    have hsub:K⊆Metric.closedBall (0:ℂ) 1:=by
      apply closure_minimal _ Metric.isClosed_closedBall
      rintro y ⟨x,hx,rfl⟩
      exact Metric.ball_subset_closedBall (P.kleinCoordinate_range ▸ mem_range_self x)
    simpa only [Metric.mem_closedBall,dist_zero_right] using hsub hzK
  by_cases hi:‖z‖=1
  · exact Or.inl ((compactKlein_ideal_mem_iff P Q z hi).mp hzK)
  · have hlt:‖z‖<1:=lt_of_le_of_ne hbound hi
    obtain ⟨x,rfl⟩:=(P.kleinCoordinate_range ▸ (mem_ball_zero_iff.mpr hlt))
    have hxF:P.kleinCoordinate x∈frontier K:=by
      rw [frontier,(show IsClosed K from isClosed_closure).closure_eq]
      refine ⟨hzK,?_⟩
      exact fun hx=>disjoint_left.mp (disjoint_interior_extremePoints K) hx hz
    have hxQ:= (nielsenCore_klein_finite_frontier hD hNE w hwD hwN x).mp hxF
    have hxC:=hcover (mem_image_of_mem P.finiteCoordinate hxQ)
    obtain ⟨L,hxL⟩:=mem_iUnion.mp hxC
    obtain ⟨hLT,hxL⟩:=mem_iUnion.mp hxL
    right
    exact mem_iUnion₂.mpr ⟨L,hLT,hz,P.finiteCoordinate x,hxL,rfl⟩

theorem nielsenCore_actual_cyclic_model
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H) (ha:fuchsianNielsenCoreArea P hNE D≠⊤)
    (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    ∃n:ℕ,∃S:Polygon.CyclicDiscPolygonSupportData n,
      S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE) ∧
      S.toDiscPolygon.interior=P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE) := by
  classical
  let Q:=D∩fuchsianNielsenCore P hNE
  let K:=fuchsianPolygonCompactKlein P Q
  let hE:=finite_nielsenCore_compactKlein_extreme hD hNE ha hfin w hwD hwN
  let V:=hE.toFinset
  have hV:(V:Set ℂ)=K.extremePoints ℝ:=hE.coe_toFinset
  have hconv:Convex ℝ K:=by
    have h:=(Hyperbolic.discHConvex_iff_klein_convex _).mp (nielsenCore_inter_native_convex hD hNE)
    have h':Convex ℝ (P.kleinCoordinate '' Q):=by simpa only [image_image,Fuchsian.UnitDiscFuchsianGroup.kleinCoordinate] using h
    exact h'.closure
  have hK:K=convexHull ℝ (V:Set ℂ):=by
    have he:=closure_convexHull_extremePoints (fuchsianPolygonCompactKlein_compact P Q) hconv
    rw [←hV,(V.finite_toSet.isClosed_convexHull ℝ).closure_eq] at he
    exact he.symm
  have hint:(interior K).Nonempty:=by
    rw [nielsenCore_klein_interior hD hNE w hwD hwN]
    exact ⟨P.kleinCoordinate w,w,⟨hwD,hwN⟩,rfl⟩
  have hcard:3≤V.card:=_root_.LowDimensionalTopology.Geometry.Euclidean.finite_planar_hull_card_ge_three V (hK ▸ hint)
  have hext (z:ℂ) (hz:z∈V):z∈(convexHull ℝ (V:Set ℂ)).extremePoints ℝ:=by
    rw [←hK]
    exact (Set.Finite.mem_toFinset hE).mp hz
  have hdisc (z:ℂ) (hz:z∈V):‖z‖≤1:=by
    have hzK:z∈K:=extremePoints_subset ((Set.Finite.mem_toFinset hE).mp hz)
    have hsub:K⊆Metric.closedBall (0:ℂ) 1:=by
      apply closure_minimal _ Metric.isClosed_closedBall
      rintro y ⟨x,hx,rfl⟩
      exact Metric.ball_subset_closedBall (P.kleinCoordinate_range ▸ mem_range_self x)
    simpa only [Metric.mem_closedBall,dist_zero_right] using hsub hzK
  obtain ⟨n,S,hvertices,hsupport⟩:=Polygon.finite_extreme_cyclic_support_data V hcard hext hdisc
  have hregion:S.toCenteredData.kleinRegion=K:=by
    apply subset_antisymm
    · rw [Polygon.cyclic_support_region_eq_convexHull,hK]
      apply convexHull_mono
      rintro z ⟨i,rfl⟩
      exact hvertices i
    · rw [hK]
      exact convexHull_min (fun z hz=>hsupport z hz) S.toCenteredData.kleinRegion_convex
  refine ⟨n,S,hregion,?_⟩
  change S.toCenteredData.toDiscPolygon.interior=P.finiteCoordinate '' Q
  rw [S.toCenteredData.toDiscPolygon_interior]
  ext z
  change Hyperbolic.kleinCoordinate z∈S.toCenteredData.strictKleinRegion↔_
  rw [←S.toCenteredData.interior_kleinRegion,hregion,nielsenCore_klein_interior hD hNE w hwD hwN]
  have he:P.kleinCoordinate '' Q=Hyperbolic.kleinCoordinate '' (P.finiteCoordinate '' Q):=by
    rw [image_image]
    rfl
  rw [he,Hyperbolic.kleinCoordinate_injective.mem_set_image]

theorem finitelyGenerated_nielsenCore_polygon
    {H:Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG) :
    ∃w:P.domain.carrier,IsDirichletCenter P w ∧ w∈fuchsianNielsenCore P hNE ∧
      ∃n:ℕ,∃S:Polygon.CyclicDiscPolygonSupportData n,
        S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P
          (dirichletDomain P w∩fuchsianNielsenCore P hNE) ∧
        S.toDiscPolygon.interior=P.finiteCoordinate '' (dirichletDomain P w∩fuchsianNielsenCore P hNE) := by
  obtain ⟨w,hw,hwN⟩:=exists_dirichlet_center_in_nielsenCore P hNE
  have hD:=dirichletDomain_isConvexFuchsianPolygon P w hw
  have ha:=finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD.locallyFinite.fundamental
  obtain ⟨n,S,hK,hI⟩:=nielsenCore_actual_cyclic_model hD hNE ha
    (finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw) w
    (dirichletDomain_center_mem P w hw) hwN
  exact ⟨w,hw,hwN,n,S,hK,hI⟩

end LowDimensionalTopology.Geometry.Fuchsian
