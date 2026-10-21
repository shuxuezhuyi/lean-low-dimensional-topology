module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonLocalGeometry
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped Complex.UnitDisc Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Surfaces

theorem IsConvexFuchsianPolygon.normalizedKlein_frontier_iff
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x y : P.domain.carrier) :
    normalizedPolygonKleinCoordinate P x y ∈
      frontier (normalizedPolygonKleinCoordinate P x '' closure D) ↔ y ∈ frontier D := by
  let F := normalizedPolygonKleinCoordinate P x
  have hF := normalizedPolygonKleinCoordinate_isOpenEmbedding P x
  have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hfront : frontier (closure D) = frontier D := by
    simp only [frontier,closure_closure,hD.interior_closure,hDo.interior_eq]
  have he := hF.isOpenMap.preimage_frontier_eq_frontier_preimage hF.continuous (F '' closure D)
  rw [hF.injective.preimage_image,hfront] at he
  exact Set.ext_iff.mp he y

theorem IsConvexFuchsianPolygon.exists_local_boundary_ray
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) (hx : x ∈ frontier D) :
    ∃ (v : ℂ) (N : Set ℂ), v ≠ 0 ∧ IsOpen N ∧ (0 : ℂ) ∈ N ∧
      ∀ t : ℝ, 0 ≤ t → t • v ∈ N →
        t • v ∈ frontier (normalizedPolygonKleinCoordinate P x '' closure D) := by
  rcases hD.boundary_geometric_angle x hx with ⟨q,N,hq,hN,h0N,he,_hangle⟩ |
    ⟨u,v,N,hu,hv,_hθpos,_hθ,hN,h0N,he,_hangle⟩
  · let v := Complex.I*q
    have hv : v ≠ 0 := mul_ne_zero Complex.I_ne_zero hq
    have hqv : inner ℝ q v = 0 := by simp [v,Complex.inner]; ring
    refine ⟨v,N,hv,hN,h0N,fun t ht htN => ?_⟩
    have hz : t • v ∈ frontier {z : ℂ | inner ℝ q z ≤ 0} := by
      apply mem_frontier_of_supporting_halfplane hq (subset_refl _)
      · change inner ℝ q (t • v) ≤ 0
        rw [real_inner_smul_right,hqv,mul_zero]
      · rw [real_inner_smul_right,hqv,mul_zero]
    have hg := frontiers_equal_on_open_germ hN he
    exact (hg.symm ▸ (show t • v ∈ frontier {z : ℂ | inner ℝ q z ≤ 0} ∩ N from ⟨hz,htN⟩)).1
  · refine ⟨u,N,hu,hN,h0N,fun t ht htN => ?_⟩
    have hg := frontiers_equal_on_open_germ hN he
    exact (hg.symm ▸ (show t • u ∈ frontier
      {z : ℂ | ∃ α : ℝ, 0 ≤ α ∧ ∃ β : ℝ, 0 ≤ β ∧ z = α • u + β • v} ∩ N from
        ⟨positive_cone_boundary_ray u v hu t ht,htN⟩)).1

/-- The original polygon has no isolated boundary points in the genuine hyperbolic plane. -/
theorem IsConvexFuchsianPolygon.boundary_accumulates
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (x : P.domain.carrier) (hx : x ∈ frontier D)
    (U : Set P.domain.carrier) (hU : U ∈ 𝓝 x) :
    ∃ y ∈ frontier D ∩ U, y ≠ x := by
  obtain ⟨V,hVU,hVo,hxV⟩ := mem_nhds_iff.mp hU
  let F := normalizedPolygonKleinCoordinate P x
  have hF := normalizedPolygonKleinCoordinate_isOpenEmbedding P x
  obtain ⟨v,N,hv,hN,h0N,hboundary⟩ := hD.exists_local_boundary_ray x hx
  have hFV : IsOpen (F '' V) := hF.isOpenMap V hVo
  have h0FV : (0 : ℂ) ∈ F '' V := ⟨x,hxV,normalizedPolygonKleinCoordinate_self P x⟩
  have hW : N ∩ (F '' V) ∈ 𝓝 (0 : ℂ) := (hN.inter hFV).mem_nhds ⟨h0N,h0FV⟩
  have hc : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
  have hpre : (fun t : ℝ => t • v) ⁻¹' (N ∩ (F '' V)) ∈ 𝓝 (0 : ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa only [zero_smul] using hW
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hhalf : r/2 ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0 < r/2)]
    linarith
  obtain ⟨htN,y,hyV,hey⟩ := hball hhalf
  change normalizedPolygonKleinCoordinate P x y = (r/2) • v at hey
  have hyfront : y ∈ frontier D :=
    (hD.normalizedKlein_frontier_iff x y).mp (hey.symm ▸ hboundary (r/2) (by positivity) htN)
  refine ⟨y,⟨hyfront,hVU hyV⟩, ?_⟩
  intro hyx
  have hezero : (r/2) • v = (0 : ℂ) := by
    calc
      _ = normalizedPolygonKleinCoordinate P x y := hey.symm
      _ = normalizedPolygonKleinCoordinate P x x := congrArg (normalizedPolygonKleinCoordinate P x) hyx
      _ = 0 := normalizedPolygonKleinCoordinate_self P x
  exact (smul_ne_zero (by positivity : r/2 ≠ 0) hv) hezero

/-- Every genuine boundary point lies on a positive-length side defined by a closed-tile intersection. -/
theorem IsConvexFuchsianPolygon.boundary_mem_side
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    {x : P.domain.carrier} (hx : x ∈ frontier D) :
    ∃ S : Set P.domain.carrier, IsFuchsianPolygonSide P D S ∧ x ∈ S := by
  classical
  obtain ⟨N,_hNc,hNx,_hf,_hcover,hd⟩ := hD.locallyFinite.finite_neighborhood_star x
  obtain ⟨y,⟨hyfront,hyN⟩,hyx⟩ := hD.boundary_accumulates x hx N hNx
  obtain ⟨g,hg,hgy⟩ := hD.boundary_mate hyfront
  have hgi : g⁻¹ ≠ 1 := inv_ne_one.mpr hg
  have hytile : y ∈ fuchsianDomainTile P D g⁻¹ :=
    ⟨g • y,frontier_subset_closure hgy,inv_smul_smul g y⟩
  have hxtile : x ∈ fuchsianDomainTile P D g⁻¹ := by
    by_contra hnot
    exact (Set.disjoint_left.mp (hd g⁻¹ hnot) hyN hytile)
  refine ⟨closure D ∩ fuchsianDomainTile P D g⁻¹, ?_,⟨frontier_subset_closure hx,hxtile⟩⟩
  apply hD.side_iff.mpr
  exact ⟨g⁻¹,hgi,rfl,x,⟨frontier_subset_closure hx,hxtile⟩,
    y,⟨frontier_subset_closure hyfront,hytile⟩,Ne.symm hyx⟩

/-- The polygon frontier is exactly the union of its genuine sides. -/
theorem IsConvexFuchsianPolygon.boundary_eq_union_sides
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    frontier D = ⋃ S ∈ {S | IsFuchsianPolygonSide P D S}, S := by
  ext x
  constructor
  · intro hx
    obtain ⟨S,hS,hxS⟩ := hD.boundary_mem_side hx
    exact mem_iUnion₂.mpr ⟨S,hS,hxS⟩
  · intro hx
    obtain ⟨S,hS,hxS⟩ := mem_iUnion₂.mp hx
    exact hS.subset_frontier hD.locallyFinite.fundamental hxS

end LowDimensionalTopology.Geometry.Fuchsian
