module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Polygon.Topology.Jordan.JordanPolygonRegions
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.OriginalJordanPolygonPoincare
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.JordanRegionBounds
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletBoundaryEndpoints
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
open scoped OnePoint

/-- A genuinely preconnected original set avoiding an actual complex Jordan
curve lies wholly on one of its two genuine complementary sides. -/
theorem complexJordan_preconnected_subset_side {C N : Set ℂ}
    (hC : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C) (hN : IsPreconnected N) (hdis :
      Disjoint N C) :
    N ⊆ _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C ∨ N ⊆ _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanOutside C := by
  obtain ⟨hI,hO,hd,hunion,_hIc,_hOc,_hIF,_hOF⟩ := _root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions hC
  have hsub : N ⊆ _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C ∪ _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanOutside C := by
    rw [hunion]
    intro z hz
    exact fun hzC => disjoint_left.mp hdis hz hzC
  exact IsPreconnected.subset_or_subset hI hO hd hsub hN

/-- The genuine finite-plane coordinate of the actual unit-disc carrier is an
open embedding, with the standard complex topology. -/
theorem unitDisc_finite_plane_isOpenEmbedding
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) :
    Topology.IsOpenEmbedding (fun z : P.domain.carrier => (P.finiteCoordinate z : ℂ)) := by
  have hco : Topology.IsOpenEmbedding (fun z : Complex.UnitDisc => (z:ℂ)) := by
    change Topology.IsOpenEmbedding (Subtype.val : Metric.ball (0:ℂ) 1 → ℂ)
    exact (Metric.isOpen_ball : IsOpen (Metric.ball (0:ℂ) 1)).isOpenEmbedding_subtypeVal
  exact hco.comp P.finiteCoordinate.isOpenEmbedding

/-- An actual injective circle in the original disc is a genuine complex Jordan
curve after the true finite-plane coordinate, with no separation hypothesis. -/
theorem unitDisc_injective_circle_isComplexJordanCurve
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {J : Circle → P.domain.carrier} (hJ : Continuous J) (hJi : Function.Injective J) :
    _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve (range (fun u => (P.finiteCoordinate (J u) : ℂ))) := by
  apply _root_.LowDimensionalTopology.Geometry.Polygon.isComplexJordanCurve_of_continuous_injective
  · exact (unitDisc_finite_plane_isOpenEmbedding P).continuous.comp hJ
  · exact (unitDisc_finite_plane_isOpenEmbedding P).injective.comp hJi

/-- A genuine connected original neighborhood whose frontier contains an actual
embedded circle lies wholly on one true Jordan side of that actual circle. -/
theorem unitDisc_frontier_circle_neighborhood_one_side
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {N : Set P.domain.carrier} (hN : IsOpen N) (hNc : IsPreconnected N)
    {J : Circle → P.domain.carrier} (hJ : Continuous J) (hJi : Function.Injective J)
    (hJN : range J ⊆ frontier N) :
    let C := range (fun u => (P.finiteCoordinate (J u) : ℂ))
    (fun z : P.domain.carrier => (P.finiteCoordinate z :
      ℂ)) '' N ⊆ _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C ∨
      (fun z : P.domain.carrier => (P.finiteCoordinate z : ℂ)) '' N ⊆ _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanOutside C := by
  let f := fun z : P.domain.carrier => (P.finiteCoordinate z : ℂ)
  have hf := unitDisc_finite_plane_isOpenEmbedding P
  apply complexJordan_preconnected_subset_side (unitDisc_injective_circle_isComplexJordanCurve P hJ hJi)
    (hNc.image f hf.continuous.continuousOn)
  apply disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ ⟨u,hu⟩
  have hxEq : J u = x := hf.injective hu
  have hxfront : x ∈ frontier N := hxEq ▸ hJN (mem_range_self u)
  exact (disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hN)) hxfront hx

/-- The actual closed unit disc contains no infinite point of the Riemann sphere. -/
theorem infty_not_mem_unitDisc_closure :
    (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∉ closure _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_closure_unitDisc]
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedClosedUnitDisc,mem_image]
  rintro ⟨z,_hz,hz⟩
  exact OnePoint.coe_ne_infty z hz

/-- A genuine sphere-valued Jordan parametrization avoiding infinity is a
genuine complex Jordan parametrization through the true finite chart. -/
theorem sphere_finite_injective_circle_isComplexJordanCurve
    {J : Circle → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hJ : Continuous J) (hJi :
      Function.Injective J)
    (hfinite : ∀ u, J u ≠ ∞) : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve (range (fun u => _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u))) := by
  have hsource : ∀ u, J u ∈ _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart.source := by
    intro u
    rw [_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart_source]
    exact hfinite u
  apply _root_.LowDimensionalTopology.Geometry.Polygon.isComplexJordanCurve_of_continuous_injective
  · exact _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart.continuousOn.comp_continuous hJ hsource
  · intro u v he
    exact hJi (_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart.injOn (hsource u) (hsource v) he)

/-- The genuine sphere finite chart agrees with the original actual disc's
complex coordinate at every original interior point. -/
theorem sphereFiniteChart_unitDisc_coordinate
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (z :
      P.domain.carrier) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart z.val = (P.finiteCoordinate z : ℂ) := by
  have hz : (((P.finiteCoordinate z : ℂ)) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = z.val := _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteChart_coe z
  rw [←hz,_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart_coe]

/-- The actual bounded Jordan side of any curve contained in a genuine closed
disc lies strictly inside the corresponding open disc, even if the curve touches
the boundary circle. -/
theorem complexJordanInside_subset_ball_of_subset_closedBall
    {C : Set ℂ} {r : ℝ} (hr : 0 < r) (hC : C ⊆ Metric.closedBall (0:ℂ) r) :
    _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C ⊆ Metric.ball (0:ℂ) r :=
  _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside_subset_ball hr hC

/-- A genuine compact subset of the open unit ball fits inside a strictly
smaller positive closed ball. -/
theorem compact_subset_unitBall_smaller_closedBall
    {E : Type*} [NormedAddCommGroup E] {K : Set E} (hK : IsCompact K)
    (hsub : K ⊆ Metric.ball (0:E) 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ K ⊆ Metric.closedBall (0:E) r := by
  rcases K.eq_empty_or_nonempty with hE | hne
  · exact ⟨1/2,by norm_num,by norm_num,hE ▸ empty_subset _⟩
  obtain ⟨z,hz,hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  have hz1 : ‖z‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hsub hz
  refine ⟨(‖z‖+1)/2,by linarith [norm_nonneg z],by linarith,?_⟩
  intro x hx
  change dist x 0 ≤ (‖z‖+1)/2
  rw [dist_zero_right]
  have hh : ‖x‖ ≤ ‖z‖ := hmax hx
  linarith

/-- An actual properly discontinuous action of an infinite group cannot place
an entire original orbit inside a genuine compact set. -/
theorem properlyDiscontinuous_orbit_not_subset_compact
    {G X : Type*} [Group G] [Infinite G] [TopologicalSpace X] [MulAction G X]
    [ProperlyDiscontinuousSMul G X] (x : X) {K : Set X} (hK : IsCompact K) :
    ¬∀ g : G, g • x ∈ K := by
  intro horbit
  have hfin : {g : G | ((fun y : X => g • y) '' ({x}:Set X) ∩ K).Nonempty}.Finite :=
    ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) isCompact_singleton hK
  apply (Set.infinite_univ : (univ : Set G).Infinite)
  apply hfin.subset
  intro g _hg
  exact ⟨g • x,⟨x,mem_singleton x,rfl⟩,horbit g⟩

/-- The genuine finite coordinate pulls a smaller closed complex disc back to
a compact subset of the original actual unit-disc carrier. -/
theorem unitDisc_finite_plane_small_closedBall_preimage_compact
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) {r :
      ℝ} (hr : r < 1) :
    IsCompact ((fun z : P.domain.carrier => (P.finiteCoordinate z : ℂ)) ⁻¹'
      Metric.closedBall (0:ℂ) r) := by
  apply (unitDisc_finite_plane_isOpenEmbedding P).isEmbedding.isInducing.isCompact_preimage'
    (isCompact_closedBall (0:ℂ) r)
  intro z hz
  have hn : ‖z‖ < 1 := by
    have hzr : ‖z‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    exact hzr.trans_lt hr
  let u : Complex.UnitDisc := Complex.UnitDisc.mk z hn
  refine ⟨P.finiteCoordinate.symm u,?_⟩
  exact congrArg (fun v : Complex.UnitDisc => (v:ℂ)) (P.finiteCoordinate.apply_symm_apply u)

/-- An actual disc-valued Jordan circle has an actual compact closed inside in
the original disc; its compactness is derived from its genuine image. -/
theorem unitDisc_Jordan_inside_closure_preimage_compact
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {J : Circle → P.domain.carrier} (hJ : Continuous J) :
    IsCompact ((fun z : P.domain.carrier => (P.finiteCoordinate z : ℂ)) ⁻¹'
      closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside (range (fun u => (P.finiteCoordinate (J u) : ℂ))))) := by
  let f := fun z : P.domain.carrier => (P.finiteCoordinate z : ℂ)
  let C := range (fun u => f (J u))
  have hc : IsCompact C := isCompact_range ((unitDisc_finite_plane_isOpenEmbedding P).continuous.comp hJ)
  have hCB : C ⊆ Metric.ball (0:ℂ) 1 := by
    rintro z ⟨u,rfl⟩
    change dist (P.finiteCoordinate (J u):ℂ) 0 < 1
    rw [dist_zero_right]
    exact Complex.UnitDisc.norm_lt_one _
  obtain ⟨r,hr,hr1,hCr⟩ := compact_subset_unitBall_smaller_closedBall hc hCB
  have hIc : closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside
    C) ⊆ Metric.closedBall (0:ℂ) r :=
    closure_minimal ((complexJordanInside_subset_ball_of_subset_closedBall hr hCr).trans
      Metric.ball_subset_closedBall) Metric.isClosed_closedBall
  apply (unitDisc_finite_plane_small_closedBall_preimage_compact P hr1).of_isClosed_subset
    (isClosed_closure.preimage (unitDisc_finite_plane_isOpenEmbedding P).continuous)
  exact preimage_mono hIc

/-- Non-elementarity excludes an entire actual original orbit lying inside any
actual disc-valued Jordan circle, by proper discontinuity and true compactness. -/
theorem unitDisc_nonElementary_orbit_not_inside_circle
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (w : P.domain.carrier)
    {J : Circle → P.domain.carrier} (hJ : Continuous J) :
    ¬∀ g : H, (P.finiteCoordinate (g • w) : ℂ) ∈
      _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside (range (fun u => (P.finiteCoordinate (J u) : ℂ))) := by
  let : Infinite H := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.nonElementary_infinite H hNE
  let : ProperlyDiscontinuousSMul H P.domain.carrier :=
    _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomain_properlyDiscontinuous P.domain P.discontinuous
  intro hInside
  apply properlyDiscontinuous_orbit_not_subset_compact (G := H) w
    (unitDisc_Jordan_inside_closure_preimage_compact P hJ)
  intro g
  exact subset_closure (hInside g)

namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

/-- In the genuine finite-return case, the original connected full-orbit
neighborhood lies on the actual unbounded Jordan side. The other actual closed
side is compact in the original disc, with no assumed separation or compactness. -/
theorem finite_period_neighborhood_outside (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary
  H)
    (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius)
    (hpos : 0 < d.endpointPeriod hw x) :
    ∃ J : Circle → P.domain.carrier, Continuous J ∧ Function.Injective J ∧
      range J = ⋃ i ∈ Iio (d.endpointPeriod hw x), d.developedClosedArc hw x i ∧
      range J ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) ∧
      (fun z : P.domain.carrier => (P.finiteCoordinate z : ℂ)) ''
        _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius ⊆
          _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanOutside (range (fun u => (P.finiteCoordinate (J u)
            : ℂ))) ∧
      IsCompact ((fun z : P.domain.carrier => (P.finiteCoordinate z : ℂ)) ⁻¹'
        closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside (range (fun u => (P.finiteCoordinate (J u) : ℂ))))) := by
  obtain ⟨J,hJ,hJi,hJrange,hfront⟩ := d.finite_period_exists_jordan_curve hw x hpos
  have hside := _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_frontier_circle_neighborhood_one_side P d.orbit_neighborhood_open
    d.orbit_neighborhood_connected.isPreconnected hJ hJi hfront
  have hOrbit (g : H) : g • w ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius := by
    apply mem_iUnion.mpr
    refine ⟨g,?_⟩
    change dist (P.halfPlaneCoordinate (g • w)) (P.halfPlaneCoordinate (g • w)) < d.radius
    simpa only [dist_self] using d.radius_pos
  have hout := hside.resolve_left fun hInside =>
    _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_nonElementary_orbit_not_inside_circle P hNE w hJ
      (fun g => hInside ⟨g • w,hOrbit g,rfl⟩)
  exact ⟨J,hJ,hJi,hJrange,hfront,hout,_root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_Jordan_inside_closure_preimage_compact P hJ⟩

end RegularDirichletCircleData


/-- The genuine bounded side of a Jordan curve in the closed unit disc has a
compact complex closure, even when the curve meets the bounding circle. -/
theorem complexJordanInside_closure_compact_of_subset_closedUnitBall
    {C : Set ℂ} (hC : C ⊆ Metric.closedBall (0:ℂ) 1) :
    IsCompact (closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C)) := by
  apply (isCompact_closedBall (0:ℂ) 1).of_isClosed_subset isClosed_closure
  exact closure_minimal
    ((complexJordanInside_subset_ball_of_subset_closedBall zero_lt_one hC).trans
      Metric.ball_subset_closedBall) Metric.isClosed_closedBall

/-- An actual original non-elementary disc orbit cannot lie in the bounded
Jordan side when that curve has only countably many genuine unit-circle points.
The proof uses the true whole-group limit set, without a compactness assumption
on the corresponding region in the original open disc. -/
theorem unitDisc_nonElementary_orbit_not_inside_countable_boundary
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (w : P.domain.carrier)
    {C : Set ℂ} (hJ : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C)
    (hC : C ⊆ Metric.closedBall (0:ℂ) 1)
    (hCount : (C ∩ Metric.sphere (0:ℂ) 1).Countable) :
    ¬∀ g : H, (P.finiteCoordinate (g • w) : ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C := by
  intro horbit
  let I := _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C
  let K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := (fun z : ℂ =>
    (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) '' closure I
  have hK : IsClosed K :=
    ((complexJordanInside_closure_compact_of_subset_closedUnitBall hC).image
      OnePoint.continuous_coe).isClosed
  have horbK : MulAction.orbit H w.val ⊆ K := by
    rintro z ⟨g,rfl⟩
    refine ⟨(P.finiteCoordinate (g • w):ℂ),subset_closure (horbit g),?_⟩
    exact _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteChart_coe (g • w)
  have hLK : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H ⊆ K :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet_subset_closure_orbit H hNE w.val).trans
      (closure_minimal horbK hK)
  have hID : I ⊆ Metric.ball (0:ℂ) 1 :=
    complexJordanInside_subset_ball_of_subset_closedBall zero_lt_one hC
  have hLcontact : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H ⊆
      (fun z : ℂ => (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) '' (C ∩ Metric.sphere (0:ℂ) 1) := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := hLK hz
    have hvcl : v ∈ Metric.closedBall (0:ℂ) 1 :=
      closure_minimal (hID.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall hv
    have hvnot : v ∉ I := by
      intro hvI
      have hvD : (v:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ P.domain.carrier := by
        change (v:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
        rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc]
        simpa only [Metric.mem_ball,dist_zero_right] using hID hvI
      exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_discontinuous_open_subset_ordinary H
        P.domain.carrier
        P.domain.isOpen P.discontinuous hvD) hz
    have hvfront : v ∈ frontier I := by
      rw [(_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions hJ).1.frontier_eq]
      exact ⟨hv,hvnot⟩
    have hvC : v ∈ C := by
      rwa [(_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions hJ).2.2.2.2.2.2.1] at hvfront
    have hvnorm : ‖v‖ = 1 := by
      apply le_antisymm
      · simpa only [Metric.mem_closedBall,dist_zero_right] using hvcl
      · by_contra h
        have hvD : (v:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ P.domain.carrier := by
          change (v:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
          rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc]
          exact lt_of_not_ge h
        exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_discontinuous_open_subset_ordinary H
          P.domain.carrier
          P.domain.isOpen P.discontinuous hvD) hz
    refine ⟨v,⟨hvC,?_⟩,rfl⟩
    simpa only [Metric.mem_sphere,dist_zero_right] using hvnorm
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet_not_countable H hNE
    ((hCount.image (fun z : ℂ => (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))).mono hLcontact)


/-- The genuine sphere finite chart recovers every point of the actual closed
unit disc as a true finite complex point. -/
theorem sphereFiniteChart_coe_of_mem_unitDisc_closure
    {z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hz : z ∈ closure
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    ((_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = z := by
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_closure_unitDisc] at hz
  obtain ⟨v,_hv,rfl⟩ := hz
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart_coe]

theorem sphereFiniteChart_norm_le_one_of_mem_unitDisc_closure
    {z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hz : z ∈ closure
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    ‖_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart z‖ ≤ 1 := by
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_closure_unitDisc] at hz
  obtain ⟨v,hv,rfl⟩ := hz
  rwa [_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart_coe]

/-- A genuine Jordan compactification with one original disc-boundary endpoint
has a genuine complex Jordan image in the closed unit disc. Its actual contact
with the bounding circle contains at most that one named endpoint. -/
theorem unitDisc_one_endpoint_Jordan_finite_data
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {F : ℝ → P.domain.carrier} {a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (ha : a ∈ frontier P.domain.carrier)
    {J : Circle → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hJ : Continuous J) (hJi :
      Function.Injective J)
    (hRange : range J = insert a (range (fun t => (F t).val))) :
    let C := range (fun u => _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u))
    _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C ∧ C ⊆ Metric.closedBall (0:ℂ) 1 ∧
      C ∩ Metric.sphere (0:ℂ) 1 ⊆ {_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart a} := by
  let C := range (fun u => _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u))
  have hcl : range J ⊆ closure _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    rw [hRange]
    apply insert_subset
    · exact frontier_subset_closure ha
    · rintro z ⟨t,rfl⟩
      exact subset_closure (F t).property
  have hfin (u : Circle) : J u ≠ ∞ := by
    intro he
    exact infty_not_mem_unitDisc_closure (he ▸ hcl (mem_range_self u))
  refine ⟨sphere_finite_injective_circle_isComplexJordanCurve hJ hJi hfin,?_,?_⟩
  · rintro z ⟨u,rfl⟩
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      sphereFiniteChart_norm_le_one_of_mem_unitDisc_closure (hcl (mem_range_self u))
  · rintro z ⟨⟨u,rfl⟩,hzsphere⟩
    have hnorm : ‖_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u)‖ = 1 := by
      simpa only [Metric.mem_sphere,dist_zero_right] using hzsphere
    have hJu : J u ∈ insert a (range (fun t => (F t).val)) := hRange ▸ mem_range_self u
    rcases mem_insert_iff.mp hJu with he | he
    · exact mem_singleton_iff.mpr (congrArg _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart he)
    · obtain ⟨t,ht⟩ := he
      have hn : ‖_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u)‖ < 1 := by
        rw [←ht,sphereFiniteChart_unitDisc_coordinate P]
        exact Complex.UnitDisc.norm_lt_one _
      exact False.elim ((ne_of_lt hn) hnorm)

/-- For a genuine Jordan curve in the actual closed unit disc, the closed
bounded side has exactly the same true unit-circle contact as the curve. -/
theorem complexJordanInside_closure_sphere_eq
    {C : Set ℂ} (hJ : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C)
    (hC : C ⊆ Metric.closedBall (0:ℂ) 1) :
    closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C) ∩ Metric.sphere (0:ℂ) 1 = C ∩ Metric.sphere (0:ℂ) 1 := by
  have hfr := (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions hJ).2.2.2.2.2.2.1
  have hOpen := (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions hJ).1
  have hIB := complexJordanInside_subset_ball_of_subset_closedBall zero_lt_one hC
  apply subset_antisymm
  · intro z hz
    have hznot : z ∉ _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C := by
      intro hzI
      have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hIB hzI
      have he : ‖z‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hz.2
      exact (ne_of_lt hn) he
    refine ⟨?_,hz.2⟩
    rw [←hfr,hOpen.frontier_eq]
    exact ⟨hz.1,hznot⟩
  · intro z hz
    refine ⟨?_,hz.2⟩
    exact frontier_subset_closure (hfr.symm ▸ hz.1)

/-- In the actual one-end compactification case, an original connected open
full-orbit neighbourhood lies on the genuine unbounded Jordan side. Its bounded
side lies in the original disc and its closed unit-circle contact is at most
the unique actual parabolic endpoint. No finite-end conclusion is assumed. -/
theorem unitDisc_one_endpoint_frontier_neighborhood_outside
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (w : P.domain.carrier)
    {N : Set P.domain.carrier} (hN : IsOpen N) (hNc : IsPreconnected N)
    (hOrb : ∀ g : H, g • w ∈ N)
    {F : ℝ → P.domain.carrier} (hF : range F ⊆ frontier N)
    {a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (ha : a ∈ frontier P.domain.carrier)
    {J : Circle → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hJ : Continuous J) (hJi :
      Function.Injective J)
    (hRange : range J = insert a (range (fun t => (F t).val))) :
    let C := range (fun u => _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u))
    _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C ∧
      (fun z : P.domain.carrier => (P.finiteCoordinate z :
        ℂ)) '' N ⊆ _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanOutside C ∧
      _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C ⊆ Metric.ball (0:ℂ) 1 ∧
      closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C) ∩ Metric.sphere (0:ℂ) 1 ⊆ {_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart a} := by
  let C := range (fun u => _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u))
  obtain ⟨hCJ,hCB,hContact⟩ := unitDisc_one_endpoint_Jordan_finite_data P ha hJ hJi hRange
  let f := fun z : P.domain.carrier => (P.finiteCoordinate z : ℂ)
  have hCont : Continuous f := (unitDisc_finite_plane_isOpenEmbedding P).continuous
  have hDis : Disjoint (f '' N) C := by
    apply disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ ⟨u,hu⟩
    have hcl : J u ∈ closure _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
      have hm : J u ∈ insert a (range (fun t => (F t).val)) := hRange ▸ mem_range_self u
      rcases mem_insert_iff.mp hm with he | he
      · exact he ▸ frontier_subset_closure ha
      · obtain ⟨t,ht⟩ := he
        exact ht ▸ subset_closure (F t).property
    have hco : ((_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J
      u):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = J u :=
      sphereFiniteChart_coe_of_mem_unitDisc_closure hcl
    have hJu : J u = x.val := by
      change _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u) = f x at hu
      rw [←hco,hu]
      exact _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteChart_coe x
    have hmem : x.val ∈ insert a (range (fun t => (F t).val)) := by
      rw [←hRange,←hJu]
      exact mem_range_self u
    rcases mem_insert_iff.mp hmem with he | he
    · have hax : a ∈ P.domain.carrier := he ▸ x.property
      exact (disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr P.domain.isOpen)) ha hax
    · obtain ⟨t,ht⟩ := he
      have htx : F t = x := Subtype.ext ht
      have hxfr : x ∈ frontier N := htx ▸ hF (mem_range_self t)
      exact (disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hN)) hxfr hx
  have hSide := complexJordan_preconnected_subset_side hCJ
    (hNc.image f hCont.continuousOn) hDis
  have hOutside := hSide.resolve_left fun hInside =>
    unitDisc_nonElementary_orbit_not_inside_countable_boundary P hNE w hCJ hCB
      ((Set.countable_singleton (_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart a)).mono hContact)
      (fun g => hInside ⟨g • w,hOrb g,rfl⟩)
  refine ⟨hCJ,hOutside,complexJordanInside_subset_ball_of_subset_closedBall zero_lt_one hCB,?_⟩
  rw [complexJordanInside_closure_sphere_eq hCJ hCB]
  exact hContact


namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

/-- The genuine one-end compactification of an actual aperiodic developed
frontier curve puts the full original orbit neighbourhood on the true outside.
The other side lies in the disc and its genuine ideal closure has at most the
single actual parabolic endpoint. -/
theorem parabolic_compactification_neighborhood_outside
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H)
    {k : H} {F : ℝ → P.domain.carrier}
    (hF : range F ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius))
    (hShape : _root_.LowDimensionalTopology.Geometry.Fuchsian.DiscFrontierCurveCompactification P k F) (hpar :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic k.val) :
    ∃ a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, (k.val : Equiv.Perm
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) a = a ∧
      a ∈ frontier P.domain.carrier ∧
      ∃ J : Circle → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, Continuous J ∧ Function.Injective J ∧
        range J = closure (range (fun t => (F t).val)) ∧
        range J = insert a (range (fun t => (F t).val)) ∧
        _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve (range (fun u =>
          _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u))) ∧
        (fun z : P.domain.carrier => (P.finiteCoordinate z : ℂ)) ''
          _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius ⊆
          _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanOutside (range (fun u =>
            _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u))) ∧
        _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside (range (fun u =>
          _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u))) ⊆ Metric.ball (0:ℂ) 1 ∧
        closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside (range (fun u =>
          _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u)))) ∩
          Metric.sphere (0:ℂ) 1 ⊆ {_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart a} := by
  rcases hShape with h | h
  · obtain ⟨_hp,a,hfix,ha,J,hJ,hJi,hJcl,hJrange,_hJint⟩ := h
    have hOrb (g : H) : g • w ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius := by
      apply mem_iUnion.mpr
      refine ⟨g,?_⟩
      change dist (P.halfPlaneCoordinate (g • w)) (P.halfPlaneCoordinate (g • w)) < d.radius
      simpa only [dist_self] using d.radius_pos
    obtain ⟨hCJ,hOut,hIn,hContact⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_one_endpoint_frontier_neighborhood_outside
      P hNE w d.orbit_neighborhood_open d.orbit_neighborhood_connected.isPreconnected
      hOrb hF ha hJ hJi hJrange
    exact ⟨a,hfix,ha,J,hJ,hJi,hJcl,hJrange,hCJ,hOut,hIn,hContact⟩
  · exact False.elim (h.1.1.not_parabolic hpar)

end RegularDirichletCircleData

end LowDimensionalTopology.Geometry.Fuchsian
