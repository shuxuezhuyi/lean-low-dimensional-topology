module
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.ConvexRadial
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.HyperbolicEndRegions
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Topology
open scoped OnePoint Complex.UnitDisc Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

/-- The literal cut-indexed component arcs cover the whole actual open
Dirichlet circle slice. Coverage is derived from true component endpoints and
the actual unique-incidence theorem. -/
theorem components_cover_region (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (u : Circle) (hu : u ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleRegion P w d.radius
      d.radius_pos) :
    ∃ x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius, u ∈ d.component hw x := by
  let U := _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleRegion P w d.radius d.radius_pos
  let V := connectedComponentIn U u
  have hV : V ∈ ((fun x => connectedComponentIn U x) '' U) := ⟨u,hu,rfl⟩
  obtain ⟨p,q,_hpq,hp,_hq,hVends⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.circle_component_boundary_pair
    d.region_isOpen d.exterior d.exterior_not_closure hV
  let x := d.cutEquiv hw ⟨p,hp⟩
  have hC := d.component_spec hw x
  have hpV : p ∈ closure V := by
    have hh : p ∈ closure V \ V := hVends.symm ▸ (show p ∈ {p,q} from Or.inl rfl)
    exact hh.1
  have hpC : p ∈ closure (d.component hw x) := by
    have hh : p ∈ closure (d.component hw x) \ d.component hw x := by
      rw [hC.2]
      apply Or.inl
      exact congrArg Subtype.val ((d.cutEquiv hw).symm_apply_apply ⟨p,hp⟩).symm
    exact hh.1
  obtain ⟨W,_hW,huniq⟩ := d.unique_incidence p hp
  have hVW : V = W := huniq V ⟨hV,hpV⟩
  have hCW : d.component hw x = W := huniq _ ⟨hC.1,hpC⟩
  refine ⟨x,?_⟩
  rw [hCW,←hVW]
  exact mem_connectedComponentIn hu

/-- Every actual polygon point on the regular metric circle lies on one of
the original literal cut-indexed open arcs. -/
theorem originalArcs_cover_metric_circle (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (z : P.domain.carrier) (hz : z ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w)
    (hzR : P.hyperbolicDist w z = d.radius) :
    ∃ x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius, z ∈ d.originalArc hw x := by
  let e := _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianMetricCircleHomeomorph P w d.radius d.radius_pos
  let zc : {z : P.domain.carrier | P.hyperbolicDist w z = d.radius} := ⟨z,hzR⟩
  let u := e.symm zc
  have heu : d.coordinate u = z := congrArg Subtype.val (e.apply_symm_apply zc)
  have hu : u ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleRegion P w d.radius d.radius_pos := by
    change d.coordinate u ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w
    rwa [heu]
  obtain ⟨x,hx⟩ := d.components_cover_region hw u hu
  exact ⟨x,u,hx,heu⟩

/-- The literal strict radial end of the original Dirichlet polygon based on
the actual component arc indexed by a genuine cut point. -/
def radialEnd (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    Set P.domain.carrier :=
  {z | z ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w ∧ d.radius < P.hyperbolicDist w z ∧
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection (Real.tanh
      d.radius) (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w z) ∈
      _root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x}

/-- The finitely many original cut-indexed radial ends cover the entire
genuine strict exterior of the original polygon. -/
theorem radial_ends_cover_strict_exterior (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) :
    {z : P.domain.carrier | z ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w ∧ d.radius <
      P.hyperbolicDist w z} ⊆
      ⋃ x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius, d.radialEnd hw x := by
  let f := _root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w
  let U := f '' _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w
  let r := Real.tanh d.radius
  have hr : 0 < r := by
    apply lt_of_not_ge
    intro h
    have hh := (_root_.LowDimensionalTopology.Geometry.Fuchsian.tanh_radial_order_iff d.radius 0).mp (by simpa only [Real.tanh_zero] using h)
    exact d.radius_pos.not_ge hh
  have hUc : Convex ℝ U := by
    have hD := _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain_isConvexFuchsianPolygon P w hw
    have hh := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex
      _).mp (hD.pointCoordinate_smul_convex w (1:H))
    change Convex ℝ ((fun x => _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      ((_root_.LowDimensionalTopology.Geometry.Fuchsian.polygonPointCoordinate P w) x)) ''
      _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w)
    simpa only [one_smul,image_image] using hh
  have h0 : (0:ℂ) ∈ U :=
    ⟨w,_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain_center_mem P w
      hw,_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate_self P w⟩
  rintro z ⟨hzD,hzR⟩
  have hzn : r < ‖f z‖ := by
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist]
    apply lt_of_not_ge
    intro hh
    exact hzR.not_ge ((_root_.LowDimensionalTopology.Geometry.Fuchsian.tanh_radial_order_iff (P.hyperbolicDist w z)
      d.radius).mp hh)
  have hzNe : f z ≠ 0 := norm_pos_iff.mp (hr.trans hzn)
  obtain ⟨v,hvD,hvf⟩ := _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection_mem_convex hUc h0 r hr ⟨z,hzD,rfl⟩ hzn.le
  have hvNorm : ‖f v‖ = r := by
    rw [hvf]
    exact _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection_norm r hr hzNe
  have hvTanh : Real.tanh (P.hyperbolicDist w v) = Real.tanh d.radius := by
    rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist]
    exact hvNorm
  have hvR : P.hyperbolicDist w v = d.radius := le_antisymm
    ((_root_.LowDimensionalTopology.Geometry.Fuchsian.tanh_radial_order_iff (P.hyperbolicDist w v) d.radius).mp
      hvTanh.le)
    ((_root_.LowDimensionalTopology.Geometry.Fuchsian.tanh_radial_order_iff d.radius (P.hyperbolicDist w v)).mp
      hvTanh.ge)
  obtain ⟨x,hvx⟩ := d.originalArcs_cover_metric_circle hw v hvD hvR
  exact mem_iUnion.mpr ⟨x,hzD,hzR,v,hvx,hvf⟩

include d in
/-- All actual sides of a regular Dirichlet polygon form a finite family.
The proof uses the actual compact central ball and the full closed radial ends,
whose original index set is proved finite. -/
theorem sides_finite (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hw :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) :
    {S : Set P.domain.carrier | _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianPolygonSide P (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w) S}.Finite := by
  let : Finite (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :=
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts_finite P w hw d.radius).to_subtype
  let B : Set P.domain.carrier := {z | P.hyperbolicDist w z ≤ d.radius}
  have hBc : IsCompact B := by
    have hh := P.halfPlaneCoordinate.isCompact_preimage.mpr
      (isCompact_closedBall (P.halfPlaneCoordinate w) d.radius)
    convert hh using 1
    ext z
    change P.hyperbolicDist w z ≤ d.radius ↔ dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate w) ≤ d.radius
    rw [dist_comm]
    rfl
  have hDB : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w ⊆ B ∪ ⋃ x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius, d.radialEnd hw x := by
    intro z hz
    by_cases hzB : P.hyperbolicDist w z ≤ d.radius
    · exact Or.inl hzB
    · exact Or.inr (d.radial_ends_cover_strict_exterior hw ⟨hz,lt_of_not_ge hzB⟩)
  have hclDB : closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w) ⊆
      B ∪ ⋃ x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius, closure (d.radialEnd hw x) := by
    apply closure_minimal
    · intro z hz
      rcases hDB hz with hB | hQ
      · exact Or.inl hB
      · obtain ⟨x,hx⟩ := mem_iUnion.mp hQ
        exact Or.inr (mem_iUnion.mpr ⟨x,subset_closure hx⟩)
    · exact hBc.isClosed.union (isClosed_iUnion_of_finite (fun _ => isClosed_closure))
  have hQfin :
      (⋃ x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius,
        {S : Set P.domain.carrier | _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianPolygonSide P
          (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w) S ∧
          (S ∩ closure (d.radialEnd hw x)).Nonempty}).Finite :=
    Set.finite_iUnion (fun x => d.radial_end_sides_finite hNE hw x)
  have hBfin := (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain_locallyFinite P w
    hw).compact_sides_finite B hBc
  apply (hBfin.union hQfin).subset
  intro S hS
  obtain ⟨z,hzS⟩ := hS.2.2.nonempty
  have hzcl : z ∈ closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P
    w) := frontier_subset_closure
    (hS.subset_frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain_fundamental P w hw) hzS)
  rcases hclDB hzcl with hzB | hzQ
  · exact Or.inl ⟨hS,z,hzS,hzB⟩
  · obtain ⟨x,hzx⟩ := mem_iUnion.mp hzQ
    exact Or.inr (mem_iUnion.mpr ⟨x,hS,z,hzS,hzx⟩)

end RegularDirichletCircleData

/-- Finite generation of the original non-elementary disc group makes every
genuine Dirichlet polygon finite-sided, without assuming a finite core, finitely
many ends, or a finite polygon model. -/
theorem finitelyGenerated_dirichlet_sides_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    {S : Set P.domain.carrier | IsFuchsianPolygonSide P (dirichletDomain P w) S}.Finite := by
  let : Infinite H := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.nonElementary_infinite H hNE
  obtain ⟨g,hg⟩ := exists_ne (1:H)
  obtain ⟨d,_hd⟩ := finitelyGenerated_regular_dirichlet_circle_data P hFG w hw g hg 0
  exact d.sides_finite hNE hw

end LowDimensionalTopology.Geometry.Fuchsian
