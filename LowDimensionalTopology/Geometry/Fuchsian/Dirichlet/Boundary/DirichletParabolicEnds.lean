module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.EquivariantPath
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.ConvexRadial
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletRadialRegions
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Topology
open scoped Pointwise

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The genuine finite chart pulls the one-end sphere compactification back to
exactly the original actual real curve. -/
theorem unitDisc_one_endpoint_circle_preimage
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {F : ℝ → P.domain.carrier} {a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (ha : a ∈ frontier P.domain.carrier) {J : Circle → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (hRange : range J = insert a (range (fun t => (F t).val))) :
    (fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) ⁻¹'
      range (fun u => _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u)) = range F := by
  ext x
  constructor
  · rintro ⟨u,hu⟩
    have hJuRange : J u ∈ insert a (range (fun t => (F t).val)) := hRange ▸ mem_range_self u
    have hcl : J u ∈ closure _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
      rcases mem_insert_iff.mp hJuRange with he | he
      · exact he ▸ frontier_subset_closure ha
      · obtain ⟨t,ht⟩ := he
        exact ht ▸ subset_closure (F t).property
    have hJu : J u = x.val := by
      change _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u) = (P.finiteCoordinate x:ℂ) at hu
      rw [←sphereFiniteChart_coe_of_mem_unitDisc_closure hcl,hu]
      exact _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteChart_coe x
    have hxRange : x.val ∈ insert a (range (fun t => (F t).val)) := hJu ▸ hJuRange
    rcases mem_insert_iff.mp hxRange with he | he
    · have haD : a ∈ P.domain.carrier := he ▸ x.property
      exact False.elim (disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr P.domain.isOpen) ha haD)
    · obtain ⟨t,ht⟩ := he
      exact ⟨t,Subtype.ext ht⟩
  · rintro ⟨t,rfl⟩
    have hFt : (F t).val ∈ range J := hRange.symm ▸ mem_insert_of_mem a (mem_range_self t)
    obtain ⟨u,hu⟩ := hFt
    refine ⟨u,?_⟩
    change _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u) = (P.finiteCoordinate (F t):ℂ)
    rw [hu,sphereFiniteChart_unitDisc_coordinate P]

/-- Every true ambient ideal limit of a bounded Jordan side in the closed unit
disc comes from its actual closed-side contact with the unit circle. -/
theorem unitDisc_inside_ambient_closure_contact
    {C : Set ℂ} (hC : C ⊆ Metric.closedBall (0:ℂ) 1) :
    closure ((fun z : ℂ => (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ''
      _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C) \
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ⊆
      (fun z : ℂ => (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ''
        (closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C) ∩ Metric.sphere (0:ℂ) 1) := by
  have hclsub : closure ((fun z : ℂ => (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ''
    _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C) ⊆
      (fun z : ℂ => (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) '' closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C) :=
    closure_minimal (image_mono subset_closure)
      (((complexJordanInside_closure_compact_of_subset_closedUnitBall hC).image
        OnePoint.continuous_coe).isClosed)
  rintro x ⟨hxcl,hxD⟩
  obtain ⟨z,hzcl,rfl⟩ := hclsub hxcl
  have hznorm : ‖z‖ ≤ 1 := by
    have hzB : z ∈ Metric.closedBall (0:ℂ) 1 :=
      closure_minimal ((complexJordanInside_subset_ball_of_subset_closedBall zero_lt_one hC).trans
        Metric.ball_subset_closedBall) Metric.isClosed_closedBall hzcl
    simpa only [Metric.mem_closedBall,dist_zero_right] using hzB
  have hzge : 1 ≤ ‖z‖ := by
    by_contra he
    exact hxD ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc z).mpr (lt_of_not_ge he))
  refine ⟨z,⟨hzcl,?_⟩,rfl⟩
  simpa only [Metric.mem_sphere,dist_zero_right] using le_antisymm hznorm hzge

/-- The genuine original one-end Jordan region is open, has exactly the actual
original real curve as its relative frontier, and has no other true ambient
ideal limit than the named original endpoint. -/
theorem unitDisc_one_endpoint_inside_preimage_properties
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {F : ℝ → P.domain.carrier} {a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (ha : a ∈ frontier P.domain.carrier)
    {J : Circle → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hJ : Continuous J) (hJi :
      Function.Injective J)
    (hRange : range J = insert a (range (fun t => (F t).val))) :
    let C := range (fun u => _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u))
    let I := (fun z : P.domain.carrier => (P.finiteCoordinate
      z:ℂ)) ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C
    IsOpen I ∧ frontier I = range F ∧
      closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' I) \
        P.domain.carrier ⊆ {a} := by
  let f := fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)
  let C := range (fun u => _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u))
  let I := f ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C
  obtain ⟨hCJ,hCB,hContact⟩ := unitDisc_one_endpoint_Jordan_finite_data P ha hJ hJi hRange
  have hIo : IsOpen I := (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions hCJ).1.preimage
    (unitDisc_finite_plane_isOpenEmbedding P).continuous
  have hIfr : frontier I = range F := by
    rw [unitDisc_inside_preimage_frontier_eq P hCJ,
      unitDisc_one_endpoint_circle_preimage P ha hRange]
  refine ⟨hIo,hIfr,?_⟩
  have himage : (Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' I ⊆
      (fun z : ℂ => (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) '' _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C := by
    rintro z ⟨x,hx,rfl⟩
    exact ⟨f x,hx,_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteChart_coe x⟩
  rintro z ⟨hzcl,hzD⟩
  obtain ⟨v,hv,hvz⟩ := unitDisc_inside_ambient_closure_contact hCB ⟨closure_mono himage hzcl,hzD⟩
  rw [complexJordanInside_closure_sphere_eq hCJ hCB] at hv
  have hva : v = _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart a := mem_singleton_iff.mp (hContact
    hv)
  apply mem_singleton_iff.mpr
  calc z = (v:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := hvz.symm
       _ = ((_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart
         a:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := congrArg (fun w : ℂ =>
         (w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) hva
       _ = a := sphereFiniteChart_coe_of_mem_unitDisc_closure (frontier_subset_closure ha)


namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

/-- The actual aperiodic compactified frontier curve contains its whole original
base arc, not just its chosen original cut endpoint. -/
theorem aperiodic_compactification_contains_originalArc
    (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius)
    (hzero : d.endpointPeriod hw x = 0) :
    ∃ k : H, ∃ F : ℝ → P.domain.carrier,
      Function.Injective (fun n : ℤ => k^n) ∧ IsProperMap F ∧ IsClosedEmbedding F ∧
      d.originalArc hw x ⊆ range F ∧
      range F ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) ∧
      _root_.LowDimensionalTopology.Geometry.Fuchsian.DiscFrontierCurveCompactification P k F := by
  obtain ⟨L,hL,k,γ,hk,_hγ,hγrange,hproper,hembed,_hFfull,hfront⟩ :=
    d.aperiodic_exists_proper_embedded_frontier_curve hw x hzero
  refine ⟨k,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k
    γ,hk,hproper,hembed,?_,hfront,
    _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_equivariantPathExtension_compactified_dichotomy P k hk γ hembed.injective⟩
  intro z hz
  have hzγ : z ∈ range γ := by
    rw [hγrange]
    apply mem_iUnion₂.mpr
    refine ⟨0,hL,?_⟩
    have hC0 : d.developedClosedArc hw x 0 = closure (d.originalArc hw x) := by
      simp only [developedClosedArc,state,pow_zero,Equiv.Perm.one_apply,one_smul]
    rw [hC0]
    exact subset_closure hz
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_range]
  apply mem_iUnion.mpr
  refine ⟨0,?_⟩
  simpa only [zpow_zero,one_smul] using hzγ

/-- In the actual parabolic branch, the entire original strict radial end lies
in a genuine open region whose only possible ambient ideal limit is the unique
actual parabolic fixed point. No original end assignment or ideal-limit
conclusion is assumed. -/
theorem compactification_parabolic_radial_end_region
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hw :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius)
    {k : H} {F : ℝ → P.domain.carrier}
    (hArc : d.originalArc hw x ⊆ range F)
    (hF : range F ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius))
    (hShape : _root_.LowDimensionalTopology.Geometry.Fuchsian.DiscFrontierCurveCompactification P k F) (hpar :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic k.val) :
    ∃ a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, (k.val : Equiv.Perm
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) a = a ∧
      a ∈ frontier P.domain.carrier ∧
      ∃ I : Set P.domain.carrier, IsOpen I ∧ frontier I = range F ∧
        {z | z ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w ∧ d.radius < P.hyperbolicDist w z ∧
          _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection (Real.tanh
            d.radius) (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w z) ∈
            _root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x} ⊆ I ∧
        closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
          I) \
          P.domain.carrier ⊆ {a} := by
  obtain ⟨a,hfix,ha,J,hJ,hJi,_hJcl,hJrange,hCJ,hOutside,_hInside,_hContact⟩ :=
    d.parabolic_compactification_neighborhood_outside hNE hF hShape hpar
  let f := fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)
  let C := range (fun u => _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (J u))
  let I := f ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C
  obtain ⟨hIo,hIfr,hIideal⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_one_endpoint_inside_preimage_properties P ha hJ hJi hJrange
  have hIN : Disjoint I (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_inside_preimage_disjoint_of_outside P hCJ hOutside
  have hIfront : frontier I ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) := by
    rw [hIfr]
    exact hF
  have hcontact :
      ((_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x) ∩
        closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' I)).Nonempty := by
    obtain ⟨z,hz⟩ := d.originalArc_nonempty hw x
    refine ⟨_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w z,⟨z,hz,rfl⟩,?_⟩
    have hzI : z ∈ closure I := frontier_subset_closure (hIfr.symm ▸ hArc hz)
    exact mem_closure_image (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate_isOpenEmbedding P w).continuous.continuousAt hzI
  refine ⟨a,hfix,ha,I,hIo,hIfr,?_,hIideal⟩
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichlet_Klein_strict_end_subset_region P w hw d.radius d.radius_pos
    (d.klein_originalArc_isPreconnected hw x) (d.klein_originalArc_subset_spherical_slice hw x)
    (d.klein_originalArc_isOpen_sphere hw x) hIo hIN hIfront hcontact

end RegularDirichletCircleData
end LowDimensionalTopology.Geometry.Fuchsian
