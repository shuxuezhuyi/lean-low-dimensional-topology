/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ArbitraryTriangleDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.NativeGeometricCovolume
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleSideStars
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.NativeDirichletMeasureDomains
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
open Set MeasureTheory Topology InnerProductGeometry
open scoped UpperHalfPlane OnePoint Pointwise ENNReal
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
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance triangleAreaSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance triangleAreaSphereBorel : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩

/-- Reflection across a true side changes the genuine hyperbolic distance
cosine by the product of its two signed normal coordinates. -/
theorem triangleArea_reflection_cosh (L:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (z w:ℍ) :
    Real.cosh (dist z (L.reflection w))-Real.cosh (dist z w)=
      2*L.normalTimeAt z*L.normalTimeAt w := by
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePoint_cosh_distance,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePoint_cosh_distance,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_reflection,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial_reflection,
    inner_add_right,inner_smul_right]
  unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalTimeAt
  rw [real_inner_comm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlanePointSpatial z) L.incenterNormal]
  ring

/-- Every genuine interior point has all three actual triangle coordinates positive. -/
theorem triangleArea_barycentric_pos
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    {w:ℍ}
    (hw:w∈T.interior)
    (i:Fin 3) :
    0<triangleBarycentric T w i := by
  have hh: T.coordinate w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.standardOpenTriangle:=T.coordinate_image_interior ▸ mem_image_of_mem T.coordinate hw
  change 0<(T.coordinate w).1 ∧0<(T.coordinate w).2 ∧(T.coordinate w).1+(T.coordinate w).2<1 at hh
  fin_cases i <;> simp only [triangleBarycentric,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,Fin.reduceFinMk] <;> linarith only [hh.1,hh.2.1,hh.2.2]

/-- The actual closed native Dirichlet region at any interior center lies
in the literal closure of the original finite triangle, without an
integral-angle assumption. -/
theorem triangleArea_closedDirichlet_subset
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    {w:ℍ}
    (hw:w∈T.interior) :
    nativeClosedDirichlet (triangleReflectionGroup T.toClosedHTriangle) w⊆closure T.interior := by
  intro z hz
  rw [←finiteTrianglePoincarePolygon_carrier]
  apply (triangleBarycentric_carrier T z).mpr
  intro i
  let L:=finiteTrianglePoincareLine T i
  have hg:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L∈triangleReflectionGroup T.toClosedHTriangle:=by
    rw [←finiteTrianglePoincarePairing_generated]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L∈Subgroup.closure (range (finiteTrianglePoincarePairing T).element)
    apply Subgroup.subset_closure
    rw [finiteTrianglePoincarePairing_range]
    exact mem_range_self i
  have hd:=hz ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L,hg⟩
  change dist z w≤dist z (L.reflection w) at hd
  have hc:Real.cosh (dist z w)≤Real.cosh (dist z (L.reflection w)):=Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg dist_nonneg] using hd)
  have hp:0≤L.normalTimeAt z*L.normalTimeAt w:=by
    have he:=triangleArea_reflection_cosh L z w
    linarith only [hc,he]
  let k:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine L.incenterNormal L.incenterOffset (triangleOppositeVertex T i)
  have hfactor:L.normalTimeAt w=(-k)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight w*triangleBarycentric T w i):=by
    rw [L.normalTimeAt_eq_affine,triangleSide_affine_factor T i w]
    ring
  have hwpos:0<_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight w*triangleBarycentric T w i:=
    mul_pos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight_pos w) (triangleArea_barycentric_pos T hw i)
  have hp':0≤((-k)*L.normalTimeAt z)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinHeight w*triangleBarycentric T w i):=by
    rw [hfactor] at hp
    nlinarith only [hp]
  exact (triangleSide_signed_halfspace T i z).mp ((mul_nonneg_iff_of_pos_right hwpos).mp hp')

/-- The original even group has a genuine orbit cover by two literal
copies of the original compact triangle. -/
theorem triangleArea_two_copies_meet_orbits (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (hd:DiscreteTopology (triangleConformalGroup T.toClosedHTriangle)) :
    ∀x:ℍ,∃g:triangleConformalGroup T.toClosedHTriangle,
      g • x∈closure T.interior∪
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.toClosedHTriangle.sideLineA) '' closure T.interior := by
  let U:=T.toClosedHTriangle
  let : DiscreteTopology (triangleReflectionGroup U):=(triangle_discrete_full_iff_conformal U).mpr hd
  have hDis:=triangleReflectionGroup_discontinuous U
  obtain ⟨w,hw⟩:=T.interior_nonempty
  let R:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry U.sideLineA
  have hRG:R∈triangleReflectionGroup U:=Subgroup.subset_closure
    ⟨U.sideLineA,by simp [triangleReflectionSides],rfl⟩
  have hRodd:(⟨R,hRG⟩:triangleReflectionGroup U)∉triangleConformalKernel U:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.halfPlaneLineReflectionIsometry_not_conformal U.sideLineA
  intro x
  obtain ⟨g,hg⟩:=nativeClosedDirichlet_meets_orbit (triangleReflectionGroup U) hDis w x
  have hp:g.val x∈closure T.interior:=triangleArea_closedDirichlet_subset T hw hg
  by_cases he:g.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup
  · exact ⟨⟨g.val,g.property,he⟩,Or.inl hp⟩
  · have hgodd:g∉triangleConformalKernel U:=he
    have hEven:(⟨R,hRG⟩:triangleReflectionGroup U)*g∈triangleConformalKernel U:=
      (Subgroup.mul_mem_iff_of_index_two (triangleConformalKernel_index_two U)).mpr
        (iff_of_false hRodd hgodd)
    refine ⟨⟨R*g.val,(triangleReflectionGroup U).mul_mem hRG g.property,hEven⟩,Or.inr ?_⟩
    exact ⟨g.val x,hp,rfl⟩

/-- A literal orbit-covering set has at least the genuine fundamental
measure. This application uses the physical hyperbolic measure. -/
theorem triangleArea_measure_domain_le_cover {G:Type*} [Group G] [MulAction G ℍ]
    [Countable G] [MeasurableConstSMul G ℍ] [SMulInvariantMeasure G ℍ volume]
    {S C:Set ℍ} (hS:MeasureTheory.IsFundamentalDomain G S volume)
    (hC:∀x:ℍ,∃g:G,g • x∈C) : volume S≤volume C := by
  have hcover:S⊆⋃g:G,g • C∩S:=by
    intro x hx
    obtain ⟨g,hg⟩:=hC x
    exact mem_iUnion.mpr ⟨g⁻¹,⟨⟨g • x,hg,by simp⟩,hx⟩⟩
  calc
    volume S≤volume (⋃g:G,g • C∩S):=measure_mono hcover
    _≤∑'g:G,volume (g • C∩S):=measure_iUnion_le _
    _=volume C:=(hS.measure_eq_tsum C).symm

/-- The three genuine supporting geodesics make the physical finite
triangle frontier hyperbolic-area null. -/
theorem triangleArea_frontier_null
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) : volume (frontier T.interior)=0 := by
  have hsub:frontier T.interior⊆T.sideLineA.carrier∪T.sideLineB.carrier∪T.sideLineC.carrier:=by
    rw [T.frontier_eq_sides]
    rintro z ((hz|hz)|hz)
    · exact Or.inl (Or.inl (finiteTrianglePoincareSide_subset_line T 0 hz))
    · exact Or.inl (Or.inr (finiteTrianglePoincareSide_subset_line T 1 hz))
    · exact Or.inr (finiteTrianglePoincareSide_subset_line T 2 hz)
  exact measure_mono_null hsub (measure_union_null
    (measure_union_null T.sideLineA.volume_zero T.sideLineB.volume_zero) T.sideLineC.volume_zero)

/-- A genuine fundamental region for the original even triangle group has
area at most twice the original triangle, whether or not that triangle
is a primitive reflection chamber. -/
theorem triangleArea_native_domain_upper (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (hd:DiscreteTopology (triangleConformalGroup T.toClosedHTriangle))
    {S:Set ℍ} (hS:MeasureTheory.IsFundamentalDomain (triangleConformalGroup T.toClosedHTriangle) S volume) :
    volume S≤2*volume T.interior := by
  let U:=T.toClosedHTriangle
  let : Countable (triangleReflectionGroup U):=triangleReflectionGroup_countable U
  let : Countable (triangleConformalGroup U):=Function.Injective.countable (f:=fun g:triangleConformalGroup U=>
    (⟨g.val,g.property.1⟩:triangleReflectionGroup U))
    (by intro a b h;exact Subtype.ext (congrArg (fun g:triangleReflectionGroup U=>g.val) h))
  let : ContinuousConstSMul (triangleConformalGroup U) ℍ:=⟨fun g=>g.val.continuous⟩
  let R:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry U.sideLineA
  have hb:=triangleArea_measure_domain_le_cover hS (triangleArea_two_copies_meet_orbits T hd)
  calc
    volume S≤volume (closure T.interior∪R '' closure T.interior):=hb
    _≤volume (closure T.interior)+volume (R '' closure T.interior):=measure_union_le _ _
    _=2*volume T.interior:=by
      rw [native_isometry_volume_image,measure_closure_of_null_frontier (triangleArea_frontier_null T)]
      exact (two_mul _).symm

/-- A genuine triangle group's original geometric fundamental domain has
hyperbolic area at least pi/21, derived from its actual whole-disc model. -/
theorem triangleArea_original_domain_lower {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (ht:IsMobiusTriangleGroup H)
    (F:Set (fuchsianGeometricDomain D).carrier)
    (hF:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D).carrier (geometricModelArea D) F) :
    Real.pi/21≤(geometricModelArea D F).toReal := by
  obtain ⟨U,ha,hb,hc,M,hG,hDisc⟩:=mobiusTriangleGroup_exists_whole_disc_triangle_model D ht
  have he:geometricModelArea D F=ENNReal.ofReal (closedTriangleSignatureData U ha hb hc).areaFormulaValue:=
    (closedTriangle_conjugate_signature_area D U ha hb hc M hG hDisc F hF).2
  have hpos:=closedTriangleSignatureData_deficit_pos U ha hb hc
  have hlo:=((closedTriangleSignatureData U ha hb hc).areaFormulaValue_sharp hpos).1
  rw [he,ENNReal.toReal_ofReal]
  · exact hlo
  · exact (div_pos Real.pi_pos (by norm_num : (0:ℝ)<21)).le.trans hlo

/-- Any discrete actual finite reflection triangle, with arbitrary original
angles, has physical hyperbolic area at least pi/42. -/
theorem finiteTriangle_discrete_area_lower_bound (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (hd:DiscreteTopology (triangleConformalGroup T.toClosedHTriangle)) :
    Real.pi/42≤(volume T.interior).toReal := by
  let U:=T.toClosedHTriangle
  let : DiscreteTopology (triangleConformalGroup U):=hd
  let P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup U):=
    nativeConformalSubgroup_halfPlaneData (triangleConformalGroup U) inf_le_right
  have ht:=discrete_arbitrary_triangle_isMobiusTriangleGroup U hd
  let Q:=geometricDiscData P.asFuchsianDisc
  obtain ⟨w,hw,_hgood⟩:=exists_actual_dirichlet_horocycle_good_center Q
  let D:=dirichletDomain Q w
  have hD:IsFuchsianFundamentalDomain Q D:=dirichletDomain_fundamental Q w hw
  let F:=geometricDiscHomeomorph P.asFuchsianDisc ⁻¹' D
  have hF:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (closedTriangleMobiusGroup U)
      (fuchsianGeometricDomain P.asFuchsianDisc).carrier (geometricModelArea P.asFuchsianDisc) F:=
    geometricModel_fundamentalDomain_of_disc P.asFuchsianDisc hD
  have hlo:=triangleArea_original_domain_lower P.asFuchsianDisc ht F hF
  let S:=halfPlaneGeometricChart P '' F
  let triangleAreaImageAction:=P.nativeAction
  have hSGeom:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (closedTriangleMobiusGroup U) ℍ volume S:=
    halfPlaneGeometricChart_fundamental_image P F hF
  have hSM:=native_geometric_fundamental_measureDomain P S hSGeom
  let E:=closedTriangleMobiusEquiv U
  have he (g:triangleConformalGroup U) (z:ℍ):E g • z=g • z:=by
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    rw [←P.nativeAction_boundary]
    exact closedTriangleMobiusEquiv_action U g z
  have hi (g:closedTriangleMobiusGroup U) (z:ℍ):E.symm g • z=g • z:=by
    have hh:=he (E.symm g) z
    rw [E.apply_symm_apply] at hh
    exact hh.symm
  have hS:=hSM.preimage_of_equiv (f:=id) (MeasurePreserving.id volume).quasiMeasurePreserving
    E.symm.bijective (by intro g z;exact hi g z)
  have hUpper:volume S≤2*volume T.interior:=triangleArea_native_domain_upper T hd
    (by simpa only [preimage_id] using hS)
  have heq:geometricModelArea P.asFuchsianDisc F=volume S:=
    halfPlaneGeometricChart_image_area P F hF.isOpen.measurableSet
  rw [heq] at hlo
  have hfinite:2*volume T.interior≠⊤:=by
    rw [T.area_eq_angle_defect]
    finiteness
  have hup:=ENNReal.toReal_mono hfinite hUpper
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofNat] at hup
  linarith only [hlo,hup]

/-- The source positive-angle formulation, allowing nonprimitive rational
angles without replacing the original triangle by its fundamental chamber. -/
theorem closedTriangle_discrete_positive_area_lower_bound
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:0<T.alpha) (hb:0<T.beta) (hc:0<T.gamma)
    (hd:DiscreteTopology (triangleConformalGroup T)) : Real.pi/42≤(volume T.interior).toReal := by
  obtain ⟨U,hU⟩:=positive_angle_closedTriangle_has_finite_model T ha hb hc
  have hh:=finiteTriangle_discrete_area_lower_bound U (hU.symm ▸hd)
  rwa [←U.interior_toClosedHTriangle,hU] at hh

/-- The genuine small-area obstruction in the source, with the literal
three positive original angles and no assumed reciprocal denominators. -/
theorem closedTriangle_small_positive_area_not_discrete
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:0<T.alpha) (hb:0<T.beta) (hc:0<T.gamma)
    (hsmall:Real.pi-(T.alpha+T.beta+T.gamma)<Real.pi/42) :
    ¬DiscreteTopology (triangleConformalGroup T) := by
  intro hd
  have hh:=closedTriangle_discrete_positive_area_lower_bound T ha hb hc hd
  rw [T.area_eq_angle_defect,ENNReal.toReal_ofReal] at hh
  · linarith only [hsmall,hh]
  · linarith only [T.angle_sum_lt_pi]

/-- The original full reflection group satisfies the same sharp necessary
area obstruction, through its actual finite-index conformal subgroup. -/
theorem closedTriangle_reflection_discrete_positive_area_lower_bound
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:0<T.alpha) (hb:0<T.beta) (hc:0<T.gamma)
    (hd:DiscreteTopology (triangleReflectionGroup T)) : Real.pi/42≤(volume T.interior).toReal :=
  closedTriangle_discrete_positive_area_lower_bound T ha hb hc
    ((triangle_discrete_full_iff_conformal T).mp hd)

end LowDimensionalTopology.Geometry.Fuchsian
