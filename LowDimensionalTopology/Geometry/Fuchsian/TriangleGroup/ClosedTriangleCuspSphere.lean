module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleCuspPaths
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.NativeFiniteQuotientArea
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.MatchedPuncturePaths
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set
  Filter
  Topology
open scoped UpperHalfPlane OnePoint Complex.UnitDisc

/-- The unchanged actual native orbit, followed by the original full Mobius quotient and its unique all-cusp completion. -/
def closedTriangleCompletionOldMap (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (triangleConformalGroup T) ℍ→FuchsianCuspCompletion P.asFuchsianDisc :=
  fuchsianCuspCompletionOld P.asFuchsianDisc ∘ closedTriangleMobiusOrbitHomeomorph T P

theorem closedTriangleCompletionOldMap_isOpenEmbedding
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    Topology.IsOpenEmbedding (closedTriangleCompletionOldMap T P) :=
  (fuchsianCuspCompletionOld_isOpenEmbedding P.asFuchsianDisc).comp
    (closedTriangleMobiusOrbitHomeomorph T P).isOpenEmbedding

theorem closedTriangleCompletionOldMap_range (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    range (closedTriangleCompletionOldMap T P)=range (fuchsianCuspCompletionOld P.asFuchsianDisc) := by
  ext y
  constructor
  · rintro ⟨o,rfl⟩
    exact mem_range_self _
  · rintro ⟨o,rfl⟩
    exact ⟨(closedTriangleMobiusOrbitHomeomorph T P).symm o,
      congrArg (fuchsianCuspCompletionOld P.asFuchsianDisc)
        ((closedTriangleMobiusOrbitHomeomorph T P).apply_symm_apply o)⟩

theorem closedTriangleCompletionOldMap_complement_finite
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    (range (closedTriangleCompletionOldMap T P))ᶜ.Finite := by
  let :Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic):=
    closedTriangle_cyclic_classes_finite T ha hb hc P .parabolic
  rw [closedTriangleCompletionOldMap_range]
  apply (finite_range (fuchsianCuspCompletionPoint P.asFuchsianDisc)).subset
  intro y hy
  obtain h|⟨c,hc⟩:=fuchsianCuspCompletion_old_or_cusp P.asFuchsianDisc y
  · exact (hy h).elim
  · exact ⟨c,hc.symm⟩

/-- The actual physical double and the unique whole-group cusp completion are homeomorphic, with every old orbit fixed through its genuine original maps. -/
theorem closedTriangle_compactDouble_completion_homeomorph_exists
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    ∃E:closedTrianglePhysicalCompactDouble T≃ₜFuchsianCuspCompletion P.asFuchsianDisc,
      ∀o,E (closedTriangleConformalOrbitCompactInclusion T ha hb hc o)=closedTriangleCompletionOldMap T P o := by
  let sphereE:OnePoint ℂ≃ₜMetric.sphere (0:EuclideanSpace ℝ (Fin 3)) 1:=
    onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])
  let E0:=sphereE.trans (closedTrianglePhysicalCompactDoubleSphereHomeomorph T).symm
  let :CompactSpace (closedTrianglePhysicalCompactDouble T):=E0.compactSpace
  let :T2Space (closedTrianglePhysicalCompactDouble T):=E0.symm.isEmbedding.t2Space
  let :Nonempty (closedTrianglePhysicalCompactDouble T):=⟨E0 ∞⟩
  let :=_root_.LowDimensionalTopology.Geometry.Surfaces.sphereRiemannAtlas.toChartedSpace
  let :ChartedSpace ℂ (closedTrianglePhysicalCompactDouble T):=E0.chartedSpace
  let :T2Space (FuchsianCuspCompletion P.asFuchsianDisc):=fuchsianCuspCompletion_t2Space _
  let :ChartedSpace ℂ (FuchsianCuspCompletion P.asFuchsianDisc):=
    (fuchsianCuspCompletionRiemannSurface P.asFuchsianDisc).toRiemannAtlas.toChartedSpace
  apply _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.homeomorph_of_matching_puncture_paths
    (closedTriangleConformalOrbitCompactInclusion T ha hb hc) (closedTriangleCompletionOldMap T P)
    (closedTriangleConformalOrbitCompactInclusion_isOpenEmbedding T ha hb hc)
    (closedTriangleCompletionOldMap_isOpenEmbedding T P)
    (closedTriangleConformalOrbitCompactInclusion_complement_finite T ha hb hc)
    (closedTriangleCompletionOldMap_complement_finite T ha hb hc P)
  intro a haOld
  have hp:a∈range (closedTrianglePhysicalIdealPoint T):=by
    rw [←closedTriangleConformalOrbitCompactInclusion_complement T ha hb hc]
    exact haOld
  obtain ⟨p,rfl⟩:=hp
  obtain ⟨i,hi⟩:=(closedTrianglePhysicalIdealLabelEquiv T).surjective p
  obtain ⟨c,q,hq,hphys,hcusp⟩:=closedTriangle_ideal_vertex_two_limits T ha hb hc P i.val i.property
  refine ⟨fuchsianCuspCompletionPoint P.asFuchsianDisc c,?_,
    fun n=>_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (triangleConformalGroup T) ℍ (q n),?_,?_⟩
  · rw [closedTriangleCompletionOldMap_range]
    exact fuchsianCuspCompletionPoint_not_mem_old P.asFuchsianDisc c
  · rw [←hi]
    exact hphys
  · exact hcusp

/-- The true completed original triangle quotient has genus zero. -/
theorem closedTriangle_cusp_completion_genus_zero (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (FuchsianCuspCompletion P.asFuchsianDisc) 0 := by
  obtain ⟨E,_hE⟩:=closedTriangle_compactDouble_completion_homeomorph_exists T ha hb hc P
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.hasTopologicalGenus_zero_iff.mpr
    ⟨E.symm.trans (closedTrianglePhysicalCompactDoubleSphereHomeomorph T)⟩


/-- The genuine physical-to-completed homeomorphism, chosen only after its actual extension has been proved. -/
def closedTriangleCuspCompletionHomeomorph (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    closedTrianglePhysicalCompactDouble T≃ₜFuchsianCuspCompletion P.asFuchsianDisc :=
  (closedTriangle_compactDouble_completion_homeomorph_exists T ha hb hc P).choose

theorem closedTriangleCuspCompletionHomeomorph_old (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (o:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient (triangleConformalGroup T) ℍ) :
    closedTriangleCuspCompletionHomeomorph T ha hb hc P
      (closedTriangleConformalOrbitCompactInclusion T ha hb hc o)=closedTriangleCompletionOldMap T P o :=
  (closedTriangle_compactDouble_completion_homeomorph_exists T ha hb hc P).choose_spec o

/-- The actual maximal parabolic class reached by an original zero-angle corner. -/
def closedTriangleIdealCuspClass (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (i:{i:Fin 3|closedTriangleCornerAngle T i=0}) :
    FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic :=
  (closedTriangle_ideal_vertex_two_limits T ha hb hc P i.val i.property).choose

/-- The proved global homeomorphism sends each original omitted endpoint to exactly its actual cusp class point. -/
theorem closedTriangleCuspCompletionHomeomorph_ideal
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (i:{i:Fin 3|closedTriangleCornerAngle T i=0}) :
    closedTriangleCuspCompletionHomeomorph T ha hb hc P
      (closedTrianglePhysicalIdealPoint T (closedTrianglePhysicalIdealLabelEquiv T i))=
        fuchsianCuspCompletionPoint P.asFuchsianDisc (closedTriangleIdealCuspClass T ha hb hc P i) := by
  obtain ⟨q,_hq,hphys,hcusp⟩:=
    (closedTriangle_ideal_vertex_two_limits T ha hb hc P i.val i.property).choose_spec
  let E:=closedTriangleCuspCompletionHomeomorph T ha hb hc P
  have ht:=(E.continuous.tendsto
    (closedTrianglePhysicalIdealPoint T (closedTrianglePhysicalIdealLabelEquiv T i))).comp hphys
  have ht':Tendsto (fun n=>E (closedTriangleConformalOrbitCompactInclusion T ha hb hc
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (triangleConformalGroup T) ℍ (q n)))) atTop
      (𝓝 (fuchsianCuspCompletionPoint P.asFuchsianDisc (closedTriangleIdealCuspClass T ha hb hc P i))):=by
    apply hcusp.congr'
    filter_upwards [] with n
    exact (closedTriangleCuspCompletionHomeomorph_old T ha hb hc P
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (triangleConformalGroup T) ℍ (q n))).symm
  let :T2Space (FuchsianCuspCompletion P.asFuchsianDisc):=fuchsianCuspCompletion_t2Space _
  exact tendsto_nhds_unique ht ht'

/-- Original zero-angle vertices classify all actual parabolic maximal cyclic conjugacy classes, without a supplied end bijection. -/
def closedTriangleIdealCuspClassEquiv (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    {i:Fin 3|closedTriangleCornerAngle T i=0}≃FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic :=
  Equiv.ofBijective (closedTriangleIdealCuspClass T ha hb hc P) ⟨by
    intro i j hij
    apply (closedTrianglePhysicalIdealLabelEquiv T).injective
    apply closedTrianglePhysicalIdealPoint_injective T
    apply (closedTriangleCuspCompletionHomeomorph T ha hb hc P).injective
    rw [closedTriangleCuspCompletionHomeomorph_ideal,closedTriangleCuspCompletionHomeomorph_ideal,hij],by
    intro c
    let E:=closedTriangleCuspCompletionHomeomorph T ha hb hc P
    let x:=E.symm (fuchsianCuspCompletionPoint P.asFuchsianDisc c)
    have hx:x∉range (closedTriangleConformalOrbitCompactInclusion T ha hb hc):=by
      rintro ⟨o,ho⟩
      apply fuchsianCuspCompletionPoint_not_mem_old P.asFuchsianDisc c
      refine ⟨closedTriangleMobiusOrbitHomeomorph T P o,?_⟩
      have hh:=congrArg E ho
      rw [closedTriangleCuspCompletionHomeomorph_old,E.apply_symm_apply] at hh
      exact hh
    have hxp:x∈range (closedTrianglePhysicalIdealPoint T):=by
      rw [←closedTriangleConformalOrbitCompactInclusion_complement T ha hb hc]
      exact hx
    obtain ⟨p,hp⟩:=hxp
    obtain ⟨i,hi⟩:=(closedTrianglePhysicalIdealLabelEquiv T).surjective p
    refine ⟨i,?_⟩
    apply fuchsianCuspCompletionPoint_injective P.asFuchsianDisc
    rw [←closedTriangleCuspCompletionHomeomorph_ideal,hi,hp]
    exact E.apply_symm_apply _⟩

theorem closedTriangle_actual_cusp_count (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic)=
      Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0} :=
  Nat.card_congr (closedTriangleIdealCuspClassEquiv T ha hb hc P).symm

end LowDimensionalTopology.Geometry.Fuchsian
