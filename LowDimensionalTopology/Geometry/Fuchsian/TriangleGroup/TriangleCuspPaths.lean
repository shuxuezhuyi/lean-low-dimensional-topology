module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleCuspRays
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleCuspClassGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleMobiusQuotients
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.HalfPlaneCuspNormalization
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.SaccheriQuadrilaterals
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
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set
  Filter
  Topology
open scoped UpperHalfPlane Complex.UnitDisc OnePoint

/-- An unchanged physical point uses the genuine identity sheet of the literal old double. -/
theorem closedTriangleConformalOrbitCompactInclusion_project
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (p:(closedTrianglePoincarePolygon T).Point) :
    closedTriangleConformalOrbitCompactInclusion T ha hb hc
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (triangleConformalGroup T) ℍ p.val)=
      Quotient.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleSetoid _ _)
        (true,⟨closedTrianglePhysicalCayley p.val,
          (congrArg (fun A:Set ℍ=>p.val∈A) (closedTrianglePhysicalCayley_preimage T)).mpr p.property⟩) := by
  let S:=closedTrianglePoincarePairing T
  have he:closedTriangleConformalOrbitDoubleHomeomorph T ha hb hc
      (S.chamberDoublePoint (true,p))=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (triangleConformalGroup T) ℍ p.val:=by
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (triangleConformalGroup T) ℍ ((1:S.Generated)•p.val)=_
    rw [one_smul]
  change closedTrianglePhysicalDoubleInclusion T
    ((closedTriangleConformalOrbitDoubleHomeomorph T ha hb hc).symm _) = _
  rw [←he,(closedTriangleConformalOrbitDoubleHomeomorph T ha hb hc).symm_apply_apply]
  rfl

/-- A native cusp chart gives an actual interior sequence approaching the original ideal vertex. -/
theorem closedTriangle_native_cusp_sequence
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hα:T.alpha=0)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val T.a.val=∞)
    (M:ℝ) :
    ∃q:ℕ→ℍ,(∀n,q n∈T.interior) ∧
      (∀n,M<(A•q n:ℍ).im) ∧
      Tendsto (fun n=>_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (q n)) atTop (𝓝 T.a.val) ∧
      Tendsto (fun n=>(A•q n:ℍ).im) atTop atTop := by
  obtain ⟨p,hp⟩:=T.interior_nonempty
  let h:ℝ:=max (A•p:ℍ).im (max M 0)+1
  have hh:0<h:=by dsimp [h];linarith [le_max_right (A•p:ℍ).im (max M 0),le_max_right M (0:ℝ)]
  let z:ℕ→ℍ:=fun n=>⟨⟨(A•p:ℍ).re,h+(n:ℝ)⟩,by dsimp;positivity⟩
  let q:ℕ→ℍ:=fun n=>A⁻¹•z n
  have hz:∀n,(A•q n:ℍ)=z n:=fun n=>smul_inv_smul A (z n)
  have hi:∀n,q n∈T.interior:=by
    intro n
    apply closedTriangle_native_cusp_ray_inside T hα A hA p (q n) hp
    · rw [hz]
      rfl
    · rw [hz]
      change (A•p:ℍ).im≤h+(n:ℝ)
      dsimp [h]
      have hn:0≤(n:ℝ):=Nat.cast_nonneg n
      linarith [le_max_left (A•p:ℍ).im (max M 0)]
  have hgt:∀n,M<(A•q n:ℍ).im:=by
    intro n
    rw [hz]
    change M<h+(n:ℝ)
    have hn:0≤(n:ℝ):=Nat.cast_nonneg n
    dsimp [h]
    linarith [le_max_right (A•p:ℍ).im (max M 0),le_max_left M (0:ℝ)]
  have ht:Tendsto (fun n=>(A•q n:ℍ).im) atTop atTop:=by
    simp_rw [hz]
    change Tendsto (fun n:ℕ=>h+(n:ℝ)) atTop atTop
    exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hInf:=halfPlane_height_tendsto_infty (fun n=>A•q n) ht
  have hinv:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹).val ∞=T.a.val:=by
    rw [map_inv,←hA]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val.symm_apply_apply T.a.val
  have hlim:=((_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹)).tendsto ∞).comp hInf
  rw [hinv] at hlim
  have hq:Tendsto (fun n=>_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (q n)) atTop (𝓝 T.a.val):=by
    apply hlim.congr'
    filter_upwards [] with n
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A⁻¹ (A•q n)).trans
      (congrArg _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (inv_smul_smul A (q n)))
  exact ⟨q,hi,hgt,hq,ht⟩


/-- The unchanged original orbit of an interior cusp path has its genuine physical ideal-vertex limit. -/
theorem closedTriangle_native_path_physical_limit (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (i:Fin 3) (hi:closedTriangleCornerAngle T i=0)
    (q:ℕ→ℍ) (hq:∀n,q n∈T.interior)
    (ht:Tendsto (fun n=>_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (q n)) atTop (𝓝 (closedTriangleVertex T i).val)) :
    Tendsto (fun n=>closedTriangleConformalOrbitCompactInclusion T ha hb hc
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (triangleConformalGroup T) ℍ (q n))) atTop
      (𝓝 (closedTrianglePhysicalIdealPoint T
        ⟨closedTrianglePhysicalVertex T i,(closedTrianglePhysicalVertex_ideal_iff T i).mpr hi⟩)) := by
  let p:ℕ→(closedTrianglePoincarePolygon T).Point:=fun n=>⟨q n,by
    rw [closedTrianglePoincarePolygon_carrier]
    exact subset_closure (hq n)⟩
  let v:=closedTrianglePhysicalVertex T i
  let w:ℕ→closedTrianglePhysicalCompactRegion T:=fun n=>
    ⟨closedTrianglePhysicalCayley (q n),
      (congrArg (fun A:Set ℍ=>q n∈A) (closedTrianglePhysicalCayley_preimage T)).mpr (p n).property⟩
  have hh:Tendsto (fun n=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (q n)) atTop (𝓝 (closedTriangleVertex T i)):=
    tendsto_subtype_rng.mpr ht
  have hd:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.continuous.tendsto (closedTriangleVertex T i) |>.comp hh
  have hw:Tendsto w atTop (𝓝 v):=by
    apply tendsto_subtype_rng.mpr
    have hval:=((show Continuous (fun z:𝕔𝔻=>(z:ℂ)) from continuous_subtype_val).tendsto _).comp hd
    change Tendsto (fun n=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (q n)):ℂ)) atTop
      (𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph (closedTriangleVertex T i):ℂ)) at hval
    change Tendsto (fun n=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (q n):ℂ)) atTop (𝓝 v.val)
    have hv:v.val=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph (closedTriangleVertex T i):ℂ):=by
      fin_cases i <;> rfl
    rw [hv]
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel, Complex.UnitClosedDisc.coe_mk] using hval
  have hcmap:Continuous (fun z:closedTrianglePhysicalCompactRegion T=>
      (Quotient.mk _ (true,z):closedTrianglePhysicalCompactDouble T)):=
    continuous_quotient_mk'.comp (continuous_const.prodMk continuous_id)
  have hDouble:=(hcmap.tendsto v).comp hw
  have hvertex:Quotient.mk (_root_.LowDimensionalTopology.Geometry.Surfaces.boundaryDoubleSetoid _ _) (true,v)=
      closedTrianglePhysicalIdealPoint T
        ⟨closedTrianglePhysicalVertex T i,(closedTrianglePhysicalVertex_ideal_iff T i).mpr hi⟩:=by
    apply Quotient.sound
    exact ⟨rfl,Or.inr (closedTrianglePhysical_ideal_frontier T v
      ((closedTrianglePhysicalVertex_ideal_iff T i).mpr hi))⟩
  rw [hvertex] at hDouble
  apply hDouble.congr'
  filter_upwards [] with n
  exact (closedTriangleConformalOrbitCompactInclusion_project T ha hb hc (p n)).symm


/-- Every original zero-angle vertex is an actual parabolic fixed point of the whole original group. -/
theorem closedTriangle_ideal_vertex_is_cusp_at (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i:Fin 3) (hi:closedTriangleCornerAngle T i=0)
    (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    (closedTriangleVertex T i).val∈fuchsianCyclicFixedPoints P.asFuchsianDisc .parabolic := by
  let U:=closedTriangleCornerCycle T i
  have hu:U.alpha=0:=(closedTriangleCornerCycle_angle T i).trans hi
  obtain ⟨hpar,hfix⟩:=closedTriangle_ideal_vertex_parabolic U hu
  have hG:triangleConformalGroup U=triangleConformalGroup T:=by
    fin_cases i
    · rfl
    · exact triangleConformalGroup_cycle T
    · exact (triangleConformalGroup_cycle T.cycle).trans (triangleConformalGroup_cycle T)
  refine ⟨?_,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL U.sideLineC U.sideLineB),?_,hpar,?_⟩
  · intro h;cases h
  · apply _root_.LowDimensionalTopology.Geometry.Fuchsian.nativeConformalSubgroupMobiusGroup_matrix_mem
    rw [←hG,←reflectionProductSL_native,triangleConformalGroup_eq_pairProductGroup]
    exact trianglePairProductGroup_pair_mem U _ _
      (by simp [triangleReflectionSides]) (by simp [triangleReflectionSides])
  · simpa only [U,closedTriangleCornerCycle_vertex] using hfix

/-- The genuine ray construction works at every original zero-angle corner, without excluding other ideal vertices. -/
theorem closedTriangle_native_cusp_sequence_at (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i:Fin 3) (hi:closedTriangleCornerAngle T i=0)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (closedTriangleVertex T i).val=∞) (M:ℝ) :
    ∃q:ℕ→ℍ,(∀n,q n∈T.interior) ∧
      (∀n,M<(A•q n:ℍ).im) ∧
      Tendsto (fun n=>_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (q n)) atTop (𝓝 (closedTriangleVertex T i).val) ∧
      Tendsto (fun n=>(A•q n:ℍ).im) atTop atTop := by
  let U:=closedTriangleCornerCycle T i
  have hu:U.alpha=0:=(closedTriangleCornerCycle_angle T i).trans hi
  have hA':(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val U.a.val=∞:=by
    simpa only [U,closedTriangleCornerCycle_vertex] using hA
  obtain ⟨q,hq,hM,hlim,ht⟩:=closedTriangle_native_cusp_sequence U hu A hA' M
  refine ⟨q,?_,hM,?_,ht⟩
  · intro n
    simpa only [U,closedTriangleCornerCycle_interior] using hq n
  · simpa only [U,closedTriangleCornerCycle_vertex] using hlim

/-- One actual interior sequence reaches the specified physical ideal endpoint and its actual full-group cusp in the unique completion. -/
theorem closedTriangle_ideal_vertex_two_limits (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma)
    (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (i:Fin 3) (hi:closedTriangleCornerAngle T i=0) :
    ∃c:FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic,∃q:ℕ→ℍ,
      (∀n,q n∈T.interior) ∧
      Tendsto (fun n=>closedTriangleConformalOrbitCompactInclusion T ha hb hc
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (triangleConformalGroup T) ℍ (q n))) atTop
        (𝓝 (closedTrianglePhysicalIdealPoint T
          ⟨closedTrianglePhysicalVertex T i,(closedTrianglePhysicalVertex_ideal_iff T i).mpr hi⟩)) ∧
      Tendsto (fun n=>fuchsianCuspCompletionOld P.asFuchsianDisc
        (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection P.asFuchsianDisc.domain (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneOpenModelHomeomorph (q n)))) atTop
        (𝓝 (fuchsianCuspCompletionPoint P.asFuchsianDisc c)) := by
  obtain ⟨c,g,hg⟩:=fuchsianParabolicPointRepresentative_orbit_cover P.asFuchsianDisc
    ⟨(closedTriangleVertex T i).val,closedTriangle_ideal_vertex_is_cusp_at T i hi P⟩
  let C:=fuchsianCuspChartNormalization P.asFuchsianDisc c
  obtain ⟨d,A,hA,hfix⟩:=halfPlane_translated_cusp_native P C g
  have hAv:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (closedTriangleVertex T i).val=∞:=hg ▸ hfix
  obtain ⟨q,hq,hM,hlim,ht⟩:=closedTriangle_native_cusp_sequence_at T i hi A hAv (C.height-d)
  exact ⟨c,q,hq,closedTriangle_native_path_physical_limit T ha hb hc i hi q hq hlim,
    halfPlane_cusp_native_path_tendsto P c g d A hA q hM ht⟩

end LowDimensionalTopology.Geometry.Fuchsian
