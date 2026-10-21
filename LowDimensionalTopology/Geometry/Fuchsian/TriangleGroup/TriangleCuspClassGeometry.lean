module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleMobiusQuotients
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.HalfPlaneCuspNormalization
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.SaccheriQuadrilaterals
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set
  Filter
  Topology
open scoped UpperHalfPlane Complex.UnitDisc OnePoint

theorem reflectionProductSL_fixes_common_ideal (L M:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (p:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel)
    (hp:p.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary)
    (hL:p∈L.closedCarrier) (hM:p∈M.closedCarrier) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L M)).val p.val=p.val := by
  have hfix (N:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (hN:p∈N.closedCarrier) :
      (_root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom N.realReflection) p.val=p.val := by
    have he:=(N.idealEndpoint_iff_extendedCircle p.val hp).mp ((N.closedCarrier_mem_ideal_iff p hp).mp hN)
    rw [←N.realReflection_fixedPoints] at he
    exact he
  have he:=congrArg (fun g:_root_.LowDimensionalTopology.Geometry.Mobius.complexGeneralMobiusGroup=>g.val)
    (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension (reflectionProductSL_native L M))
  rw [map_mul,nativeHalfPlaneExtension_hSL] at he
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L)).val *
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry M)).val=_ at he
  rw [nativeHalfPlaneExtension_reflection,nativeHalfPlaneExtension_reflection] at he
  change (_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusToFull (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L M))).val p.val=p.val
  rw [←he]
  change (_root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom L.realReflection)
    ((_root_.LowDimensionalTopology.Geometry.Mobius.euclideanToComplexHom M.realReflection) p.val)=p.val
  rw [hfix M hM,hfix L hL]

theorem closedTriangle_ideal_vertex_parabolic
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hα:T.alpha=0) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineC T.sideLineB)) ∧
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineC T.sideLineB)).val T.a.val=T.a.val := by
  have hi:T.a.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary:=by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff T.a).mp
    exact T.toDiscTriangle.alpha_eq_zero_iff_ideal.mp hα
  have hC:T.a∈T.sideLineC.closedCarrier:=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.a).mp T.toDiscTriangle.a_mem_sideLineC
  have hB:T.a∈T.sideLineB.closedCarrier:=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.a).mp T.toDiscTriangle.a_mem_sideLineB
  exact ⟨reflectionProductSL_common_ideal_parabolic _ _ (triangle_sideLineCB_distinct T) T.a hi hC hB,
    reflectionProductSL_fixes_common_ideal _ _ T.a hi hC hB⟩

theorem closedTriangle_ideal_vertex_is_cusp
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hα:T.alpha=0)
    (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    T.a.val∈fuchsianCyclicFixedPoints P.asFuchsianDisc .parabolic := by
  obtain ⟨hpar,hfix⟩:=closedTriangle_ideal_vertex_parabolic T hα
  refine ⟨?_,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineC T.sideLineB),?_,hpar,hfix⟩
  · intro h
    cases h
  · apply _root_.LowDimensionalTopology.Geometry.Fuchsian.nativeConformalSubgroupMobiusGroup_matrix_mem
    rw [←reflectionProductSL_native,triangleConformalGroup_eq_pairProductGroup]
    exact trianglePairProductGroup_pair_mem T _ _
      (by simp [triangleReflectionSides]) (by simp [triangleReflectionSides])

/-- An actual group translate of a chosen cusp chart is again an actual native real-SL chart at the translated ideal point. -/
theorem halfPlane_translated_cusp_native {H:Subgroup Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H)
    {S:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset P.asFuchsianDisc.domain}
    {w:Mobius.ExtendedComplex}
    (C:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S w)
    (g:H) :
    ∃d:ℝ,∃A:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ)*C.normalizer*g.val⁻¹ ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (g.val.val w)=∞ := by
  obtain ⟨d,A,hA,hfix⟩:=halfPlane_cusp_normalizer_native P C
  obtain ⟨B,hB⟩:=mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
  refine ⟨d,A*B⁻¹,?_,?_⟩
  · rw [map_mul,map_inv,hA,hB]
  · rw [map_mul,map_inv,hB]
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (g.val.val.symm (g.val.val w))=∞
    rw [Equiv.symm_apply_apply]
    exact hfix

/-- Infinite actual height in a standard cusp converges to its genuine added cusp point. -/
theorem stableCuspCompletion_height_tendsto {ι:Type*} {l:Filter ι} (h:ℝ)
    (z:ι→_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspHalfPlane h)
    (hz:Tendsto (fun i=>(z i).val.im) l atTop) :
    Tendsto (fun i=>_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspCompletionSome h (z i)) l (𝓝 (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspCompletionInfinity h)) := by
  rw [tendsto_def]
  intro U hU
  obtain ⟨t,_ht,htU⟩:=(_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspCompletion_mem_nhds_iff h U).mp hU
  filter_upwards [hz.eventually_gt_atTop t] with i hi
  exact htU ((_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspCompletionTail_some h t (z i)).mpr hi)


/-- The original translated cusp coordinate is the native coordinate plus its actual vertical origin. -/
theorem halfPlane_translated_cusp_coordinates
    {H:Subgroup Mobius.complexMobiusGroup}
    {D:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H}
    {S:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D}
    {w:Mobius.ExtendedComplex}
    (C:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S w) (g:H) (d:ℝ)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ)*C.normalizer*g.val⁻¹) (z:ℍ) :
    C.normalizer.val (g.val.val.symm (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z))=
      (((A•z:ℍ):ℂ)+⟨0,d⟩:ℂ) := by
  have he:_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (A•z)=
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ)).val
        (C.normalizer.val (g.val.val.symm (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z))):=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A z).symm.trans
      (congrArg (fun f:Mobius.complexMobiusGroup=>f.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)) hA)
  have he':=congrArg (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ)).val.symm he.symm
  rw [Equiv.symm_apply_apply] at he'
  have hInv:(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ))⁻¹=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,d⟩:ℂ):=by
    rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_neg]
    congr 1
    apply Complex.ext <;> simp
  change C.normalizer.val (g.val.val.symm (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z))=
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ))⁻¹).val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (A•z)) at he'
  rw [hInv] at he'
  exact he'.trans (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe _ ((A•z:ℍ):ℂ))

/-- The actual chosen completed chart followed by the original simultaneous orbit projection. -/
def fuchsianCuspCompletedChart
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (c:FuchsianCyclicConjugacyClasses D .parabolic) (g:H) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.StableCuspCompletion (fuchsianCuspChartNormalization D c).height→FuchsianCuspCompletion D :=
  fun p=>Quotient.mk _ (_root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspAugmentedPiece (fuchsianCuspChartNormalization D) c
    (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusCuspAugmentedCusp (fuchsianCuspChartNormalization D c) g p))

theorem fuchsianCuspCompletedChart_continuous
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (c:FuchsianCyclicConjugacyClasses D .parabolic) (g:H) :
    Continuous (fuchsianCuspCompletedChart D c g) :=
  continuous_quotient_mk'.comp ((_root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspAugmentedPiece_continuous _ c).comp
    (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusCuspAugmentedCusp_continuous _ g))

theorem fuchsianCuspCompletedChart_infty
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (c:FuchsianCyclicConjugacyClasses D .parabolic) (g:H) :
    fuchsianCuspCompletedChart D c g (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspCompletionInfinity _)=fuchsianCuspCompletionPoint D c := by
  apply Quotient.sound
  refine ⟨g,?_⟩
  apply Subtype.ext
  change g • ((1:H) • (fuchsianParabolicPointRepresentative D c).val)=
    g • (fuchsianParabolicPointRepresentative D c).val
  rw [one_smul]


/-- The finite part of the actual completed chart is the unchanged original orbit projection. -/
theorem fuchsianCuspCompletedChart_some
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (c:FuchsianCyclicConjugacyClasses D .parabolic) (g:H)
    (z:_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspHalfPlane (fuchsianCuspChartNormalization D c).height)
    (q:D.domain.carrier)
    (hq:(fuchsianCuspChartNormalization D c).normalizer.val (g.val.val.symm q.val)=
      (z.val:Mobius.ExtendedComplex)) :
    fuchsianCuspCompletedChart D c g (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspCompletionSome _ z)=
      fuchsianCuspCompletionOld D (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain q) := by
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  change g.val.val ((fuchsianCuspChartNormalization D c).normalizer.val.symm (z.val:Mobius.ExtendedComplex))=q.val
  rw [←hq,Equiv.symm_apply_apply,Equiv.apply_symm_apply]

/-- A real-height divergent native path converges to the actual chosen full-group cusp class. -/
theorem halfPlane_cusp_native_path_tendsto {H:Subgroup Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H)
    (c:FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) (g:H)
    (d:ℝ) (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ)*
      (fuchsianCuspChartNormalization P.asFuchsianDisc c).normalizer*g.val⁻¹)
    (q:ℕ→ℍ)
    (hq:∀n,(fuchsianCuspChartNormalization P.asFuchsianDisc c).height-d<(A•q n:ℍ).im)
    (ht:Tendsto (fun n=>(A•q n:ℍ).im) atTop atTop) :
    Tendsto (fun n=>fuchsianCuspCompletionOld P.asFuchsianDisc
      (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection P.asFuchsianDisc.domain (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneOpenModelHomeomorph (q n)))) atTop
      (𝓝 (fuchsianCuspCompletionPoint P.asFuchsianDisc c)) := by
  let C:=fuchsianCuspChartNormalization P.asFuchsianDisc c
  let z:ℕ→_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspHalfPlane C.height:=fun n=>⟨((A•q n:ℍ):ℂ)+⟨0,d⟩,by
    change C.height<(A•q n:ℍ).im+d
    have hn:=hq n
    change C.height-d<(A•q n:ℍ).im at hn
    linarith⟩
  have hz:Tendsto (fun n=>(z n).val.im) atTop atTop:=by
    change Tendsto (fun n=>(A•q n:ℍ).im+d) atTop atTop
    exact tendsto_atTop_add_const_right _ _ ht
  have hh:=(fuchsianCuspCompletedChart_continuous P.asFuchsianDisc c g).tendsto
    (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspCompletionInfinity C.height)
  have hlim:=hh.comp (stableCuspCompletion_height_tendsto C.height z hz)
  rw [fuchsianCuspCompletedChart_infty] at hlim
  apply hlim.congr'
  filter_upwards [] with n
  exact fuchsianCuspCompletedChart_some P.asFuchsianDisc c g (z n)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneOpenModelHomeomorph (q n)) (halfPlane_translated_cusp_coordinates C g d A hA (q n))

end LowDimensionalTopology.Geometry.Fuchsian
