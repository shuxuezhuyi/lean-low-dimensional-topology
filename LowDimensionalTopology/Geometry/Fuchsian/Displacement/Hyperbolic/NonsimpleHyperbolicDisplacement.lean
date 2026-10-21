/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.WeakDisplacementGap
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Hyperbolic.HyperbolicDisplacementProducts
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine discrete partner moving a genuine hyperbolic axis generates a
non-elementary subgroup. The elementary fixed-endpoint pair would force that axis invariant. -/
theorem discrete_hyperbolic_axis_moving_pair_nonElementary
    (H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (A F:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hFm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F∈H)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (htA:4<(Matrix.trace A.val)^2)
    (hne:((F•·:ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)≠
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  let K:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hKH:K≤H:=(Subgroup.closure_le H).mpr (by rintro f (rfl|rfl);exact hAm;exact hFm)
  have hdK:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K:=discreteMobius_subgroup_of_le H K hd hKH
  intro he
  have hAH:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr htA
  obtain ⟨a,b,hab,ha,hb,hpres⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elementary_loxodromic_fixed_pair K hdK he (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
    (Subgroup.subset_closure (by simp)) hAH.1
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA
  have hEnds:L.idealEndpoints=({a,b}:Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints]
    ext z
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val z=z ↔ z∈({a,b}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    constructor
    · intro hz
      by_cases hza:z=a
      · exact Or.inl hza
      · by_cases hzb:z=b
        · exact Or.inr (Set.mem_singleton_iff.mpr hzb)
        · exact False.elim (hA (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_eq_one_of_three_fixed _ a b z hab
          (Ne.symm hza) (Ne.symm hzb) ha hb hz))
    · rintro (rfl|rfl)
      · exact ha
      · exact hb
  have hpos:0<(Matrix.SpecialLinearGroup.mapGL ℝ F).val.det:=by
    change 0<F.val.det
    rw [F.det_coe]
    norm_num
  have hGL:(L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F)).idealEndpoints=
      _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix (Matrix.SpecialLinearGroup.mapGL ℝ F)) '' L.idealEndpoints:=
    L.idealEndpoints_realGL_image _ _ hpos (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier])
  have hfrac:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F).val=_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix (Matrix.SpecialLinearGroup.mapGL ℝ F)):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius,MonoidHom.comp_apply,_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_matrix]
  rw [←hfrac,hEnds,hpres ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F,Subgroup.subset_closure (by simp)⟩] at hGL
  have hline:L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F)=L:=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.idealEndpoints_injective (hGL.trans hEnds.symm)
  apply hne
  rw [show ((F•·:ℍ→ℍ) '' L.carrier)=(L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F)).carrier by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier];rfl,hline]

/--
A genuinely nonsimple hyperbolic element has the universal translation-length
bound needed for, directly from the proved Jorgensen displacement theorem.
-/
theorem HalfPlaneFuchsianGroup.nonsimple_translation_sinh_eighth
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (htA:4<(Matrix.trace A.val)^2)
    (hns:¬IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    1/Real.sqrt 8≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2) := by
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA
  have hAH:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr htA
  obtain ⟨g,hgm,hne,x,hx,hgx⟩:=(not_isSimple_iff_crossing H
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) hAm hAH).mp hns
  obtain ⟨F,hF⟩:=mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hgm⟩)
  subst g
  have hneq:((F•·:ℍ→ℍ) '' L.carrier)≠L.carrier:=by
    intro he
    apply hne
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis A hA
      htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_image_realSL,he]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis A hA htA] at hx hgx
  obtain ⟨u,hu,rfl⟩:=hx
  have hp:F•u∈L.carrier:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_realSL] at hgx
    obtain ⟨v,hv,he⟩:=hgx
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_injective he) ▸ hv
  let C:=F*A*F⁻¹
  have hC:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C≠1:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation A F hA
  have htC:4<(Matrix.trace C.val)^2:=by dsimp only [C];rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have hCaxis:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC).carrier=((F•·:ℍ→ℍ) '' L.carrier):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation A F hA
      htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  have hpC:F•u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC).carrier:=by rw [hCaxis];exact mem_image_of_mem _ hu
  let K:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hKH:K≤H:=(Subgroup.closure_le H).mpr (by rintro f (rfl|rfl);exact hAm;exact hgm)
  have hNK:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K:=discrete_hyperbolic_axis_moving_pair_nonElementary H P.discrete A F hAm hgm hA htA hneq
  have hbound:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.eighth_le_hyperbolic_conjugate_sinh_displacement_product (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F) hAH
    (discreteMobius_subgroup_of_le H K P.discrete
      hKH) hNK (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed (F•u))
  have hbridge:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C:=by
    simp only [C,map_mul,map_inv]
  rw [hbridge,halfPlaneH3Embed_sinh_displacement,halfPlaneH3Embed_sinh_displacement] at hbound
  change 1/8≤Real.sinh (dist (F•u) (A•(F•u))/2)*Real.sinh (dist (F•u) (C•(F•u))/2) at hbound
  rw [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_minimum A hA htA (F•u)).mpr hp,
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_minimum C hC htC
      (F•u)).mpr hpC,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_conjugation] at hbound
  apply (sq_le_sq₀ (show 0≤1/Real.sqrt 8 by positivity)
    (Real.sinh_nonneg_iff.mpr (by linarith only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos A hA htA]))).mp
  have he:(1/Real.sqrt (8:ℝ))^2=(1:ℝ)/8:=by norm_num [div_pow,Real.sq_sqrt]
  rw [he,pow_two]
  exact hbound

/-- Every partner has the source maximum-displacement bound when the actual
hyperbolic element is genuinely nonsimple in the original discrete group. -/
theorem HalfPlaneFuchsianGroup.nonsimple_displacementM_eighth
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (B:ℍ≃ᵢℍ)
    (hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (htA:4<(Matrix.trace A.val)^2)
    (hns:¬IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    1/Real.sqrt 8≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) B := by
  have hs:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nonsimple_translation_sinh_eighth P A hAm hA htA hns
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_lower_bound _ _ _).mpr
  intro z
  exact hs.trans ((translation_sinh_displacement_lower (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)
    z).trans (le_max_left _ _))

/-- The actual nonsimple original-disc bound uses the entire original hyperbolic
metric and its true whole-disc infimum. It holds for every partner, without an ellipticity hypothesis. -/
theorem fuchsian_nonsimple_displacementM_eighth
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D:FuchsianDisc H) (f g:H)
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val) (hns:¬IsSimple H f.val) :
    1/Real.sqrt 8≤_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D f g := by
  let A:=D.normalizedLift f
  let B:=D.normalizedLift g
  let q:=D.halfPlaneNormalizer
  have P:HalfPlaneFuchsianGroup D.normalizedGroup:=
    ⟨fun u=>D.normalizedGroup_preserves_halfPlane u.val u.property,D.normalizedGroup_discrete⟩
  have hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation f.val q).mpr hf
  have hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈D.normalizedGroup:=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨f.val,f.property,rfl⟩
  have hnsN:¬IsSimple D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    intro hs
    rw [D.normalizedLift_spec] at hs
    exact hns ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_conjugation H f.val q).mp hs)
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM_eq_native]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nonsimple_displacementM_eighth P A (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) hAm hA.1.1
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA) hnsN

end LowDimensionalTopology.Geometry.Fuchsian
