/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicFuchsianModels
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.OneParabolicHeckeModels
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleMobiusQuotients
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
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

/-- The actual simultaneous real lifts retain the literal image of the entire original invariant disc. -/
theorem fuchsian_pair_real_lifts_with_whole_disc (f g:Mobius.complexMobiusGroup)
    (D:FuchsianDisc (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup))) :
    ∃q:Mobius.complexMobiusGroup,∃A B:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=q*f*q⁻¹ ∧_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=q*g*q⁻¹ ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup))=
        Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((Matrix.trace (A*B*A⁻¹*B⁻¹).val:ℝ):ℂ) := by
  obtain ⟨q,hq,hall⟩:=D.halfPlane_normalizer_exists
  obtain ⟨A,hA⟩:=hall (q*f*q⁻¹) ⟨f,Subgroup.subset_closure (Or.inl rfl),rfl⟩
  obtain ⟨B,hB⟩:=hall (q*g*q⁻¹) ⟨g,Subgroup.subset_closure (Or.inr rfl),rfl⟩
  refine ⟨q,A,B,hq,hA,hB,?_,?_⟩
  · change (Subgroup.closure _).map _=_
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,←hA,←hB]
  · rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_commutatorTrace_conjugation f g q,←hA,←hB,realSLMobius_commutatorTrace]

/-- Every original small-trace two-parabolic pair has an actual entire-group exceptional model and the same genuine whole-disc chart. -/
theorem fuchsian_two_parabolic_whole_disc_models (f g:Mobius.complexMobiusGroup)
    (D:FuchsianDisc (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup)))
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup)))
    (hsmall:(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re<18) :
    ∃q:Mobius.complexMobiusGroup,q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      ((∃n:ℕ,∃hn:3≤n,Odd n ∧
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup))=
          unitHeckeMobiusGroup n (by exact_mod_cast hn) ∧
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((2+16*(Real.cos (Real.pi/(n:ℝ)))^4:ℝ):ℂ)) ∨
      (∃p:ℕ,∃hp:2≤p,
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup))=
          closedTriangleMobiusGroup (twoIdealIntegralTriangle p hp) ∧
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((2+16*(Real.cos (Real.pi/(2*(p:ℝ))))^4:ℝ):ℂ))) := by
  obtain ⟨q₀,A,B,hq₀,hA,hB,hG,htr⟩:=fuchsian_pair_real_lifts_with_whole_disc f g D
  have hAp:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [hA]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q₀,rfl⟩)).mp hf
  have hBp:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by
    rw [hB]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q₀,rfl⟩)).mp hg
  have hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup)):=by
    let :DiscreteTopology (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup)):=D.discrete
    have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q₀ (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup))
    change _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q₀
      (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup))) at h
    rwa [hG] at h
  have hNE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup)):=by
    have h:=hne.conjugation q₀
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q₀
      (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup))) at h
    rwa [hG] at h
  have hs:Matrix.trace (A*B*A⁻¹*B⁻¹).val<18:=by
    simpa only [htr,Complex.ofReal_re] using hsmall
  obtain ⟨r,hmodel⟩:=two_parabolic_exceptional_group_models A B hAp hBp hd hNE hs
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r*q₀,?_,?_⟩
  · change (fun z=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r).val (q₀.val z)) '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    rw [←image_image,hq₀,realSLMobius_image_openHalfPlane]
  · rcases hmodel with ⟨n,hn,hodd,hmodel,htrace⟩|⟨p,hp,hmodel,htrace⟩
    · left
      refine ⟨n,hn,hodd,?_,?_⟩
      · rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose,hG]
        exact hmodel
      · rw [htr,htrace]
    · right
      refine ⟨p,hp,?_,?_⟩
      · rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose,hG]
        exact hmodel
      · rw [htr,htrace]

/-- The actual one-parabolic small-trace model uses a chart of the whole original invariant disc. -/
theorem fuchsian_one_parabolic_whole_disc_model (f g:Mobius.complexMobiusGroup)
    (D:FuchsianDisc (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup)))
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup)))
    (hsmall:(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re<6) :
    ∃q:Mobius.complexMobiusGroup,q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      ∃n:ℕ,∃hn:3≤n,
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup))=
          unitHeckeMobiusGroup n (by exact_mod_cast hn) ∧
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((4+2*Real.cos (2*Real.pi/(n:ℝ)):ℝ):ℂ) := by
  obtain ⟨q₀,A,B,hq₀,hA,_hB,hG,htr⟩:=fuchsian_pair_real_lifts_with_whole_disc f g D
  have hAp:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [hA]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q₀,rfl⟩)).mp hf
  have hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup)):=by
    let :DiscreteTopology (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup)):=D.discrete
    have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q₀ (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup))
    change _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q₀
      (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup))) at h
    rwa [hG] at h
  have hNE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set Mobius.complexMobiusGroup)):=by
    have h:=hne.conjugation q₀
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q₀
      (Subgroup.closure ({f,g}:Set Mobius.complexMobiusGroup))) at h
    rwa [hG] at h
  have hs:Matrix.trace (A*B*A⁻¹*B⁻¹).val<6:=by
    simpa only [htr,Complex.ofReal_re] using hsmall
  obtain ⟨r,n,hn,hmodel,htrace⟩:=one_parabolic_small_trace_Hecke_model A B hAp hd hNE hs
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r*q₀,?_,n,hn,?_,?_⟩
  · change (fun z=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r).val (q₀.val z)) '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    rw [←image_image,hq₀,realSLMobius_image_openHalfPlane]
  · rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose,hG]
    exact hmodel
  · rw [htr,htrace]

end LowDimensionalTopology.Geometry.Fuchsian
