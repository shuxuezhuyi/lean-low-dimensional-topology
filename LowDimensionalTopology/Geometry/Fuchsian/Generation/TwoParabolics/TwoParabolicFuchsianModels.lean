/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicHeckeModels
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
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

theorem realSLMobius_commutatorTrace (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=
      ((Matrix.trace (A*B*A⁻¹*B⁻¹).val:ℝ):ℂ) := by
  let M : Matrix.SpecialLinearGroup (Fin 2) ℝ →* Matrix.SpecialLinearGroup (Fin 2) ℂ :=
    Matrix.SpecialLinearGroup.map Complex.ofRealHom
  have hm : _root_.LowDimensionalTopology.Geometry.Mobius.Classification.specialCommutator (M A) (M B)=M (A*B*A⁻¹*B⁻¹) := by
    simp only [_root_.LowDimensionalTopology.Geometry.Mobius.Classification.specialCommutator,map_mul,map_inv]
  change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection (M A))
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection (M B))=_
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace_representatives _ _ (M A) (M B) rfl rfl,hm]
  simp [M,Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two,Matrix.adjugate_fin_two]

theorem fuchsian_pair_simultaneous_real_lifts (f g : Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup))) :
    ∃q : Mobius.complexMobiusGroup,∃A B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=q*f*q⁻¹ ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=q*g*q⁻¹ ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup))=
        Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((Matrix.trace (A*B*A⁻¹*B⁻¹).val:ℝ):ℂ) := by
  obtain ⟨q,_hq,hall⟩:=D.halfPlane_normalizer_exists
  obtain ⟨A,hA⟩:=hall (q*f*q⁻¹)
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _ _).mpr ⟨f,Subgroup.subset_closure (by simp),rfl⟩)
  obtain ⟨B,hB⟩:=hall (q*g*q⁻¹)
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _ _).mpr ⟨g,Subgroup.subset_closure (by simp),rfl⟩)
  refine ⟨q,A,B,hA,hB,?_,?_⟩
  · change (Subgroup.closure _).map _=_
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,←hA,←hB]
  · rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_commutatorTrace_conjugation f g q,←hA,←hB,realSLMobius_commutatorTrace]

theorem fuchsian_parabolic_pair_real_lifts (f g : Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup))) :
    ∃q : Mobius.complexMobiusGroup,∃A B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=q*f*q⁻¹ ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=q*g*q⁻¹ ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup))=
        Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((Matrix.trace (A*B*A⁻¹*B⁻¹).val:ℝ):ℂ) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)) := by
  obtain ⟨q,A,B,hA,hB,hG,htr⟩:=fuchsian_pair_simultaneous_real_lifts f g D
  have hAp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    rw [hA]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf
  have hBp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := by
    rw [hB]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hg
  have hdisc : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)) := by
    let : DiscreteTopology (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)):=D.discrete
    have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup))
    change _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup))) at h
    rwa [hG] at h
  have hne' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)) := by
    have h:=hne.conjugation q
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup))) at h
    rwa [hG] at h
  exact ⟨q,A,B,hA,hB,hG,htr,hAp,hBp,hdisc,hne'⟩

theorem fuchsian_two_parabolic_trace_alternatives
    (f g : Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup))) :
    ∃t : ℝ,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=(t:ℂ) ∧
      (18≤t ∨ (∃n : ℕ,3≤n ∧ t=2+16*(Real.cos (Real.pi/(n:ℝ)))^4) ∨
        (∃p : ℕ,2≤p ∧ t=2+16*(Real.cos (Real.pi/(2*(p:ℝ))))^4)) := by
  obtain ⟨_q,A,B,_hA,_hB,_hG,htr,hAp,hBp,hd,hne'⟩:=
    fuchsian_parabolic_pair_real_lifts f g D hf hg hne
  exact ⟨_,htr,two_parabolic_commutator_trace_alternatives A B hAp hBp hd hne'⟩


theorem fuchsian_two_parabolic_exceptional_group_models
    (f g : Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup)))
    (hsmall : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re<18) :
    ∃q : Mobius.complexMobiusGroup,
      (∃n : ℕ,∃hn : 3≤n,Odd n ∧
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup))=
          unitHeckeMobiusGroup n (by exact_mod_cast hn) ∧
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((2+16*(Real.cos (Real.pi/(n:ℝ)))^4:ℝ):ℂ)) ∨
      (∃p : ℕ,∃hp : 2≤p,
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup))=
          (nativeConformalSubgroupMobiusHom (triangleConformalGroup (twoIdealIntegralTriangle p hp))
            inf_le_right).range ∧
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((2+16*(Real.cos (Real.pi/(2*(p:ℝ))))^4:ℝ):ℂ)) := by
  obtain ⟨q₀,A,B,_hA,_hB,hG,htr,hAp,hBp,hd,hne'⟩:=
    fuchsian_parabolic_pair_real_lifts f g D hf hg hne
  have hs : Matrix.trace (A*B*A⁻¹*B⁻¹).val<18 := by
    simpa only [htr,Complex.ofReal_re] using hsmall
  obtain ⟨q,hmodel⟩:=two_parabolic_exceptional_group_models A B hAp hBp hd hne' hs
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*q₀,?_⟩
  rcases hmodel with ⟨n,hn,hodd,hmodel,htrace⟩|⟨p,hp,hmodel,htrace⟩
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

end LowDimensionalTopology.Geometry.Fuchsian
