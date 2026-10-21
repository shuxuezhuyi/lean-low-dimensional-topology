/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicFuchsianModels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem fuchsian_one_parabolic_pair_real_lifts (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    ∃q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∃A B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=q*f*q⁻¹ ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=q*g*q⁻¹ ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (Subgroup.closure ({f,g}
        : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))=
        Subgroup.closure
          ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
            _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
            _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((Matrix.trace (A*B*A⁻¹*B⁻¹).val:ℝ):ℂ) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  obtain ⟨q,A,B,hA,hB,hG,htr⟩:=fuchsian_pair_simultaneous_real_lifts f g D
  have hAp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    rw [hA]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf
  have hdisc : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    let : DiscreteTopology (Subgroup.closure ({f,g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=D.discrete
    have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q (Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))
    change _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      (Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) at h
    rwa [hG] at h
  have hne' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    have h:=hne.conjugation q
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      (Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) at h
    rwa [hG] at h
  exact ⟨q,A,B,hA,hB,hG,htr,hAp,hdisc,hne'⟩


theorem fuchsian_parabolic_commutator_trace_ge_three (f g :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    3≤(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re := by
  obtain ⟨_q,A,B,_hA,_hB,_hG,htr,hAp,hd,hne'⟩:=
    fuchsian_one_parabolic_pair_real_lifts f g D hf hne
  rw [htr,Complex.ofReal_re]
  exact parabolic_commutator_trace_lower_three A B hAp hd hne'

theorem fuchsian_parabolic_ellipticFree_commutator_trace_ge_eighteen (f g :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree (Subgroup.closure ({f,g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    18≤(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re := by
  obtain ⟨q,A,B,_hA,_hB,hG,htr,hAp,_hd,hne'⟩:=
    fuchsian_one_parabolic_pair_real_lifts f g D hf hne
  have hE' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    have h:=hE.conjugation q
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      (Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) at h
    rwa [hG] at h
  rw [htr,Complex.ofReal_re]
  exact parabolic_commutator_trace_lower_eighteen _ hE' A B
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hAp hne'

theorem fuchsian_parabolic_small_trace_has_elliptic (f g :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hsmall : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g).re<18) :
    ∃u∈Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup),_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic u := by
  by_contra hn
  have hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree (Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    intro u hu
    exact hn ⟨u.val,u.property,hu⟩
  exact (not_lt_of_ge
    (fuchsian_parabolic_ellipticFree_commutator_trace_ge_eighteen f g D hf hne hE)) hsmall

end LowDimensionalTopology.Geometry.Fuchsian
