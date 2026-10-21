/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicHyperbolicSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.HyperbolicProducts
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.ParabolicEllipticCommutators
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicProducts
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem translation_ellipticFree_coefficient_bound (G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G) (t : ℝ) (ht : t≠0) (B :
      Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hTm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈G) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    4≤|t*B 1 0| := by
  have hc:=translation_hyperbolic_lowerLeft_nezero t B hPair
  apply ellipticFree_progression_gap (Matrix.trace B.val) (t*B 1 0) (mul_ne_zero ht hc)
  intro n
  have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)^n*B)∈G:=by
    rw [map_mul,map_zpow]
    exact G.mul_mem (G.zpow_mem hTm n) hBm
  have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_not_elliptic_abs_trace ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)^n*B) (hE ⟨_,hm⟩)
  rw [hTranslationSL_zpow,canonical_translation_mul_trace] at h
  simpa only [mul_assoc] using h

theorem translation_commutator_trace_lower_three (t : ℝ)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    3≤Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹*B⁻¹).val := by
  have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.one_le_jorgensenDefect_of_discrete_nonElementary _ _ hd hne
  rw [translation_jorgensen_defect,sq_abs] at h
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_commutator_trace]
  linarith

theorem translation_commutator_trace_lower_eighteen (G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G) (t : ℝ) (ht : t≠0) (B :
      Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hTm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈G) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    18≤Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹*B⁻¹).val := by
  have h:=translation_ellipticFree_coefficient_bound G hE t ht B hTm hBm hPair
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_commutator_trace]
  nlinarith [sq_abs (t*B 1 0)]


theorem hSL_commutator_trace_neg_left (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace ((-A)*B*(-A)⁻¹*B⁻¹).val=Matrix.trace (A*B*A⁻¹*B⁻¹).val := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_commutator_trace (-A)
    B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_commutator_trace A B]
  simp only [neg_mul,Matrix.SpecialLinearGroup.coe_neg,Matrix.trace_neg]
  ring

theorem parabolic_normalization_commutator_trace (A B q : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (t : ℝ) (hnorm : q*A*q⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t ∨ q*A*q⁻¹=
      -(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) :
    Matrix.trace (A*B*A⁻¹*B⁻¹).val=
      Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*(q*B*q⁻¹)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹*(q*B*q⁻¹)⁻¹).val := by
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation (A*B*A⁻¹*B⁻¹)
    q,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_commutator_conjugation]
  rcases hnorm with he|he
  · rw [he]
  · rw [he,hSL_commutator_trace_neg_left]

theorem parabolic_commutator_trace_lower_three (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    3≤Matrix.trace (A*B*A⁻¹*B⁻¹).val := by
  obtain ⟨q,t,_ht,hnorm⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  have hprojA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
    rw [←map_inv,←map_mul,←map_mul]
    rcases hnorm with he|he
    · rw [he]
    · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  have hprojB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹) := by
    simp only [map_mul,map_inv]
  have hdQ : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    let H:=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    let : DiscreteTopology H:=hd
    have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H
    change DiscreteTopology (H.map (MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      q)).toMonoidHom) at h
    dsimp only [H] at h
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,hprojA,hprojB] at h
    exact h
  have hnQ : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    have h:=hne.conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,hprojA,hprojB] at h
    exact h
  rw [parabolic_normalization_commutator_trace A B q t hnorm]
  exact translation_commutator_trace_lower_three t _ hdQ hnQ

theorem parabolic_commutator_trace_lower_eighteen (G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G) (A B : Matrix.SpecialLinearGroup (Fin
      2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈G) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    18≤Matrix.trace (A*B*A⁻¹*B⁻¹).val := by
  obtain ⟨q,t,ht,hnorm⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) G
  have hprojA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
    rw [←map_inv,←map_mul,←map_mul]
    rcases hnorm with he|he
    · rw [he]
    · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  have hprojB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹) := by
    simp only [map_mul,map_inv]
  have hTmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈K:=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ G
      _).mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hAm,hprojA⟩
  have hBmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)∈K:=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ G
      _).mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,hBm,hprojB⟩
  have hnQ : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    have h:=hne.conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,hprojA,hprojB] at h
    exact h
  rw [parabolic_normalization_commutator_trace A B q t hnorm]
  exact translation_commutator_trace_lower_eighteen K (hE.conjugation _) t ht _ hTmem hBmem hnQ

theorem parabolic_small_commutator_has_elliptic (G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈G) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hsmall : Matrix.trace (A*B*A⁻¹*B⁻¹).val<18) : ∃g∈G,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g := by
  by_contra hn
  have hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G:=by
    intro g hg
    exact hn ⟨g.val,g.property,hg⟩
  exact (not_lt_of_ge (parabolic_commutator_trace_lower_eighteen G hE A B hAm hBm hA hne)) hsmall

end LowDimensionalTopology.Geometry.Fuchsian
