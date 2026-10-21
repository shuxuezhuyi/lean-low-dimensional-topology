/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.HyperbolicCanonicalHeight
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

theorem native_ellipticFree_trace_sq_lower (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) :
    4≤(Matrix.trace A.val)^2 := by
  have h:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_specialLinear_trace H hD hE
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom A) hAm).2
  have he : (Matrix.trace (Matrix.SpecialLinearGroup.map Complex.ofRealHom A).val).re=
      Matrix.trace A.val := by simp [Matrix.trace_fin_two]
  rw [he] at h
  rcases h with h|h <;> nlinarith

theorem canonical_translation_mul_trace (t : ℝ) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t*B).val=Matrix.trace B.val+t*B 1 0 := by
  simp only [Matrix.trace_fin_two,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL]
  ring

theorem canonical_translation_inverse (t : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]

theorem trace_pair_abs_gap (s v : ℝ) (hp : 4≤(s+v)^2) (hm : 4≤(s-v)^2) :
    4≤(|s|-|v|)^2 := by
  by_cases hs : 0≤s
  · by_cases hv : 0≤v
    · rw [abs_of_nonneg hs,abs_of_nonneg hv]
      exact hm
    · rw [abs_of_nonneg hs,abs_of_neg (lt_of_not_ge hv)]
      nlinarith [hp]
  · by_cases hv : 0≤v
    · rw [abs_of_neg (lt_of_not_ge hs),abs_of_nonneg hv]
      nlinarith [hp]
    · rw [abs_of_neg (lt_of_not_ge hs),abs_of_neg (lt_of_not_ge hv)]
      nlinarith [hm]

theorem trace_gap_large_step (s y : ℝ) (hs : 4<s^2) (hy : 0≤y)
    (hscale : s^2-4≤y^2) (hgap : 4≤(|s|-y)^2) : |s|+2≤y := by
  have ha : 2< |s| := by nlinarith [sq_abs s,abs_nonneg s]
  have hl : |s|-2<y := by
    by_contra hn
    have hb : y≤|s|-2 := le_of_not_gt hn
    have hsq:=mul_self_le_mul_self hy hb
    nlinarith [hsq,hscale,sq_abs s]
  by_contra hn
  have hu : y< |s|+2 := lt_of_not_ge hn
  have hp:=mul_pos (by linarith : 0<2-(|s|-y)) (by linarith : 0<(|s|-y)+2)
  nlinarith [hp,hgap]

theorem simple_hyperbolic_translation_trace_radius (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htB : 4<(Matrix.trace B.val)^2) (hSimple : IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (t : ℝ) (ht : t≠0) (htm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H) (hc : B 1 0≠0) :
    (Matrix.trace B.val)^2-4≤(t*B 1 0)^2 := by
  obtain ⟨r,hr,haxis,hR⟩:=hyperbolic_axis_finite_circle B hB htB hc
  have hd:=simple_hyperbolic_translation_radius H B hB htB hSimple t ht htm _ r hr haxis
  have hm:=mul_le_mul_of_nonneg_left hd (abs_nonneg (B 1 0))
  have hsq:=(sq_le_sq₀ (by positivity : 0≤|B 1 0| *(2*r)) (by positivity : 0≤|B 1 0| *|t|)).mpr hm
  simp only [mul_pow,sq_abs] at hsq
  nlinarith [hsq,hR]

theorem simple_hyperbolic_translation_coefficient_gap (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htB : 4<(Matrix.trace B.val)^2) (hSimple : IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (t : ℝ) (ht : t≠0) (htm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H) (hc : B 1 0≠0) :
    |Matrix.trace B.val|+2≤|t*B 1 0| := by
  have htminus : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t))∈H := by
    rw [canonical_translation_inverse,map_inv]
    exact H.inv_mem htm
  have hp:=native_ellipticFree_trace_sq_lower H hD hE (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
    t*B)
    (by rw [map_mul];exact H.mul_mem htm hSimple.1)
  have hm:=native_ellipticFree_trace_sq_lower H hD hE (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
    (-t)*B)
    (by rw [map_mul];exact H.mul_mem htminus hSimple.1)
  rw [canonical_translation_mul_trace] at hp hm
  have hgap:=trace_pair_abs_gap (Matrix.trace B.val) (t*B 1 0) hp (by nlinarith [hm])
  exact trace_gap_large_step _ _ htB (abs_nonneg _) (by
    rw [sq_abs]
    exact simple_hyperbolic_translation_trace_radius H B hB htB hSimple t ht htm hc) hgap

theorem canonical_translation_simple_hyperbolic_disjoint (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htB : 4<(Matrix.trace B.val)^2) (hSimple : IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (t : ℝ) (ht : t≠0) (htm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈H) (hc : B 1 0≠0) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B) := by
  apply Set.disjoint_left.mpr
  intro z hzT hzB
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_translation] at hzT
  change |t|/2<z.im at hzT
  have htr : Matrix.trace B.val≠0 := by intro he;rw [he] at htB;norm_num at htB
  have hh:=canonical_region_height_bound B hc htr z hzB
  have hg:=simple_hyperbolic_translation_coefficient_gap H hD hE B hB htB hSimple t ht htm hc
  rw [abs_mul] at hg
  have hl:=mul_lt_mul_of_pos_left hzT (abs_pos.mpr hc)
  nlinarith [hg,hh,hl]


theorem discrete_parabolic_hyperbolic_pair_nonElementary (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hdH : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (A B : Matrix.SpecialLinearGroup
      (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hParA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hHypB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  let L:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hle : L≤H:=(Subgroup.closure_le H).mpr (by
    intro f hf
    rcases hf with rfl|hf
    · exact hAm
    · simpa only [Set.mem_singleton_iff] using hf ▸ hBm)
  have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈L:=Subgroup.subset_closure (by simp)
  have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈L:=Subgroup.subset_closure (by simp)
  intro he
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elementary_parabolic_no_loxodromic L
    (discreteMobius_subgroup_of_le H L hdH hle) he _ hA hParA _ hB hHypB.1

theorem translation_hyperbolic_lowerLeft_nezero (t : ℝ)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) : B 1 0≠0 := by
  intro hc
  apply hPair
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_elementary_of_common_fixed _ _ ∞
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff _).mpr rfl
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff B).mpr hc

theorem canonical_parabolic_simple_hyperbolic_disjoint (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hdH : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H) (hParA :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hSimpleB : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B) := by
  have hPair:=discrete_parabolic_hyperbolic_pair_nonElementary H hdH A B hAm hSimpleB.1
    hParA hSimpleB.2.1
  obtain ⟨q,t,ht,hnorm⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hParA
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H
  have hprojA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
    rw [←map_inv,←map_mul,←map_mul]
    rcases hnorm with he|he
    · rw [he]
    · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  have hprojB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹) := by simp only [map_mul,map_inv]
  have hTmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)∈K:=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ H
      _).mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hAm,hprojA⟩
  have hsQ : IsSimple K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)):=by
    rw [←hprojB]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_conjugation H _ _).mpr hSimpleB
  have hPairQ : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    have he:=hPair.conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,hprojA,hprojB] at he
    exact he
  have hc:=translation_hyperbolic_lowerLeft_nezero t (q*B*q⁻¹) hPairQ
  have hdisjoint:=canonical_translation_simple_hyperbolic_disjoint K
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.invariantDisc_conjugate H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) hD) (hE.conjugation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q))
    (q*B*q⁻¹) hsQ.2.1.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
      hsQ.2.1.1.1).mp hsQ.2.1)
    hsQ t ht hTmem hc
  apply (Set.disjoint_image_iff (MulAction.injective q)).mp
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_conjugation A
    q,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_conjugation B q]
  rcases hnorm with he|he
  · rw [he]
    exact hdisjoint
  · rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_neg]
    exact hdisjoint

end LowDimensionalTopology.Geometry.Fuchsian
