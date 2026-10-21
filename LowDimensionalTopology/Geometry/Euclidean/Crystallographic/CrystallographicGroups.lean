/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.ParabolicAffineIsometries
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteTranslationGroups
public import Mathlib.Topology.Algebra.OpenSubgroup
@[expose] public section
noncomputable section
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem affine_conjugate_translation (f : Mobius.mobiusInftyStabilizer) (b : ℂ) :
    f.val * mobiusTranslation b * f.val⁻¹ = mobiusTranslation ((Mobius.mobiusMultiplier f:ℂ)*b) := by
  have hrel : f.val * mobiusTranslation b = mobiusTranslation ((Mobius.mobiusMultiplier f:ℂ)*b) * f.val := by
    apply Subtype.ext
    ext z
    cases z using OnePoint.rec with
    | infty =>
      change f.val.val ((mobiusTranslation b).val ∞) =
        (mobiusTranslation ((Mobius.mobiusMultiplier f:ℂ)*b)).val (f.val.val ∞)
      rw [mobiusTranslation_infty,f.property,mobiusTranslation_infty]
    | coe z =>
      change f.val.val ((mobiusTranslation b).val z) =
        (mobiusTranslation ((Mobius.mobiusMultiplier f:ℂ)*b)).val (f.val.val z)
      rw [mobiusTranslation_coe,Mobius.mobius_affine_formula,Mobius.mobius_affine_formula,mobiusTranslation_coe]
      congr 1
      ring
  rw [hrel,mul_inv_cancel_right]

theorem multiplier_preserves_translationDisplacements (H : Subgroup Mobius.complexMobiusGroup)
    (hi : H ≤ Mobius.mobiusInftyStabilizer) (f : H) (b : ℂ) (hb : b ∈ translationDisplacements H) :
    ((Mobius.subgroupMultiplierHom H hi f:ℂˣ):ℂ)*b ∈ translationDisplacements H := by
  change mobiusTranslation ((Mobius.mobiusMultiplier ⟨f.val,hi f.property⟩:ℂ)*b) ∈ H
  rw [← affine_conjugate_translation ⟨f.val,hi f.property⟩ b]
  exact H.mul_mem (H.mul_mem f.property hb) (H.inv_mem f.property)

theorem discrete_affine_unit_multiplier_range_finite (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hu : ∀ f : H, ‖((Mobius.subgroupMultiplierHom H hi f:ℂˣ):ℂ)‖=1)
    (b : ℂ) (hb0 : b ≠ 0) (hb : b ∈ translationDisplacements H) :
    Finite (Mobius.subgroupMultiplierRange H hi) := by
  let L := translationDisplacements H
  let : DiscreteTopology L := translationDisplacements_discrete H hD
  have hclosed : IsClosed (L : Set ℂ) := AddSubgroup.isClosed_of_discreteTopology
  let K := (L : Set ℂ) ∩ Metric.closedBall (0:ℂ) ‖b‖
  have hK : K.Finite :=
    ((isCompact_closedBall (0:ℂ) ‖b‖).inter_left hclosed).finite
      ((isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology L)).mono inter_subset_left)
  let : Fintype K := hK.fintype
  let F : Mobius.subgroupMultiplierRange H hi → K := fun s => ⟨(s.val:ℂ)*b,by
    obtain ⟨f,hf⟩ := s.property
    constructor
    · rw [← hf]
      exact multiplier_preserves_translationDisplacements H hi f b hb
    · rw [Metric.mem_closedBall,dist_zero_right,norm_mul,← hf,hu f,one_mul]⟩
  apply Finite.of_injective F
  intro s t h
  apply Subtype.ext
  apply Units.ext
  exact mul_right_cancel₀ hb0 (congrArg Subtype.val h)

theorem unit_complex_order_restriction_of_integer_trace (a : ℂˣ)
    (ha : ‖(a:ℂ)‖=1) (ht : ∃ t : ℤ, 2*(a:ℂ).re=(t:ℝ)) :
    orderOf a=1 ∨ orderOf a=2 ∨ orderOf a=3 ∨ orderOf a=4 ∨ orderOf a=6 := by
  obtain ⟨t,ht⟩ := ht
  have hre : |(a:ℂ).re|≤1 := by simpa only [ha] using Complex.abs_re_le_norm (a:ℂ)
  have hlo : (-2:ℤ)≤t := by
    exact_mod_cast (show (-2:ℝ)≤(t:ℝ) by linarith [(abs_le.mp hre).1])
  have hhi : t≤(2:ℤ) := by
    exact_mod_cast (show (t:ℝ)≤(2:ℝ) by linarith [(abs_le.mp hre).2])
  have hnorm : (a:ℂ).re^2+(a:ℂ).im^2=1 := by
    have h := Complex.normSq_eq_norm_sq (a:ℂ)
    rw [ha,one_pow,Complex.normSq_apply] at h
    nlinarith [h]
  have hp : (a:ℂ)^2-(t:ℂ)*(a:ℂ)+1=0 := by
    apply Complex.ext <;> simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,
      pow_two,Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.intCast_re,
      Complex.intCast_im,Complex.one_re,Complex.one_im,Complex.zero_re,Complex.zero_im]
    · rw [← ht]
      nlinarith
    · rw [← ht]
      ring
  have hd : orderOf a ∣ 2 ∨ orderOf a ∣ 3 ∨ orderOf a ∣ 4 ∨ orderOf a ∣ 6 := by
    interval_cases t
    · left
      apply orderOf_dvd_of_pow_eq_one
      apply Units.ext
      change (a:ℂ)^2=1
      norm_num at hp
      have hz : ((a:ℂ)+1)^2=0 := by linear_combination hp
      have he := (sq_eq_zero_iff.mp hz)
      linear_combination ((a:ℂ)-1)*he
    · right;left
      apply orderOf_dvd_of_pow_eq_one
      apply Units.ext
      change (a:ℂ)^3=1
      norm_num at hp
      linear_combination ((a:ℂ)-1)*hp
    · right;right;left
      apply orderOf_dvd_of_pow_eq_one
      apply Units.ext
      change (a:ℂ)^4=1
      norm_num at hp
      linear_combination ((a:ℂ)^2-1)*hp
    · right;right;right
      apply orderOf_dvd_of_pow_eq_one
      apply Units.ext
      change (a:ℂ)^6=1
      norm_num at hp
      linear_combination ((a:ℂ)^4+(a:ℂ)^3-(a:ℂ)-1)*hp
    · left
      apply orderOf_dvd_of_pow_eq_one
      apply Units.ext
      change (a:ℂ)^2=1
      norm_num at hp
      have hz : ((a:ℂ)-1)^2=0 := by linear_combination hp
      have he := (sq_eq_zero_iff.mp hz)
      linear_combination ((a:ℂ)+1)*he
  rcases hd with hd | hd | hd | hd
  all_goals
    have hzero : orderOf a≠0 := by
      intro h
      rw [h] at hd
      norm_num at hd
    have hpos : 0 < orderOf a := Nat.pos_of_ne_zero hzero
    have hbound := Nat.le_of_dvd (by decide) hd
    interval_cases orderOf a
    all_goals norm_num at hd
    all_goals tauto

theorem unit_complex_integer_trace_of_rank_two (a : ℂˣ) (ha : ‖(a:ℂ)‖=1)
    (v w : ℂ) (hv : v≠0) (p q r s : ℤ)
    (hv0 : (a:ℂ)*v=(p:ℂ)*v+(q:ℂ)*w)
    (hv1 : (a:ℂ)*w=(r:ℂ)*v+(s:ℂ)*w) :
    ∃ t : ℤ, 2*(a:ℂ).re=(t:ℝ) := by
  have hp : (a:ℂ)^2-((p+s:ℤ):ℂ)*(a:ℂ)+((p*s-q*r:ℤ):ℂ)=0 := by
    apply (mul_eq_zero.mp (show
      ((a:ℂ)^2-((p+s:ℤ):ℂ)*(a:ℂ)+((p*s-q*r:ℤ):ℂ))*v=0 by
        push_cast
        linear_combination ((a:ℂ)-(s:ℂ))*hv0+(q:ℂ)*hv1)).resolve_right hv
  by_cases hai : (a:ℂ).im=0
  · have hn := Complex.normSq_eq_norm_sq (a:ℂ)
    rw [ha,one_pow,Complex.normSq_apply,hai] at hn
    have he : (a:ℂ).re^2=1 := by nlinarith [hn]
    rcases sq_eq_one_iff.mp he with h | h
    · exact ⟨2,by norm_num; linarith⟩
    · exact ⟨-2,by norm_num; linarith⟩
  · refine ⟨p+s,?_⟩
    have he := congrArg Complex.im hp
    simp only [pow_two,Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.intCast_im,
      Complex.intCast_re,Complex.zero_im] at he
    have hm : (2*(a:ℂ).re-((p+s:ℤ):ℝ))*(a:ℂ).im=0 := by nlinarith [he]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hai)

theorem unit_complex_integer_trace_of_discrete_lattice (a : ℂˣ) (ha : ‖(a:ℂ)‖=1)
    (L : Submodule ℤ ℂ) [DiscreteTopology L] (b : ℂ) (hb : b∈L) (hb0 : b≠0)
    (hpres : ∀ z∈L,(a:ℂ)*z∈L) : ∃ t : ℤ,2*(a:ℂ).re=(t:ℝ) := by
  obtain ⟨n,hn,v,hv,hspan⟩ := Euclidean.discrete_complex_submodule_basis L
  have hmem (i : Fin n) : v i∈L := by
    rw [hspan]
    exact Submodule.subset_span ⟨i,rfl⟩
  have hcoeff (i : Fin n) : ∃ c : Fin n→ℤ,∑ j,c j • v j=(a:ℂ)*v i := by
    apply (Submodule.mem_span_range_iff_exists_fun ℤ).mp
    rw [← hspan]
    exact hpres (v i) (hmem i)
  interval_cases n
  · have hzero : L=⊥ := by simpa using hspan
    exact False.elim (hb0 (by simpa only [hzero,Submodule.mem_bot] using hb))
  · obtain ⟨c,hc⟩ := hcoeff 0
    have he : (a:ℂ)*v 0=(c 0:ℂ)*v 0 := by
      simpa only [Fin.sum_univ_one,zsmul_eq_mul] using hc.symm
    have hva : v 0≠0 := hv.ne_zero 0
    have heq := mul_right_cancel₀ hva he
    have hre := congrArg Complex.re heq
    simp only [Complex.intCast_re] at hre
    refine ⟨2*c 0,?_⟩
    push_cast
    linarith
  · obtain ⟨c,hc⟩ := hcoeff 0
    obtain ⟨d,hd⟩ := hcoeff 1
    apply unit_complex_integer_trace_of_rank_two a ha (v 0) (v 1) (hv.ne_zero 0)
      (c 0) (c 1) (d 0) (d 1)
    · simpa only [Fin.sum_univ_two,zsmul_eq_mul] using hc.symm
    · simpa only [Fin.sum_univ_two,zsmul_eq_mul] using hd.symm

theorem discrete_affine_multiplier_order_restriction (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hu : ∀ f : H, ‖((Mobius.subgroupMultiplierHom H hi f:ℂˣ):ℂ)‖=1)
    (b : ℂ) (hb0 : b≠0) (hb : b∈translationDisplacements H) (f : H) :
    orderOf (Mobius.subgroupMultiplierHom H hi f)=1 ∨
      orderOf (Mobius.subgroupMultiplierHom H hi f)=2 ∨
      orderOf (Mobius.subgroupMultiplierHom H hi f)=3 ∨
      orderOf (Mobius.subgroupMultiplierHom H hi f)=4 ∨
      orderOf (Mobius.subgroupMultiplierHom H hi f)=6 := by
  apply unit_complex_order_restriction_of_integer_trace _ (hu f)
  have : DiscreteTopology (translationDisplacements H) := translationDisplacements_discrete H hD
  have : DiscreteTopology (translationDisplacements H).toIntSubmodule :=
    (inferInstance : DiscreteTopology (translationDisplacements H))
  apply unit_complex_integer_trace_of_discrete_lattice _ (hu f)
    (translationDisplacements H).toIntSubmodule b hb hb0
  exact fun z hz => multiplier_preserves_translationDisplacements H hi f z hz

theorem discrete_affine_multiplier_range_isCyclic (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hu : ∀ f : H, ‖((Mobius.subgroupMultiplierHom H hi f:ℂˣ):ℂ)‖=1)
    (b : ℂ) (hb0 : b≠0) (hb : b∈translationDisplacements H) :
    IsCyclic (Mobius.subgroupMultiplierRange H hi) := by
  have : Finite (Mobius.subgroupMultiplierRange H hi) :=
    discrete_affine_unit_multiplier_range_finite H hD hi hu b hb0 hb
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom ℂ).comp (Mobius.subgroupMultiplierRange H hi).subtype)
    (Units.val_injective.comp Subtype.val_injective)

theorem discrete_affine_multiplier_bounded_generator (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hu : ∀ f : H, ‖((Mobius.subgroupMultiplierHom H hi f:ℂˣ):ℂ)‖=1)
    (b : ℂ) (hb0 : b≠0) (hb : b∈translationDisplacements H) :
    ∃ w : H, ∃ q : ℕ, 0<q ∧ (q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=6) ∧
      orderOf (Mobius.subgroupMultiplierHom H hi w)=q ∧
      ∀ f : H, ∃ k : Fin q,
        Mobius.subgroupMultiplierHom H hi (w^(k:ℕ))=Mobius.subgroupMultiplierHom H hi f := by
  let S := Mobius.subgroupMultiplierRange H hi
  have : Finite S := discrete_affine_unit_multiplier_range_finite H hD hi hu b hb0 hb
  have : IsCyclic S := discrete_affine_multiplier_range_isCyclic H hD hi hu b hb0 hb
  obtain ⟨ω,hω⟩ := IsCyclic.exists_generator (α := S)
  obtain ⟨w,hw⟩ := ω.property
  have horder : orderOf (Mobius.subgroupMultiplierHom H hi w)=orderOf ω := by
    rw [hw]
    exact orderOf_injective S.subtype Subtype.val_injective ω
  refine ⟨w,orderOf ω,orderOf_pos ω,?_,horder,?_⟩
  · rw [← horder]
    exact discrete_affine_multiplier_order_restriction H hD hi hu b hb0 hb w
  · intro f
    let s : S := ⟨Mobius.subgroupMultiplierHom H hi f,⟨f,rfl⟩⟩
    obtain ⟨m,hm⟩ := (isOfFinOrder_of_finite ω).mem_powers_iff_mem_zpowers.mpr (hω s)
    let k : Fin (orderOf ω) := ⟨m%orderOf ω,Nat.mod_lt _ (orderOf_pos ω)⟩
    refine ⟨k,?_⟩
    rw [map_pow,hw]
    have he : ω^(k:ℕ)=s := (pow_mod_orderOf ω m).trans hm
    exact congrArg Subtype.val he

theorem discrete_affine_translation_coset_normal_form (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hu : ∀ f : H, ‖((Mobius.subgroupMultiplierHom H hi f:ℂˣ):ℂ)‖=1)
    (b : ℂ) (hb0 : b≠0) (hb : b∈translationDisplacements H) :
    ∃ w : H, ∃ q : ℕ, 0<q ∧ (q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=6) ∧
      orderOf (Mobius.subgroupMultiplierHom H hi w)=q ∧
      ∀ f : Mobius.complexMobiusGroup, f∈H ↔ ∃ k : Fin q,∃ c∈translationDisplacements H,
        f=mobiusTranslation c*w.val^(k:ℕ) := by
  obtain ⟨w,q,hq,hallowed,horder,hw⟩ := discrete_affine_multiplier_bounded_generator H hD hi hu b hb0 hb
  refine ⟨w,q,hq,hallowed,horder,?_⟩
  intro f
  constructor
  · intro hf
    obtain ⟨k,hk⟩ := hw ⟨f,hf⟩
    let t : H := ⟨f,hf⟩*(w^(k:ℕ))⁻¹
    have ht : t∈subgroupTranslations H hi := by
      rw [← subgroupMultiplier_kernel_eq_translations]
      change Mobius.subgroupMultiplierHom H hi t=1
      simp only [t,map_mul,map_inv,← hk,mul_inv_cancel]
    obtain ⟨c,hc⟩ := (mem_subgroupTranslations_iff H hi t).mp ht
    refine ⟨k,c,?_,?_⟩
    · change mobiusTranslation c∈H
      rw [← hc]
      exact t.property
    · have he : t.val*w.val^(k:ℕ)=f := by
        change (f*(w.val^(k:ℕ))⁻¹)*w.val^(k:ℕ)=f
        group
      rw [hc] at he
      exact he.symm
  · rintro ⟨k,c,hc,rfl⟩
    exact H.mul_mem hc (H.pow_mem w.property (k:ℕ))

theorem affine_conjugate_to_scaling_by_translation (f : Mobius.mobiusInftyStabilizer)
    (hf : Mobius.mobiusMultiplier f≠1) :
    ∃ u : Mobius.complexMobiusGroup, (∀ b : ℂ,u*mobiusTranslation b*u⁻¹=mobiusTranslation b) ∧
      u*f.val*u⁻¹=Mobius.mobiusScaling (Mobius.mobiusMultiplier f) := by
  let a : ℂ := Mobius.mobiusMultiplier f
  let c : ℂ := Mobius.mobiusAffineConstant f/(1-a)
  have ha : a≠1 := fun h => hf (Units.ext h)
  have hden : 1-a≠0 := sub_ne_zero.mpr ha.symm
  have hcen : (1-a)*c=Mobius.mobiusAffineConstant f := by
    dsimp [c]
    field_simp
  let u := mobiusTranslation (-c)
  have hui : u⁻¹=mobiusTranslation c := by
    change (mobiusTranslation (-c))⁻¹=mobiusTranslation c
    rw [mobiusTranslation_neg,inv_inv]
  refine ⟨u,?_,?_⟩
  · intro b
    rw [hui]
    change mobiusTranslation (-c)*mobiusTranslation b*mobiusTranslation c=mobiusTranslation b
    rw [← mobiusTranslation_add,← mobiusTranslation_add]
    congr 1
    abel
  · apply Subtype.ext
    ext z
    cases z using OnePoint.rec with
    | infty =>
      change u.val (f.val.val ((u⁻¹).val ∞))=_
      rw [hui]
      dsimp only [u]
      rw [mobiusTranslation_infty,f.property,mobiusTranslation_infty,Mobius.mobiusScaling_infty]
    | coe z =>
      change u.val (f.val.val ((u⁻¹).val z))=_
      rw [hui]
      dsimp only [u]
      rw [mobiusTranslation_coe,Mobius.mobius_affine_formula,mobiusTranslation_coe,Mobius.mobiusScaling_coe]
      congr 1
      change a*(z+c)+Mobius.mobiusAffineConstant f+-c=a*z
      linear_combination -hcen

theorem conjugation_translation_power_normal_form (u w : Mobius.complexMobiusGroup) (a : ℂˣ)
    (ht : ∀ b : ℂ,u*mobiusTranslation b*u⁻¹=mobiusTranslation b)
    (hw : u*w*u⁻¹=Mobius.mobiusScaling a) (b : ℂ) (k : ℕ) :
    u*(mobiusTranslation b*w^k)*u⁻¹=mobiusTranslation b*(Mobius.mobiusScaling a)^k := by
  calc
    _ = (u*mobiusTranslation b*u⁻¹)*(u*w*u⁻¹)^k := by rw [conj_pow];group
    _ = _ := by rw [ht,hw]

theorem nonzero_translationDisplacements_basis (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (b : ℂ) (hb : b∈translationDisplacements H) (hb0 : b≠0) :
    ∃ n : ℕ, 1≤n ∧ n≤2 ∧ ∃ v : Fin n→ℂ,LinearIndependent ℝ v ∧
      (translationDisplacements H : Set ℂ)=(Submodule.span ℤ (Set.range v):Set ℂ) := by
  obtain ⟨n,hn,v,hv,hspan⟩ := translationDisplacements_basis H hD
  have hpos : 1≤n := by
    by_contra hn0
    have he : n=0 := by omega
    subst n
    have hm : b∈Submodule.span ℤ (Set.range v) := (Set.ext_iff.mp hspan b).mp hb
    have hempty : Set.range v=∅ := Set.range_eq_empty_iff.mpr inferInstance
    rw [hempty,Submodule.span_empty,Submodule.mem_bot] at hm
    exact hb0 hm
  exact ⟨n,hpos,hn,v,hv,hspan⟩

theorem discrete_affine_centered_normal_form (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hu : ∀ f : H, ‖((Mobius.subgroupMultiplierHom H hi f:ℂˣ):ℂ)‖=1)
    (b : ℂ) (hb0 : b≠0) (hb : b∈translationDisplacements H) :
    ∃ u : Mobius.complexMobiusGroup,∃ a : ℂˣ,∃ q : ℕ,0<q ∧
      (q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=6) ∧ ‖(a:ℂ)‖=1 ∧ orderOf a=q ∧
      ∀ f : Mobius.complexMobiusGroup,f∈DiscreteGroups.Action.Actions.subgroupConjugate u H ↔
        ∃ k : Fin q,∃ c∈translationDisplacements H,f=mobiusTranslation c*(Mobius.mobiusScaling a)^(k:ℕ) := by
  obtain ⟨w,q,hq,hallowed,horder,hcoset⟩ := discrete_affine_translation_coset_normal_form H hD hi hu b hb0 hb
  let wi : Mobius.mobiusInftyStabilizer := ⟨w.val,hi w.property⟩
  by_cases hw1 : Mobius.mobiusMultiplier wi=1
  · have hwT : w∈subgroupTranslations H hi := by
      rw [← subgroupMultiplier_kernel_eq_translations]
      exact hw1
    have hallT : ∀ f∈H,∃ c,f=mobiusTranslation c := by
      intro f hf
      obtain ⟨k,c,hc,hf⟩ := (hcoset f).mp hf
      let t : H := ⟨mobiusTranslation c,hc⟩
      have ht : t∈subgroupTranslations H hi := ⟨c,rfl⟩
      obtain ⟨d,hd⟩ := (mem_subgroupTranslations_iff H hi (t*w^(k:ℕ))).mp
        ((subgroupTranslations H hi).mul_mem ht ((subgroupTranslations H hi).pow_mem hwT (k:ℕ)))
      exact ⟨d,hf.trans hd⟩
    refine ⟨1,1,q,hq,hallowed,by simp,?_,?_⟩
    · change orderOf (Mobius.mobiusMultiplier wi)=q at horder
      simpa only [hw1] using horder
    · intro f
      constructor
      · rintro ⟨g,hg,hgf⟩
        change (1:Mobius.complexMobiusGroup)*g*1⁻¹=f at hgf
        simp only [one_mul,mul_one,inv_one] at hgf
        obtain ⟨c,hc⟩ := hallT g hg
        refine ⟨⟨0,hq⟩,c,?_,?_⟩
        · change mobiusTranslation c∈H
          rw [← hc]
          exact hg
        · simp only [pow_zero,mul_one]
          exact hgf.symm.trans hc
      · rintro ⟨k,c,hc,hf⟩
        rw [mobiusScaling_one,one_pow,mul_one] at hf
        exact ⟨mobiusTranslation c,hc,by
          change (1:Mobius.complexMobiusGroup)*mobiusTranslation c*1⁻¹=f
          simpa only [one_mul,mul_one,inv_one] using hf.symm⟩
  · obtain ⟨u,ht,hw⟩ := affine_conjugate_to_scaling_by_translation wi hw1
    refine ⟨u,Mobius.mobiusMultiplier wi,q,hq,hallowed,hu w,horder,?_⟩
    intro f
    constructor
    · rintro ⟨g,hg,hgf⟩
      obtain ⟨k,c,hc,hgform⟩ := (hcoset g).mp hg
      refine ⟨k,c,hc,?_⟩
      rw [← hgf,hgform]
      exact conjugation_translation_power_normal_form u w.val _ ht hw c (k:ℕ)
    · rintro ⟨k,c,hc,hf⟩
      refine ⟨mobiusTranslation c*w.val^(k:ℕ),H.mul_mem hc (H.pow_mem w.property (k:ℕ)),?_⟩
      rw [hf]
      exact conjugation_translation_power_normal_form u w.val _ ht hw c (k:ℕ)

theorem discrete_affine_integer_normal_form (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hu : ∀ f : H, ‖((Mobius.subgroupMultiplierHom H hi f:ℂˣ):ℂ)‖=1)
    (b : ℂ) (hb0 : b≠0) (hb : b∈translationDisplacements H) :
    ∃ u : Mobius.complexMobiusGroup,∃ a : ℂˣ,∃ q : ℕ,0<q ∧
      (q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=6) ∧ ‖(a:ℂ)‖=1 ∧ orderOf a=q ∧
      ∃ n : ℕ,1≤n ∧ n≤2 ∧ ∃ v : Fin n→ℂ,LinearIndependent ℝ v ∧
        ∀ f : Mobius.complexMobiusGroup,f∈DiscreteGroups.Action.Actions.subgroupConjugate u H ↔
          ∃ k : Fin q,∃ c : Fin n→ℤ,
            f=mobiusTranslation (∑ i,c i • v i)*(Mobius.mobiusScaling a)^(k:ℕ) := by
  obtain ⟨u,a,q,hq,hallowed,ha,horder,hform⟩ := discrete_affine_centered_normal_form H hD hi hu b hb0 hb
  obtain ⟨n,hn0,hn,v,hv,hspan⟩ := nonzero_translationDisplacements_basis H hD b hb hb0
  refine ⟨u,a,q,hq,hallowed,ha,horder,n,hn0,hn,v,hv,?_⟩
  intro f
  rw [hform]
  constructor
  · rintro ⟨k,c,hc,hf⟩
    have hm : c∈Submodule.span ℤ (Set.range v) := (Set.ext_iff.mp hspan c).mp hc
    obtain ⟨d,hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hm
    exact ⟨k,d,by rw [hd];exact hf⟩
  · rintro ⟨k,c,hf⟩
    refine ⟨k,∑ i,c i • v i,?_,hf⟩
    apply (Set.ext_iff.mp hspan _).mpr
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c,rfl⟩

theorem mobius_subgroupConjugate_mul (u q : Mobius.complexMobiusGroup) (H : Subgroup Mobius.complexMobiusGroup) :
    DiscreteGroups.Action.Actions.subgroupConjugate u (DiscreteGroups.Action.Actions.subgroupConjugate q
      H)=DiscreteGroups.Action.Actions.subgroupConjugate (u*q) H := by
  ext f
  constructor
  · rintro ⟨g,⟨h,hh,hg⟩,hf⟩
    change q*h*q⁻¹=g at hg
    change u*g*u⁻¹=f at hf
    refine ⟨h,hh,?_⟩
    change (u*q)*h*(u*q)⁻¹=f
    rw [← hf,← hg]
    group
  · rintro ⟨g,hg,hf⟩
    change (u*q)*g*(u*q)⁻¹=f at hf
    refine ⟨q*g*q⁻¹,⟨g,hg,rfl⟩,?_⟩
    change u*(q*g*q⁻¹)*u⁻¹=f
    rw [← hf]
    group

theorem discrete_elementary_parabolic_integer_normal_form (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (hE : IsElementary H) (p : Mobius.complexMobiusGroup)
    (hpH : p∈H) (hp : Mobius.MobiusParabolic p) :
    ∃ u : Mobius.complexMobiusGroup,∃ a : ℂˣ,∃ q : ℕ,0<q ∧
      (q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=6) ∧ ‖(a:ℂ)‖=1 ∧ orderOf a=q ∧
      ∃ n : ℕ,1≤n ∧ n≤2 ∧ ∃ v : Fin n→ℂ,LinearIndependent ℝ v ∧
        ∀ f : Mobius.complexMobiusGroup,f∈DiscreteGroups.Action.Actions.subgroupConjugate u H ↔
          ∃ k : Fin q,∃ c : Fin n→ℤ,
            f=mobiusTranslation (∑ i,c i • v i)*(Mobius.mobiusScaling a)^(k:ℕ) := by
  obtain ⟨r,hi,hu⟩ := discrete_elementary_parabolic_euclidean_coordinates H hD hE p hpH hp
  let K := DiscreteGroups.Action.Actions.subgroupConjugate r H
  have hKD : Mobius.IsDiscreteMobiusSubgroup K := by
    have : DiscreteTopology H := hD
    exact DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete r H
  let P : K := ⟨r*p*r⁻¹,⟨p,hpH,rfl⟩⟩
  have hP : Mobius.MobiusParabolic P.val := by
    apply (Mobius.mobiusParabolic_isConj (show IsConj p P.val from ?_)).mp hp
    exact isConj_iff.mpr ⟨r,rfl⟩
  let Pi : Mobius.mobiusInftyStabilizer := ⟨P.val,hi P.property⟩
  have hmul : Mobius.mobiusMultiplier Pi=1 :=
    (mobiusMultiplier_eq_one_iff_parabolic_or_identity Pi).mpr (Or.inl hP)
  obtain ⟨b,hb⟩ := (mobiusMultiplier_eq_one_iff_translation Pi).mp hmul
  have hbmem : b∈translationDisplacements K := by
    change mobiusTranslation b∈K
    rw [← hb]
    exact P.property
  have hb0 : b≠0 := by
    intro he
    apply hP.1
    rw [hb,he,(mobiusTranslation_eq_one_iff 0).mpr rfl]
  obtain ⟨u,a,q,hq,hallowed,ha,horder,n,hn0,hn,v,hv,hform⟩ :=
    discrete_affine_integer_normal_form K hKD hi (fun f => (hu f).1) b hb0 hbmem
  refine ⟨u*r,a,q,hq,hallowed,ha,horder,n,hn0,hn,v,hv,?_⟩
  intro f
  rw [← mobius_subgroupConjugate_mul]
  exact hform f

end LowDimensionalTopology.Geometry.DiscreteGroups
