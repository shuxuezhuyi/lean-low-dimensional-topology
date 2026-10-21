/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteDihedralGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusDiscontinuity

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem affineMobius_apply_coe (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    (Mobius.affineMobius a b ha).val z = ((a*z+b : ℂ) : Mobius.ExtendedComplex) := by
  rw [Mobius.affineMobius_coe]
  exact Mobius.affineHomeomorph_coe a b z ha

theorem affineMobius_apply_infty (a b : ℂ) (ha : a ≠ 0) :
    (Mobius.affineMobius a b ha).val ∞ = ∞ := by
  rw [Mobius.affineMobius_coe]
  exact Mobius.affineHomeomorph_infty a b ha

theorem continuous_upperHalfSpacePoint_horizontal (t : ℝ) (ht : 0 < t) :
    Continuous (fun z : ℂ => Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint z t ht) := by
  apply Continuous.subtype_mk
  have hcont := Hyperbolic.QuaternionHalfSpace.complexQuaternionPlane.continuous.add
    (continuous_const : Continuous (fun _ : ℂ => Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 t))
  convert hcont using 1
  funext z
  apply Subtype.ext
  apply Quaternion.ext <;> simp
    [Hyperbolic.QuaternionHalfSpace.complexQuaternionPlane_apply,Hyperbolic.QuaternionHalfSpace.quaternionThreePoint]

theorem affineMobius_smul_j (a b : ℂ) (ha : a ≠ 0) :
    Mobius.affineMobius a b ha • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ =
      Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint b ‖a‖ (norm_pos_iff.mpr ha) := by
  apply Subtype.ext
  rw [Mobius.affineMobius_smul, Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_horizontal,
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_height, mul_zero, zero_add, mul_one]
  rfl

theorem affine_geometric_translation_tendsto (a b c : ℂ) (ha : a ≠ 0) (hc : 1 < ‖c‖) :
    Tendsto (fun n : ℕ => Mobius.affineMobius a (b/c^n) ha • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) atTop
      (𝓝 (Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint 0 ‖a‖ (norm_pos_iff.mpr ha))) := by
  have hi : ‖c⁻¹‖ < 1 := by
    rw [norm_inv,inv_lt_one₀ (by linarith : 0 < ‖c‖)]
    exact hc
  have hp : Tendsto (fun n : ℕ => b/c^n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,inv_pow,mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hi).const_mul b
  simp_rw [affineMobius_smul_j]
  exact (continuous_upperHalfSpacePoint_horizontal ‖a‖ (norm_pos_iff.mpr ha)).continuousAt.tendsto.comp hp

theorem affine_geometric_translation_injective (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : 1 < ‖c‖) : Function.Injective (fun n : ℕ => Mobius.affineMobius a (b/c^n) ha) := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h,norm_zero] at hc
    linarith
  intro m n hmn
  have h := congrArg (fun f : Mobius.complexMobiusGroup => f.val (0 : ℂ)) hmn
  rw [affineMobius_apply_coe,affineMobius_apply_coe] at h
  simp only [mul_zero,zero_add] at h
  have hd : b/c^m=b/c^n := OnePoint.coe_injective h
  have hm : b*c^n=b*c^m :=
    (div_eq_div_iff (pow_ne_zero _ hc0) (pow_ne_zero _ hc0)).mp hd
  have he : c^m=c^n := (mul_left_cancel₀ hb hm).symm
  have hn := congrArg (fun z : ℂ => ‖z‖) he
  simp only [norm_pow] at hn
  exact (pow_right_strictMono₀ hc).injective hn

theorem discontinuousMobius_no_geometric_affine_family (H : Subgroup Mobius.complexMobiusGroup)
    (hH : DiscreteGroups.Action.IsDiscontinuous H Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (a b c : ℂ) (ha :
      a ≠ 0) (hb : b ≠ 0)
    (hc : 1 < ‖c‖) (hmem : ∀ n : ℕ,Mobius.affineMobius a (b/c^n) ha ∈ H) : False := by
  let f (n : ℕ) : H := ⟨Mobius.affineMobius a (b/c^n) ha,hmem n⟩
  have hi : Function.Injective f := by
    intro m n h
    exact affine_geometric_translation_injective a b c ha hb hc (congrArg Subtype.val h)
  have ht := affine_geometric_translation_tendsto a b c ha hc
  exact hH.not_tendsto_orbit f hi
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ (Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint 0 ‖a‖
      (norm_pos_iff.mpr ha)) ht

theorem affineMobius_mul (a b c d : ℂ) (ha : a ≠ 0) (hc : c ≠ 0) :
    Mobius.affineMobius a b ha * Mobius.affineMobius c d hc =
      Mobius.affineMobius (a*c) (a*d+b) (mul_ne_zero ha hc) := by
  apply Subtype.ext
  ext z
  cases z using OnePoint.rec with
  | infty =>
    change (Mobius.affineMobius a b ha).val ((Mobius.affineMobius c d hc).val ∞) = _
    rw [affineMobius_apply_infty,affineMobius_apply_infty,affineMobius_apply_infty]
  | coe z =>
    change (Mobius.affineMobius a b ha).val ((Mobius.affineMobius c d hc).val z) = _
    rw [affineMobius_apply_coe,affineMobius_apply_coe,affineMobius_apply_coe]
    congr 1
    ring

theorem mobiusScaling_eq_affine (c : ℂˣ) :
    Mobius.mobiusScaling c = Mobius.affineMobius c 0 (Units.ne_zero c) := rfl

theorem mobiusScaling_pow (c : ℂˣ) (n : ℕ) :
    Mobius.mobiusScaling c ^ n = Mobius.mobiusScaling (c^n) := by
  induction n with
  | zero => simpa only [pow_zero] using mobiusScaling_one.symm
  | succ n ih => rw [pow_succ,ih,← mobiusScaling_mul,pow_succ]

theorem affineMobius_scaling_conjugate (a b : ℂ) (ha : a ≠ 0) (c : ℂˣ) (n : ℕ) :
    (Mobius.mobiusScaling c ^ n)⁻¹ * Mobius.affineMobius a b ha * (Mobius.mobiusScaling c ^ n) =
      Mobius.affineMobius a (b/(c:ℂ)^n) ha := by
  rw [mobiusScaling_pow,mobiusScaling_inv]
  simp_rw [mobiusScaling_eq_affine]
  rw [affineMobius_mul,affineMobius_mul]
  congr 1 <;> simp [Units.val_inv_eq_inv_val,Units.ne_zero,mul_comm,div_eq_mul_inv]

theorem discontinuousMobius_affine_shared_endpoints (H : Subgroup Mobius.complexMobiusGroup)
    (hH : DiscreteGroups.Action.IsDiscontinuous H Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (a b : ℂ) (ha : a
      ≠ 0) (c : ℂˣ)
    (hc : 1 < ‖(c:ℂ)‖) (hf : Mobius.affineMobius a b ha ∈ H) (hg : Mobius.mobiusScaling c ∈ H) :
    b = 0 := by
  by_contra hb
  apply discontinuousMobius_no_geometric_affine_family H hH a b c ha hb hc
  intro n
  rw [← affineMobius_scaling_conjugate a b ha c n]
  exact H.mul_mem (H.mul_mem (H.inv_mem (H.pow_mem hg n)) hf) (H.pow_mem hg n)

theorem isDiscontinuous_H3_subgroupConjugate (H : Subgroup Mobius.complexMobiusGroup)
    (hH : DiscreteGroups.Action.IsDiscontinuous H Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (u :
      Mobius.complexMobiusGroup) :
    DiscreteGroups.Action.IsDiscontinuous (DiscreteGroups.Action.Actions.subgroupConjugate u H)
      Hyperbolic.QuaternionHalfSpace.UpperHalfSpace := by
  apply DiscreteGroups.Action.IsDiscontinuous.transport
    (DiscreteGroups.Action.Actions.subgroupConjugateEquivalence u H).toEquiv
    (Mobius.mobiusPoincareHomeomorph u) _ hH
  intro g x
  change u • (g.val • x) = (u*g.val*u⁻¹) • (u • x)
  simp only [mul_smul,inv_smul_smul]

theorem mobiusScaling_loxodromic_norm_ne_one (c : ℂˣ)
    (hc : Mobius.MobiusLoxodromic (Mobius.mobiusScaling c)) : ‖(c:ℂ)‖ ≠ 1 := by
  by_cases h1 : (c:ℂ) = 1
  · have hunit : c = 1 := Units.ext h1
    exact False.elim (hc.1 (by rw [hunit,mobiusScaling_one]))
  · have he : Mobius.mobiusScaling c = Mobius.mobiusStandardElement c := by
      rw [Mobius.mobiusStandardElement_affine,ite_eq_right h1]
      rfl
    exact (Mobius.mobiusStandardElement_loxodromic_iff c).mp (he ▸ hc)

theorem discontinuousMobius_affine_shared_endpoints_of_norm_ne_one
    (H : Subgroup Mobius.complexMobiusGroup) (hH : DiscreteGroups.Action.IsDiscontinuous H
      Hyperbolic.QuaternionHalfSpace.UpperHalfSpace)
    (a b : ℂ) (ha : a ≠ 0) (c : ℂˣ) (hc : ‖(c:ℂ)‖ ≠ 1)
    (hf : Mobius.affineMobius a b ha ∈ H) (hg : Mobius.mobiusScaling c ∈ H) : b = 0 := by
  rcases lt_or_gt_of_ne hc with hc | hc
  · have hi : 1 < ‖((c⁻¹:ℂˣ):ℂ)‖ := by
      rw [Units.val_inv_eq_inv_val,norm_inv,one_lt_inv₀ (norm_pos_iff.mpr (Units.ne_zero c))]
      exact hc
    apply discontinuousMobius_affine_shared_endpoints H hH a b ha c⁻¹ hi hf
    rw [← mobiusScaling_inv]
    exact H.inv_mem hg
  · exact discontinuousMobius_affine_shared_endpoints H hH a b ha c hc hf hg

theorem discreteMobius_shared_loxodromic_endpoints (H : Subgroup Mobius.complexMobiusGroup)
    (hH : Mobius.IsDiscreteMobiusSubgroup H) (f g : Mobius.complexMobiusGroup) (hf : f ∈ H) (hg : g ∈ H)
    (hgL : Mobius.MobiusLoxodromic g) (a b : Mobius.ExtendedComplex) (hab : a ≠ b)
    (hga : g.val a = a) (hgb : g.val b = b) (hfa : f.val a = a) : f.val b = b := by
  obtain ⟨q,hqb,hqa⟩ := mobius_exists_send_pair_zero_infty b a hab.symm
  let K := DiscreteGroups.Action.Actions.subgroupConjugate q H
  let F := q*f*q⁻¹
  let G := q*g*q⁻¹
  have hK : DiscreteGroups.Action.IsDiscontinuous K Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
    isDiscontinuous_H3_subgroupConjugate H (discreteMobius_isDiscontinuous_H3 H hH) q
  have hFK : F ∈ K := ⟨f,hf,rfl⟩
  have hGK : G ∈ K := ⟨g,hg,rfl⟩
  have hFi : F.val ∞ = ∞ := by
    apply (Mobius.mobius_conjugate_boundary_fixed_iff f q ∞).mpr
    rw [← hqa,Equiv.symm_apply_apply]
    exact hfa
  have hGi : G.val ∞ = ∞ := by
    apply (Mobius.mobius_conjugate_boundary_fixed_iff g q ∞).mpr
    rw [← hqa,Equiv.symm_apply_apply]
    exact hga
  have hGz : G.val (0:ℂ) = (0:ℂ) := by
    apply (Mobius.mobius_conjugate_boundary_fixed_iff g q (0:ℂ)).mpr
    rw [← hqb,Equiv.symm_apply_apply]
    exact hgb
  obtain ⟨c,hc⟩ := Mobius.mobius_fix_zero_infty_eq_scaling G hGz hGi
  have hcL : Mobius.MobiusLoxodromic (Mobius.mobiusScaling c) :=
    hc ▸ Mobius.mobiusLoxodromic_conjugation_forward g q hgL
  obtain ⟨d,e,hF⟩ := Mobius.mobius_affine_of_fixes_infty F hFi
  change F = Mobius.affineMobius d e (Units.ne_zero d) at hF
  have he : e = 0 := discontinuousMobius_affine_shared_endpoints_of_norm_ne_one K hK
    d e (Units.ne_zero d) c (mobiusScaling_loxodromic_norm_ne_one c hcL)
      (hF ▸ hFK) (hc ▸ hGK)
  have hFz : F.val (0:ℂ) = (0:ℂ) := by
    rw [hF,affineMobius_apply_coe,he,mul_zero,zero_add]
  have hh := (Mobius.mobius_conjugate_boundary_fixed_iff f q (0:ℂ)).mp hFz
  rw [← hqb,Equiv.symm_apply_apply] at hh
  exact hh

theorem mobius_loxodromic_boundary_fixed_pair (g : Mobius.complexMobiusGroup)
    (hg : Mobius.MobiusLoxodromic g) :
    ∃ a b : Mobius.ExtendedComplex, a ≠ b ∧ ∀ z, g.val z = z ↔ z = a ∨ z = b := by
  rcases Mobius.mobius_nonidentity_fixedPoint_dichotomy g hg.1 with h | h
  · exact False.elim (hg.not_parabolic ⟨hg.1,h⟩)
  · exact h

/-- on the actual conformal boundary. -/
theorem not_discrete_of_loxodromic_unique_common_boundary_fixedPoint (f g : Mobius.complexMobiusGroup)
    (hg : Mobius.MobiusLoxodromic g) (hcommon : ∃! z : Mobius.ExtendedComplex, f.val z = z ∧ g.val z = z) :
    ¬Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure {f,g}) := by
  intro hH
  have hfmem : f ∈ Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup) :=
    Subgroup.subset_closure (by simp)
  have hgmem : g ∈ Subgroup.closure ({f,g} : Set Mobius.complexMobiusGroup) :=
    Subgroup.subset_closure (by simp)
  obtain ⟨z,hz,hunique⟩ := hcommon
  obtain ⟨a,b,hab,hfix⟩ := mobius_loxodromic_boundary_fixed_pair g hg
  rcases (hfix z).mp hz.2 with hza | hzb
  · subst z
    have hgb := (hfix b).mpr (Or.inr rfl)
    have hfb := discreteMobius_shared_loxodromic_endpoints _ hH f g hfmem hgmem hg a b hab
      hz.2 hgb hz.1
    exact hab (hunique b ⟨hfb,hgb⟩).symm
  · subst z
    have hga := (hfix a).mpr (Or.inl rfl)
    have hfa := discreteMobius_shared_loxodromic_endpoints _ hH f g hfmem hgmem hg b a hab.symm
      hz.2 hga hz.1
    exact hab (hunique a ⟨hfa,hga⟩)

theorem mobius_loxodromic_full_fixed_is_boundary (g : Mobius.complexMobiusGroup)
    (hg : Mobius.MobiusLoxodromic g) (w : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
    (hw : w ∈ Mobius.mobiusExtendedFixedPoints g) :
    ∃ z : Mobius.ExtendedComplex, Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding z = w ∧ g.val z = z := by
  obtain ⟨a,b,hab,hfix⟩ := mobius_loxodromic_boundary_fixed_pair g hg
  have ha := (Mobius.mobiusExtendedFixedPoints_boundary_iff g a).mpr ((hfix a).mpr (Or.inl rfl))
  have hb := (Mobius.mobiusExtendedFixedPoints_boundary_iff g b).mpr ((hfix b).mpr (Or.inr rfl))
  have he : Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding a ≠
    Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding b :=
    fun h => hab (Hyperbolic.QuaternionHalfSpace.injective_extendedBoundaryEmbedding h)
  obtain ⟨u,v,_,hfull⟩ := hg.2
  rcases (hfull _).mp ha with hau | hav <;> rcases (hfull _).mp hb with hbu | hbv
  · exact False.elim (he (hau.trans hbu.symm))
  · rcases (hfull w).mp hw with hwu | hwv
    · exact ⟨a,hau.trans hwu.symm,(hfix a).mpr (Or.inl rfl)⟩
    · exact ⟨b,hbv.trans hwv.symm,(hfix b).mpr (Or.inr rfl)⟩
  · rcases (hfull w).mp hw with hwu | hwv
    · exact ⟨b,hbu.trans hwu.symm,(hfix b).mpr (Or.inr rfl)⟩
    · exact ⟨a,hav.trans hwv.symm,(hfix a).mpr (Or.inl rfl)⟩
  · exact False.elim (he (hav.trans hbv.symm))

/-- Using the full compactified three-space fixed sets. -/
theorem not_discrete_of_loxodromic_unique_common_extended_fixedPoint (f g : Mobius.complexMobiusGroup) (hg :
    Mobius.MobiusLoxodromic g)
    (hcommon : ∃! w : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace,
      w ∈ Mobius.mobiusExtendedFixedPoints f ∧ w ∈ Mobius.mobiusExtendedFixedPoints g) :
    ¬Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure {f,g}) := by
  apply not_discrete_of_loxodromic_unique_common_boundary_fixedPoint f g hg
  obtain ⟨w,hw,hunique⟩ := hcommon
  obtain ⟨z,hz,hgz⟩ := mobius_loxodromic_full_fixed_is_boundary g hg w hw.2
  refine ⟨z,⟨?_,hgz⟩,?_⟩
  · apply (Mobius.mobiusExtendedFixedPoints_boundary_iff f z).mp
    rw [hz]
    exact hw.1
  · intro y hy
    apply Hyperbolic.QuaternionHalfSpace.injective_extendedBoundaryEmbedding
    exact (hunique (Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding y)
      ⟨(Mobius.mobiusExtendedFixedPoints_boundary_iff f y).mpr hy.1,
        (Mobius.mobiusExtendedFixedPoints_boundary_iff g y).mpr hy.2⟩).trans hz.symm

end LowDimensionalTopology.Geometry.DiscreteGroups
