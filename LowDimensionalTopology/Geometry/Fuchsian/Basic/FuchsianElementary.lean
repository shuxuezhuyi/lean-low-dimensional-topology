/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianFiniteGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Packing.ElementaryPacking
@[expose] public section
noncomputable section
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A norm-one multiplier fixes a genuine interior point. -/
theorem scaling_fixJ_of_norm_one (a : ℂˣ) (ha : ‖(a:ℂ)‖=1) :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a • _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ=_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_eq_affine,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.affineMobius_smul_j]
  apply Subtype.ext
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 ‖(a:ℂ)‖=_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 1
  rw [ha]

/-- The actual reciprocal fixes the same interior point. -/
theorem reciprocal_fixJ : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal • _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ=_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  have h := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_axis_smul 1 zero_lt_one
  have hp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint 0 1 zero_lt_one=_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
    apply Subtype.ext
    rfl
  simpa only [hp,inv_one] using h

/-- A hyperbolic scaling has an actually positive real multiplier. -/
theorem hyperbolic_scaling_positive (a : ℂˣ) (ha : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
  (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a)) :
    (a:ℂ).im=0 ∧ 0<(a:ℂ).re := by
  have hnorm := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_loxodromic_norm_ne_one a ha.1
  have ha1 : (a:ℂ)≠1 := fun he => hnorm (he ▸ norm_one)
  obtain ⟨q,k,hki,hkp,_,hq⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugate_positive_standard ha
  have htrace := congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace hq
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_conjugation,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_eq_standard a ha1,
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_squaredTrace,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_squaredTrace] at htrace
  rcases (_root_.LowDimensionalTopology.Geometry.Mobius.Classification.standardTrace_eq_iff a
    k).mp htrace with rfl | rfl
  · exact ⟨hki,hkp⟩
  · simp only [Units.val_inv_eq_inv_val,Complex.inv_im,Complex.inv_re]
    exact ⟨by simp only [hki,neg_zero,zero_div],div_pos hkp (Complex.normSq_pos.mpr k.ne_zero)⟩


/-- Conjugate common fixed points recover a common fixed point in the original group. -/
theorem FuchsianDisc.conjugate_common_fixed_isCyclic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (u : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hz : ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H, f.val z=z) : IsCyclic H := by
  apply D.common_fixed_isCyclic (u⁻¹•z)
  intro f hf
  have h := hz (u*f*u⁻¹) ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff u H _).mpr ⟨f,hf,rfl⟩)
  change (u*f*u⁻¹)•z=z at h
  apply MulAction.injective u
  change u•(f•(u⁻¹•z))=u•(u⁻¹•z)
  simpa only [mul_smul,smul_inv_smul] using h

/-- A genuine Fuchsian endpoint-pair group has a positive real infinite multiplier,
with no residual rotations in the endpoint kernel. -/
theorem FuchsianDisc.invariant_pair_normal_form {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (a b : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hab : a≠b)
    (hp : ∀ f : H, f.val.val '' {a,b}={a,b}) :
    IsCyclic H ∨ ∃ u : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, ∃ c : ℂˣ,
      (c:ℂ).im=0 ∧ 0<(c:ℂ).re ∧ ‖(c:ℂ)‖≠1 ∧
      ∀ f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H ↔
        ∃ n : ℤ, f=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (c^n) ∨ f=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (c^n)*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal := by
  by_cases hcyc : IsCyclic H
  · exact Or.inl hcyc
  · right
    obtain ⟨u,w,c,q,hq,hwn,_,hcases⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_invariant_pair_normal_forms H D.discrete a b hab hp
    let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H
    obtain ⟨B,hB,hpres⟩ := invariantDisc_conjugate H u ⟨D.carrier,D.isDisc,D.image_eq⟩
    have hdK : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K := by
      let : DiscreteTopology H := D.discrete
      exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete u H
    rcases hcases with hfix | ⟨_,hform⟩
    · exact False.elim (hcyc (D.conjugate_common_fixed_isCyclic u (0:ℂ) (by
        intro f hf
        obtain ⟨k,n,rfl⟩ := (hfix f).mp hf
        exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero _)))
    · have hcK : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c ∈ K := (hform _).mpr ⟨⟨0,hq⟩,1,Or.inl (by simp)⟩
      have hcn : ‖(c:ℂ)‖≠1 := by
        intro hc
        have hfixJ : ∀ f ∈ K, f•_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ=_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
          intro f hf
          obtain ⟨k,n,hf⟩ := (hform f).mp hf
          have hcoef : ‖((w^(k:ℕ)*c^n:ℂˣ):ℂ)‖=1 := by
            simp only [Units.val_mul,Units.val_pow_eq_pow_val,Units.val_zpow_eq_zpow_val,
              norm_mul,norm_pow,norm_zpow,hwn,hc,one_pow,one_zpow,mul_one]
          rcases hf with rfl | rfl
          · exact scaling_fixJ_of_norm_one _ hcoef
          · rw [mul_smul,reciprocal_fixJ,scaling_fixJ_of_norm_one _ hcoef]
        let : Finite K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_finite_of_common_H3_fixed K hdK _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ hfixJ
        let : IsCyclic K := finiteMobius_preserves_disc_isCyclic K hB hpres
        exact hcyc (isCyclic_of_injective
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence u
          H).toMonoidHom
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence u
            H).injective)
      have hc1 : (c:ℂ)≠1 := fun he => hcn (he ▸ norm_one)
      have hcL : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c) := by
        rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_eq_standard c hc1]
        exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_loxodromic_iff c).mpr hcn
      have hcH : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c) := ⟨hcL,B,hB,hpres ⟨_,hcK⟩⟩
      obtain ⟨hci,hcp⟩ := hyperbolic_scaling_positive c hcH
      have hzero : ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ frontier B :=
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c) hcH hB (hpres ⟨_,hcK⟩)
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero c)
      have hwk (k : Fin q) : w^(k:ℕ)=1 := by
        by_contra hk
        have hk1 : ((w^(k:ℕ):ℂˣ):ℂ)≠1 := fun he => hk (Units.ext he)
        have hkK : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (w^(k:ℕ)) ∈ K :=
          (hform _).mpr ⟨k,0,Or.inl (by simp)⟩
        have hkE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (w^(k:ℕ))) := by
          rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_eq_standard _ hk1]
          exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_isElliptic _ hk1 (by simp [hwn])
        exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_fixed_not_mem_disc_frontier _ hkE hB (hpres
          ⟨_,hkK⟩)
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero _) hzero
      refine ⟨u,c,hci,hcp,hcn,?_⟩
      intro f
      constructor
      · intro hf
        obtain ⟨k,n,hf⟩ := (hform f).mp hf
        refine ⟨n,?_⟩
        simpa only [hwk k,one_mul] using hf
      · rintro ⟨n,hf⟩
        apply (hform f).mpr
        exact ⟨⟨0,hq⟩,n,by simpa using hf⟩


/-- A positive real nontrivial generator can be chosen greater than one. -/
theorem positive_multiplier_above_one (c : ℂˣ) (hi : (c:ℂ).im=0)
    (hp : 0<(c:ℂ).re) (hn : ‖(c:ℂ)‖≠1) :
    ∃ d : ℂˣ, (d:ℂ).im=0 ∧ 1<(d:ℂ).re ∧ (d=c ∨ d=c⁻¹) := by
  have hnorm : ‖(c:ℂ)‖=(c:ℂ).re :=
    (Complex.abs_re_eq_norm.mpr hi).symm.trans (abs_of_pos hp)
  by_cases hbig : 1<(c:ℂ).re
  · exact ⟨c,hi,hbig,Or.inl rfl⟩
  · have hsmall : (c:ℂ).re<1 := lt_of_le_of_ne (le_of_not_gt hbig)
      (fun he => hn (hnorm.trans he))
    have hr : (c:ℂ)=((c:ℂ).re:ℂ) := Complex.ext rfl hi
    have hv := congrArg (fun z : ℂ => z⁻¹) hr
    rw [←Complex.ofReal_inv] at hv
    refine ⟨c⁻¹,?_,?_,Or.inr rfl⟩
    · rw [Units.val_inv_eq_inv_val,hv,Complex.ofReal_im]
    · rw [Units.val_inv_eq_inv_val,hv,Complex.ofReal_re]
      exact (one_lt_inv₀ hp).mpr hsmall

/-- The actual two-generator subgroup described by the exact endpoint normal form. -/
theorem scaling_reciprocal_normal_form_eq_closure (K : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (c : ℂˣ) (hform : ∀ f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, f ∈ K ↔
      ∃ n : ℤ, f=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (c^n) ∨ f=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (c^n)*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal) :
    K=Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal} := by
  apply le_antisymm
  · intro f hf
    obtain ⟨n,hf⟩ := (hform f).mp hf
    have hc : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c ∈ Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal} :=
      Subgroup.subset_closure (by simp)
    have hr : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal ∈ Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal} :=
      Subgroup.subset_closure (by simp)
    have hpow : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (c^n) ∈ Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal} := by
      change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom (c^n) ∈ _
      rw [map_zpow]
      exact Subgroup.zpow_mem _ hc n
    rcases hf with rfl | rfl
    · exact hpow
    · exact Subgroup.mul_mem _ hpow hr
  · apply (Subgroup.closure_le _).mpr
    intro f hf
    rcases (Set.mem_insert_iff.mp hf) with rfl | hf
    · exact (hform _).mpr ⟨1,Or.inl (by simp)⟩
    · have he : f=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal := Set.mem_singleton_iff.mp hf
      subst f
      exact (hform _).mpr ⟨0,Or.inr (by simp [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_one])⟩

/-- Inverting one generator does not change the actual generated subgroup. -/
theorem closure_pair_inv_first {G : Type*} [Group G] (g h : G) :
    Subgroup.closure {g⁻¹,h}=Subgroup.closure {g,h} := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · rw [Set.mem_singleton_iff.mp hx]
      exact Subgroup.subset_closure (by simp)
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]
      have hi : g⁻¹ ∈ Subgroup.closure {g⁻¹,h} := Subgroup.subset_closure (by simp)
      change g ∈ Subgroup.closure {g⁻¹,h}
      exact (Subgroup.inv_mem_iff _).mp hi
    · rw [Set.mem_singleton_iff.mp hx]
      exact Subgroup.subset_closure (by simp)

/-- Rotation of coordinates by i is an actual geometric Mobius map. -/
def fuchsianQuarterRotation : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Units.mk0 Complex.I Complex.I_ne_zero)

/-- The actual formulation involution is minus reciprocal. -/
def fuchsianDihedralFlip : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal

theorem fuchsianDihedralFlip_coe (z : ℂ) (hz : z≠0) :
    fuchsianDihedralFlip.val z=((-1/z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  rw [fuchsianDihedralFlip,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mul_reciprocal_coe _ z
    hz]
  simp only [Units.val_neg,Units.val_one]

theorem fuchsianQuarterRotation_scaling (c : ℂˣ) :
    fuchsianQuarterRotation*_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c*fuchsianQuarterRotation⁻¹=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c := by
  rw [fuchsianQuarterRotation,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_inv,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mul,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mul]
  congr 1
  rw [mul_comm (Units.mk0 Complex.I Complex.I_ne_zero) c,mul_assoc,mul_inv_cancel,mul_one]

theorem fuchsianQuarterRotation_reciprocal :
    fuchsianQuarterRotation*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal*fuchsianQuarterRotation⁻¹=fuchsianDihedralFlip := by
  rw [fuchsianQuarterRotation,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_inv,mul_assoc,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_mul_scaling,
    inv_inv,←mul_assoc,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mul]
  have hI : Units.mk0 Complex.I Complex.I_ne_zero * Units.mk0 Complex.I Complex.I_ne_zero=(-1:ℂˣ) := by
    apply Units.ext
    simp only [Units.val_mul,Units.val_mk0,Complex.I_mul_I,Units.val_neg,Units.val_one]
  rw [hI]
  rfl


/-- Actual subgroup conjugation transports the actual two generators. -/
theorem conjugate_closure_pair (u g h : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u (Subgroup.closure {g,h})=
      Subgroup.closure {u*g*u⁻¹,u*h*u⁻¹} := by
  change (Subgroup.closure {g,h}).map (MulAut.conj u).toMonoidHom=_
  rw [MonoidHom.map_closure,Set.image_pair]
  rfl

/--
The endpoint-pair classification in the precise formulation coordinates and with the
infinite positive dilation generator chosen greater than one.
-/
theorem FuchsianDisc.invariant_pair_book_form {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (a b : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hab : a≠b)
    (hp : ∀ f : H, f.val.val '' {a,b}={a,b}) :
    IsCyclic H ∨ ∃ u : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, ∃ d : ℂˣ,
      (d:ℂ).im=0 ∧ 1<(d:ℂ).re ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H=
        Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d,fuchsianDihedralFlip} := by
  rcases D.invariant_pair_normal_form a b hab hp with hcyc | ⟨u,c,hci,hcp,hcn,hform⟩
  · exact Or.inl hcyc
  · right
    obtain ⟨d,hdi,hdb,hd⟩ := positive_multiplier_above_one c hci hcp hcn
    have hgen : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H=Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal} :=
      scaling_reciprocal_normal_form_eq_closure _ c hform
    have hrot : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (fuchsianQuarterRotation*u) H=
        Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling c,fuchsianDihedralFlip} := by
      rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose,hgen,conjugate_closure_pair,
        fuchsianQuarterRotation_scaling,fuchsianQuarterRotation_reciprocal]
    refine ⟨fuchsianQuarterRotation*u,d,hdi,hdb,?_⟩
    rcases hd with rfl | rfl
    · exact hrot
    · rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_inv,closure_pair_inv_first]
      exact hrot

/-- The complete elementary Fuchsian classification, including all finite and
common-fixed-point branches, without an invariant-pair hypothesis. -/
theorem FuchsianDisc.elementary_classification {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) :
    IsCyclic H ∨ ∃ u : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, ∃ d : ℂˣ,
      (d:ℂ).im=0 ∧ 1<(d:ℂ).re ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H=
        Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d,fuchsianDihedralFlip} := by
  by_cases hf : Finite H
  · let : Finite H := hf
    exact Or.inl (finiteMobius_preserves_disc_isCyclic H D.isDisc D.image_eq)
  · let : Infinite H := not_finite_iff_infinite.mp hf
    rcases (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.infinite_isElementary_iff_interior_or_fixed_or_pair
      H).mp he with hinner | hfix | hpair
    · obtain ⟨p,hp⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.hasTypeOneOrbit_iff_common_H3_fixed
      H).mp (Or.inl hinner)
      exact False.elim (hf
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_finite_of_common_H3_fixed H D.discrete p
        hp))
    · obtain ⟨z,hz⟩ := hfix
      exact Or.inl (D.common_fixed_isCyclic z (fun f hf => hz ⟨f,hf⟩))
    · obtain ⟨a,b,hab,hpair⟩ := hpair
      exact D.invariant_pair_book_form a b hab hpair


/-- The actual real positive dilation, with its literal action on the full sphere. -/
def fuchsianPositiveDilation (k : ℝ) (hk : 0<k) : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Units.mk0 (k:ℂ) (Complex.ofReal_ne_zero.mpr hk.ne'))

theorem fuchsianPositiveDilation_coe (k : ℝ) (hk : 0<k) (z : ℂ) :
    (fuchsianPositiveDilation k hk).val z=(((k:ℂ)*z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  rw [fuchsianPositiveDilation,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe]
  rfl

/-- The classification with a literal real parameter k greater than one. -/
theorem FuchsianDisc.elementary_real_classification {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) :
    IsCyclic H ∨ ∃ u : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, ∃ k : ℝ, ∃ hk : 1<k,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H=Subgroup.closure
        {fuchsianPositiveDilation k (lt_trans zero_lt_one hk),fuchsianDihedralFlip} := by
  rcases D.elementary_classification he with hcyc | ⟨u,d,hdi,hdb,hgen⟩
  · exact Or.inl hcyc
  · right
    refine ⟨u,(d:ℂ).re,hdb,?_⟩
    have hd : d=Units.mk0 ((d:ℂ).re:ℂ)
        (Complex.ofReal_ne_zero.mpr (lt_trans zero_lt_one hdb).ne') := by
      apply Units.ext
      exact Complex.ext rfl hdi
    rw [fuchsianPositiveDilation,←hd]
    exact hgen

/--
Every elementary Fuchsian group is cyclic or has exactly
the actual generators z maps to k*z, k greater than one, and z maps to -1/z.
-/
theorem fuchsianGroup_elementary_classification (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : _root_.LowDimensionalTopology.Geometry.Surfaces.IsFuchsianGroup H) (he :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) :
    IsCyclic H ∨ ∃ u : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, ∃ k : ℝ, ∃ hk : 1<k,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H=Subgroup.closure
        {fuchsianPositiveDilation k (lt_trans zero_lt_one hk),fuchsianDihedralFlip} := by
  obtain ⟨D⟩ := (fuchsianDisc_exists_iff H).mpr hH
  exact D.elementary_real_classification he

end LowDimensionalTopology.Geometry.Fuchsian
