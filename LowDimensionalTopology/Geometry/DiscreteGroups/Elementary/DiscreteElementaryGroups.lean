/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FiniteOrbit
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.AffineDiscreteGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.TypeOneGroups
@[expose] public section
noncomputable section
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem parabolic_positive_periodic_boundary_fixed (f : Mobius.complexMobiusGroup)
    (hf : Mobius.MobiusParabolic f) (z : Mobius.ExtendedComplex) (n : ℕ) (hn : 0 < n)
    (hz : (f^n).val z=z) : f.val z=z := by
  have hc := (Mobius.mobiusBoundaryParabolic_iff_conjugate_translation f hf.1).mp hf
  obtain ⟨q,rfl⟩ := isConj_iff.mp hc.symm
  have ht : ((Mobius.mobiusStandardElement 1)^n).val (q.val.symm z) = q.val.symm z := by
    have he := congrArg q.val.symm hz
    simp only [Mobius.mobius_iterates_conjugation,Equiv.symm_apply_apply] at he
    change ((Mobius.mobiusStandardElement 1)^n).val (q.val.symm z) = q.val.symm z at he
    exact he
  have hi : q.val.symm z = ∞ := by
    cases hq : q.val.symm z using OnePoint.rec with
    | infty => rfl
    | coe w =>
      rw [hq,Mobius.mobiusStandardElement_pow_coe] at ht
      simp only [Units.val_one,ite_true,OnePoint.coe_eq_coe] at ht
      have hzero : (n:ℂ)=0 := add_left_cancel (show w+(n:ℂ)=w+0 by simpa using ht)
      exact False.elim (hn.ne' (Nat.cast_eq_zero.mp hzero))
  change q.val ((Mobius.mobiusStandardElement 1).val (q.val.symm z)) = z
  rw [hi,Mobius.mobiusStandardElement_infty]
  exact q.val.eq_symm_apply.mp hi.symm

theorem elementary_parabolic_common_fixedPoint (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsElementary H) (f : Mobius.complexMobiusGroup) (hfH : f ∈ H) (hf : Mobius.MobiusParabolic f) :
    ∃ a : Mobius.ExtendedComplex, (∀ z, f.val z=z ↔ z=a) ∧ ∀ g : H, g.val.val a=a := by
  obtain ⟨a,ha⟩ := hf.2
  have hb : MobiusBoundaryFiniteOrbit H := by
    rcases (isElementary_iff_boundary_or_interior H).mp hH with h | ⟨q,hq⟩
    · exact h
    · exact False.elim ((finite_H3_orbit_all_elliptic H q hq f hfH hf.1).not_parabolic hf)
  obtain ⟨z,hz⟩ := hb
  obtain ⟨n,hn,hfix⟩ := DiscreteGroups.Action.exists_positive_power_fixing_finite_orbit z hz (⟨f,hfH⟩ : H)
  have hza (y : Mobius.ExtendedComplex) (hy : y ∈ MulAction.orbit H z) : y=a := by
    apply (ha y).mp
    apply parabolic_positive_periodic_boundary_fixed f hf y n hn
    have hh := hfix y hy
    change (f^n).val y=y at hh
    exact hh
  have hz0 := hza z (MulAction.mem_orbit_self z)
  refine ⟨a,ha,?_⟩
  intro g
  have hg := hza (g • z) (MulAction.mem_orbit z g)
  rw [hz0] at hg
  change g.val.val a=a at hg
  exact hg

theorem discrete_elementary_parabolic_no_loxodromic (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (hH : IsElementary H) (f : Mobius.complexMobiusGroup)
    (hfH : f ∈ H) (hf : Mobius.MobiusParabolic f) : ∀ g ∈ H, ¬Mobius.MobiusLoxodromic g := by
  obtain ⟨a,ha,hall⟩ := elementary_parabolic_common_fixedPoint H hH f hfH hf
  intro g hg hgL
  obtain ⟨b,c,hbc,hfix⟩ := mobius_loxodromic_boundary_fixed_pair g hgL
  have hga : g.val a=a := hall ⟨g,hg⟩
  have hfa : f.val a=a := (ha a).mpr rfl
  rcases (hfix a).mp hga with hab | hac
  · subst b
    have hgc := (hfix c).mpr (Or.inr rfl)
    have hfc := discreteMobius_shared_loxodromic_endpoints H hD f g hfH hg hgL a c hbc hga hgc hfa
    exact hbc ((ha c).mp hfc).symm
  · subst c
    have hgb := (hfix b).mpr (Or.inl rfl)
    have hfb := discreteMobius_shared_loxodromic_endpoints H hD f g hfH hg hgL a b hbc.symm hga hgb hfa
    exact hbc ((ha b).mp hfb)

theorem finite_boundary_orbit_fixed_by_loxodromic (H : Subgroup Mobius.complexMobiusGroup)
    (g : Mobius.complexMobiusGroup) (hgH : g ∈ H) (hg : Mobius.MobiusLoxodromic g)
    (z : Mobius.ExtendedComplex) (hz : (MulAction.orbit H z).Finite) : g.val z=z := by
  by_contra hn
  have hi := Mobius.mobius_loxodromic_orbit_injective g hg z hn
  apply (hz.subset ?_).not_infinite (Set.infinite_range_of_injective hi)
  rintro _ ⟨n,rfl⟩
  exact ⟨⟨g^n,H.zpow_mem hgH n⟩,rfl⟩

theorem elementary_loxodromic_boundary_finite_orbit (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsElementary H) (g : Mobius.complexMobiusGroup) (hgH : g ∈ H)
    (hg : Mobius.MobiusLoxodromic g) : MobiusBoundaryFiniteOrbit H := by
  rcases (isElementary_iff_boundary_or_interior H).mp hH with h | ⟨q,hq⟩
  · exact h
  · exact False.elim (hg.not_elliptic (finite_H3_orbit_all_elliptic H q hq g hgH hg.1))

theorem discrete_elementary_loxodromic_fixed_pair (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (hH : IsElementary H) (g : Mobius.complexMobiusGroup)
    (hgH : g ∈ H) (hg : Mobius.MobiusLoxodromic g) :
    ∃ a b : Mobius.ExtendedComplex, a ≠ b ∧ g.val a=a ∧ g.val b=b ∧
      ∀ f : H, f.val.val '' ({a,b} : Set Mobius.ExtendedComplex) = {a,b} := by
  obtain ⟨z,hz⟩ := elementary_loxodromic_boundary_finite_orbit H hH g hgH hg
  obtain ⟨a,b,hab,hfix⟩ := mobius_loxodromic_boundary_fixed_pair g hg
  have hsub : MulAction.orbit H z ⊆ ({a,b} : Set Mobius.ExtendedComplex) := by
    intro y hy
    apply (hfix y).mp
    exact finite_boundary_orbit_fixed_by_loxodromic H g hgH hg y
      ((MulAction.orbit_eq_iff.mpr hy).symm ▸ hz)
  have hcard : (MulAction.orbit H z).ncard ≤ 2 := by
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (by simp [hab])
  rcases DiscreteGroups.Action.finite_orbit_singleton_or_pair z hz hcard with ⟨_,hall⟩ | ⟨u,v,huv,heq,hpres⟩
  · have hgz : g.val z=z := hall ⟨g,hgH⟩
    have hgeneral (w : Mobius.ExtendedComplex) (hzw : z≠w) (hgw : g.val w=w) :
        ∀ f : H, f.val.val '' ({z,w} : Set Mobius.ExtendedComplex) = {z,w} := by
      intro f
      have hfz : f.val.val z=z := hall f
      have hfw := discreteMobius_shared_loxodromic_endpoints H hD f.val g f.property hgH hg
        z w hzw hgz hgw hfz
      simp only [Set.image_pair,hfz,hfw]
    rcases (hfix z).mp hgz with hza | hzb
    · subst z
      exact ⟨a,b,hab,hgz,(hfix b).mpr (Or.inr rfl),hgeneral b hab ((hfix b).mpr (Or.inr rfl))⟩
    · subst z
      exact ⟨b,a,hab.symm,hgz,(hfix a).mpr (Or.inl rfl),hgeneral a hab.symm ((hfix a).mpr (Or.inl rfl))⟩
  · have hu : g.val u=u := by
      apply finite_boundary_orbit_fixed_by_loxodromic H g hgH hg u
      exact (MulAction.orbit_eq_iff.mpr (show u ∈ MulAction.orbit H z by rw [heq]; simp)).symm ▸ hz
    have hv : g.val v=v := by
      apply finite_boundary_orbit_fixed_by_loxodromic H g hgH hg v
      exact (MulAction.orbit_eq_iff.mpr (show v ∈ MulAction.orbit H z by rw [heq]; simp)).symm ▸ hz
    exact ⟨u,v,huv,hu,hv,hpres⟩

theorem elementary_parabolic_hasTypeTwoBoundaryOrbit (H : Subgroup Mobius.complexMobiusGroup)
    (hH : IsElementary H) (f : Mobius.complexMobiusGroup) (hfH : f ∈ H) (hf : Mobius.MobiusParabolic f) :
    HasTypeTwoBoundaryOrbit H := by
  obtain ⟨a,_,hall⟩ := elementary_parabolic_common_fixedPoint H hH f hfH hf
  apply (hasTypeTwoBoundaryOrbit_iff H).mpr
  exact ⟨a,hall⟩

theorem invariant_pair_hasTypeTwo_or_Three (H : Subgroup Mobius.complexMobiusGroup)
    (a b : Mobius.ExtendedComplex) (hab : a≠b)
    (hpair : ∀ f : H,f.val.val '' ({a,b} : Set Mobius.ExtendedComplex) = {a,b}) :
    HasTypeTwoBoundaryOrbit H ∨ HasTypeThreeBoundaryOrbit H := by
  have hsub : MulAction.orbit H a ⊆ ({a,b} : Set Mobius.ExtendedComplex) := by
    rintro _ ⟨f,rfl⟩
    rw [← hpair f]
    exact ⟨a,by simp,rfl⟩
  have hfin := (Set.toFinite ({a,b} : Set Mobius.ExtendedComplex)).subset hsub
  have hcard : (MulAction.orbit H a).ncard ≤ 2 := by
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (by simp [hab])
  rcases DiscreteGroups.Action.finite_orbit_singleton_or_pair a hfin hcard with ⟨heq,_⟩ | ⟨u,v,huv,heq,_⟩
  · exact Or.inl ⟨a,heq⟩
  · exact Or.inr ⟨a,hfin,by rw [heq]; simp [huv]⟩

theorem discrete_elementary_loxodromic_structure (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.IsDiscreteMobiusSubgroup H) (hH : IsElementary H) (g : Mobius.complexMobiusGroup)
    (hgH : g ∈ H) (hg : Mobius.MobiusLoxodromic g) :
    (HasTypeTwoBoundaryOrbit H ∨ HasTypeThreeBoundaryOrbit H) ∧
      ∀ f ∈ H, ¬Mobius.MobiusParabolic f := by
  obtain ⟨a,b,hab,_,_,hpair⟩ := discrete_elementary_loxodromic_fixed_pair H hD hH g hgH hg
  refine ⟨invariant_pair_hasTypeTwo_or_Three H a b hab hpair,?_⟩
  intro f hf hp
  exact discrete_elementary_parabolic_no_loxodromic H hD hH f hf hp g hgH hg

end LowDimensionalTopology.Geometry.DiscreteGroups
