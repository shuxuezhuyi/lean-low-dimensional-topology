/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FiniteOrbit
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteMobiusVertices
public import Mathlib.RingTheory.IntegralDomain

@[expose] public section
noncomputable section
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem finiteMobius_two_orbits_vertex_card (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (hm : Nat.card (MobiusVertexOrbit H) = 2) : Nat.card (MobiusVertex H) = 2 := by
  have hb := finiteMobius_vertex_burnside H
  have hh : 0 < Nat.card H := Nat.card_pos
  rw [hm] at hb
  omega

theorem finiteMobius_two_vertices_fixed (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (hv : Nat.card (MobiusVertex H) = 2) (g : H) (z : MobiusVertex H) : g • z = z := by
  by_cases hg : g = 1
  · subst g
    exact one_smul H z
  · have hc := finiteMobius_vertex_fixedBy_card H g hg
    have he : MulAction.fixedBy (MobiusVertex H) g = univ :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by
        rw [Set.ncard_univ, hv]
        exact hc.ge)
    have hz : z ∈ MulAction.fixedBy (MobiusVertex H) g := by
      rw [he]
      exact Set.mem_univ z
    exact hz

theorem finiteMobius_two_orbits_stabilizer_eq_top (H : Subgroup Mobius.complexMobiusGroup)
    [Finite H] (hm : Nat.card (MobiusVertexOrbit H) = 2) (z : MobiusVertex H) :
    MulAction.stabilizer H z = ⊤ := by
  ext g
  constructor
  · intro _
    exact Subgroup.mem_top g
  · intro _
    exact finiteMobius_two_vertices_fixed H (finiteMobius_two_orbits_vertex_card H hm) g z

theorem finiteMobius_two_orbits_stabilizer_card (H : Subgroup Mobius.complexMobiusGroup)
    [Finite H] (hm : Nat.card (MobiusVertexOrbit H) = 2) (z : MobiusVertex H) :
    Nat.card (MulAction.stabilizer H z) = Nat.card H := by
  rw [finiteMobius_two_orbits_stabilizer_eq_top H hm z]
  exact Nat.card_congr Subgroup.topEquiv.toEquiv

theorem finiteMobius_two_orbits_orbit_card (H : Subgroup Mobius.complexMobiusGroup)
    [Finite H] (hm : Nat.card (MobiusVertexOrbit H) = 2) (z : MobiusVertex H) :
    Nat.card (MulAction.orbit H z) = 1 := by
  have he : MulAction.orbit H z = {z} :=
    DiscreteGroups.Action.orbit_eq_singleton_of_fixed z
      (fun g => finiteMobius_two_vertices_fixed H (finiteMobius_two_orbits_vertex_card H hm) g z)
  change (MulAction.orbit H z).ncard = 1
  rw [he,Set.ncard_singleton]

theorem mobiusAffineConstant_zero_of_fix_zero (f : Mobius.mobiusInftyStabilizer)
    (hz : f.val.val (0 : ℂ) = (0 : ℂ)) : Mobius.mobiusAffineConstant f = 0 := by
  rw [Mobius.mobius_affine_formula] at hz
  exact OnePoint.coe_injective (by simpa only [mul_zero,zero_add] using hz)

theorem subgroupMultiplierHom_injective_of_fix_zero (H : Subgroup Mobius.complexMobiusGroup)
    (hi : H ≤ Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H,f.val (0 : ℂ) = (0 : ℂ)) :
    Function.Injective (Mobius.subgroupMultiplierHom H hi) := by
  intro f g hfg
  let fi : Mobius.mobiusInftyStabilizer := ⟨f.val,hi f.property⟩
  let gi : Mobius.mobiusInftyStabilizer := ⟨g.val,hi g.property⟩
  have hfi : Mobius.mobiusAffineConstant fi = 0 := mobiusAffineConstant_zero_of_fix_zero fi (hz _ f.property)
  have hgi : Mobius.mobiusAffineConstant gi = 0 := mobiusAffineConstant_zero_of_fix_zero gi (hz _ g.property)
  change Mobius.mobiusMultiplier fi = Mobius.mobiusMultiplier gi at hfg
  apply Subtype.ext
  calc
    f.val = Mobius.mobiusMatrixProjection (Mobius.Classification.affineMatrix (Mobius.mobiusMultiplier fi)
      (Mobius.mobiusAffineConstant fi)) := Mobius.mobius_affine_representation fi
    _ = Mobius.mobiusMatrixProjection (Mobius.Classification.affineMatrix (Mobius.mobiusMultiplier gi)
      (Mobius.mobiusAffineConstant gi)) := by rw [hfg,hfi,hgi]
    _ = g.val := (Mobius.mobius_affine_representation gi).symm

theorem finiteMobius_fix_zero_infty_isCyclic (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (hi : H ≤ Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H,f.val (0 : ℂ) = (0 : ℂ)) :
    IsCyclic H :=
  isCyclic_of_injective_ringHom ((Units.coeHom ℂ).comp (Mobius.subgroupMultiplierHom H hi))
    (Units.val_injective.comp (subgroupMultiplierHom_injective_of_fix_zero H hi hz))

theorem finiteMobius_multiplier_unit_norm (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (hi : H ≤ Mobius.mobiusInftyStabilizer) (g : H) :
    ‖((Mobius.subgroupMultiplierHom H hi g : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n,hn,hpow⟩ := (isOfFinOrder_of_finite g).exists_pow_eq_one
  have hp := congrArg (fun f => ((Mobius.subgroupMultiplierHom H hi f : ℂˣ) : ℂ)) hpow
  simp only [map_pow,map_one,Units.val_pow_eq_pow_val,Units.val_one] at hp
  have hnrm := congrArg (fun z : ℂ => ‖z‖) hp
  rw [norm_pow,norm_one] at hnrm
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp hnrm

theorem finiteMobius_fix_zero_infty_rotation (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (hi : H ≤ Mobius.mobiusInftyStabilizer) (hz : ∀ f ∈ H,f.val (0 : ℂ) = (0 : ℂ))
    (g : H) : ∃ a : ℂˣ, ‖(a : ℂ)‖ = 1 ∧ g.val = Mobius.mobiusScaling a := by
  let gi : Mobius.mobiusInftyStabilizer := ⟨g.val,hi g.property⟩
  refine ⟨Mobius.subgroupMultiplierHom H hi g,finiteMobius_multiplier_unit_norm H hi g,?_⟩
  change g.val = Mobius.mobiusScaling (Mobius.mobiusMultiplier gi)
  rw [Mobius.mobiusScaling,← mobiusAffineConstant_zero_of_fix_zero gi (hz _ g.property)]
  exact Mobius.mobius_affine_representation gi

theorem finiteMobius_two_orbits_common_pair (H : Subgroup Mobius.complexMobiusGroup)
    [Finite H] [Nontrivial H] (hm : Nat.card (MobiusVertexOrbit H) = 2) :
    ∃ a b : Mobius.ExtendedComplex,a ≠ b ∧ ∀ f ∈ H,f.val a = a ∧ f.val b = b := by
  obtain ⟨g,hg⟩ := exists_ne (1 : H)
  obtain ⟨a,b,hab,hfix⟩ := finiteMobius_nonidentity_two_fixed H g hg
  have ha : a ∈ mobiusVertices H := ⟨g,hg,(hfix a).mpr (Or.inl rfl)⟩
  have hb : b ∈ mobiusVertices H := ⟨g,hg,(hfix b).mpr (Or.inr rfl)⟩
  have hv := finiteMobius_two_orbits_vertex_card H hm
  refine ⟨a,b,hab,?_⟩
  intro f hf
  exact ⟨congrArg Subtype.val (finiteMobius_two_vertices_fixed H hv ⟨f,hf⟩ ⟨a,ha⟩),
    congrArg Subtype.val (finiteMobius_two_vertices_fixed H hv ⟨f,hf⟩ ⟨b,hb⟩)⟩

theorem finiteMobius_common_pair_conjugate_cyclic_rotations (H : Subgroup Mobius.complexMobiusGroup)
    [Finite H] (a b : Mobius.ExtendedComplex) (hab : a ≠ b)
    (hfix : ∀ f ∈ H,f.val a = a ∧ f.val b = b) :
    ∃ u : Mobius.complexMobiusGroup,
      Finite (DiscreteGroups.Action.Actions.subgroupConjugate u H) ∧
      IsCyclic (DiscreteGroups.Action.Actions.subgroupConjugate u H) ∧
      ∀ f ∈ DiscreteGroups.Action.Actions.subgroupConjugate u H,
        ∃ c : ℂˣ, ‖(c : ℂ)‖ = 1 ∧ f = Mobius.mobiusScaling c := by
  obtain ⟨u,hua,hub⟩ := mobius_exists_send_pair_zero_infty a b hab
  change u • a = ((0 : ℂ) : Mobius.ExtendedComplex) at hua
  change u • b = (∞ : Mobius.ExtendedComplex) at hub
  let K := DiscreteGroups.Action.Actions.subgroupConjugate u H
  let e : H ≃* K := DiscreteGroups.Action.Actions.subgroupConjugateEquivalence u H
  have : Finite K := Finite.of_surjective e e.surjective
  have hia : u⁻¹ • ((0 : ℂ) : Mobius.ExtendedComplex) = a := by
    change u⁻¹ • _ = a
    rw [← hua,inv_smul_smul]
  have hib : u⁻¹ • (∞ : Mobius.ExtendedComplex) = b := by
    rw [← hub,inv_smul_smul]
  have hk (f : Mobius.complexMobiusGroup) (hf : f ∈ K) :
      f.val (0 : ℂ) = (0 : ℂ) ∧ f.val ∞ = ∞ := by
    obtain ⟨g,hg,rfl⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff u H f).mp hf
    have hgfix := hfix g hg
    change g • a = a ∧ g • b = b at hgfix
    constructor
    · change (u*g*u⁻¹) • ((0 : ℂ) : Mobius.ExtendedComplex) = ((0 : ℂ) : Mobius.ExtendedComplex)
      simp only [mul_smul,hia,hgfix.1]
      exact hua
    · change (u*g*u⁻¹) • (∞ : Mobius.ExtendedComplex) = ∞
      simp only [mul_smul,hib,hgfix.2]
      exact hub
  have hi : K ≤ Mobius.mobiusInftyStabilizer := fun f hf => (hk f hf).2
  have hz : ∀ f ∈ K,f.val (0 : ℂ) = (0 : ℂ) := fun f hf => (hk f hf).1
  exact ⟨u,inferInstance,finiteMobius_fix_zero_infty_isCyclic K hi hz,
    fun f hf => finiteMobius_fix_zero_infty_rotation K hi hz ⟨f,hf⟩⟩

/-- Two vertex orbits give a conjugate cyclic rotation group. -/
theorem finiteMobius_two_orbits_conjugate_cyclic_rotations (H : Subgroup Mobius.complexMobiusGroup)
    [Finite H] [Nontrivial H] (hm : Nat.card (MobiusVertexOrbit H) = 2) :
    ∃ u : Mobius.complexMobiusGroup,
      Finite (DiscreteGroups.Action.Actions.subgroupConjugate u H) ∧
      IsCyclic (DiscreteGroups.Action.Actions.subgroupConjugate u H) ∧
      ∀ f ∈ DiscreteGroups.Action.Actions.subgroupConjugate u H,
        ∃ c : ℂˣ, ‖(c : ℂ)‖ = 1 ∧ f = Mobius.mobiusScaling c := by
  obtain ⟨a,b,hab,hfix⟩ := finiteMobius_two_orbits_common_pair H hm
  exact finiteMobius_common_pair_conjugate_cyclic_rotations H a b hab hfix

theorem finiteMobius_two_orbits_isCyclic (H : Subgroup Mobius.complexMobiusGroup)
    [Finite H] [Nontrivial H] (hm : Nat.card (MobiusVertexOrbit H) = 2) : IsCyclic H := by
  obtain ⟨u,_,hc,_⟩ := finiteMobius_two_orbits_conjugate_cyclic_rotations H hm
  exact (DiscreteGroups.Action.Actions.subgroupConjugateEquivalence u H).isCyclic.mpr hc

end LowDimensionalTopology.Geometry.DiscreteGroups
