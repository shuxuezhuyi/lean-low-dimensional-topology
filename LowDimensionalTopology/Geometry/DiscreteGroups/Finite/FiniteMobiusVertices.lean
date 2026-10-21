/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteMobiusGroups
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

def mobiusVertexSubaction (H : Subgroup Mobius.complexMobiusGroup) :
    SubMulAction H Mobius.ExtendedComplex where
  carrier := mobiusVertices H
  smul_mem' := fun g _ hx => mobiusVertices_smul H g hx

abbrev MobiusVertex (H : Subgroup Mobius.complexMobiusGroup) := mobiusVertexSubaction H

instance finiteMobiusVertex (H : Subgroup Mobius.complexMobiusGroup) [Finite H] :
    Finite (MobiusVertex H) := (mobiusVertices_finite H).to_subtype

abbrev MobiusVertexOrbit (H : Subgroup Mobius.complexMobiusGroup) :=
  MulAction.orbitRel.Quotient H (MobiusVertex H)

instance fintypeMobiusVertexOrbit (H : Subgroup Mobius.complexMobiusGroup) [Finite H] :
    Fintype (MobiusVertexOrbit H) := Fintype.ofFinite _

theorem finiteMobius_nonidentity_two_fixed (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (g : H) (hg : g ≠ 1) :
    ∃ a b : Mobius.ExtendedComplex, a ≠ b ∧ ∀ z, g • z = z ↔ z = a ∨ z = b := by
  have hg0 : g.val ≠ 1 := fun h => hg (Subtype.ext h)
  have hf : (MulAction.orbit H Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).Finite :=
    Set.finite_range (fun f : H => f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
  have he := finite_H3_orbit_all_elliptic H Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ hf g.val g.property hg0
  rcases Mobius.mobius_nonidentity_fixedPoint_dichotomy g.val hg0 with ⟨a, ha⟩ | hpair
  · exact False.elim (he.not_parabolic ⟨hg0, a, ha⟩)
  · exact hpair

theorem finiteMobius_vertex_fixedBy_card (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (g : H) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy (MobiusVertex H) g) = 2 := by
  obtain ⟨a,b,hab,hfix⟩ := finiteMobius_nonidentity_two_fixed H g hg
  have ha : a ∈ mobiusVertices H := ⟨g,hg,(hfix a).mpr (Or.inl rfl)⟩
  have hb : b ∈ mobiusVertices H := ⟨g,hg,(hfix b).mpr (Or.inr rfl)⟩
  let va : MobiusVertex H := ⟨a,ha⟩
  let vb : MobiusVertex H := ⟨b,hb⟩
  have hv : va ≠ vb := fun h => hab (congrArg Subtype.val h)
  have hset : MulAction.fixedBy (MobiusVertex H) g = {va,vb} := by
    ext z
    change g • z = z ↔ z = va ∨ z = vb
    rw [Subtype.ext_iff]
    change g • (z : Mobius.ExtendedComplex) = (z : Mobius.ExtendedComplex) ↔ _
    rw [hfix]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  change (MulAction.fixedBy (MobiusVertex H) g).ncard = 2
  rw [hset,Set.ncard_pair hv]

theorem finiteMobius_vertex_fixedBy_one_card (H : Subgroup Mobius.complexMobiusGroup) [Finite H] :
    Nat.card (MulAction.fixedBy (MobiusVertex H) (1 : H)) = Nat.card (MobiusVertex H) := by
  have he : MulAction.fixedBy (MobiusVertex H) (1 : H) = univ := by
    ext z
    exact ⟨fun _ => mem_univ _,fun _ => one_smul H z⟩
  rw [he]
  exact Nat.card_congr (Equiv.Set.univ (MobiusVertex H))

theorem finiteMobius_vertex_stabilizer_card_ge_two (H : Subgroup Mobius.complexMobiusGroup)
    [Finite H] (z : MobiusVertex H) : 2 ≤ Nat.card (MulAction.stabilizer H z) := by
  obtain ⟨g,hg,hfix⟩ := z.property
  have hm : g ∈ MulAction.stabilizer H z := Subtype.ext hfix
  have hne : (⟨g,hm⟩ : MulAction.stabilizer H z) ≠ 1 := by
    intro h
    exact hg (congrArg Subtype.val h)
  have : Nontrivial (MulAction.stabilizer H z) := ⟨⟨_,_,hne⟩⟩
  let : Fintype (MulAction.stabilizer H z) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using (Nat.succ_le_of_lt (Fintype.one_lt_card : 1 < Fintype.card
    (MulAction.stabilizer H z)))

theorem finiteMobius_vertex_orbit_stabilizer (H : Subgroup Mobius.complexMobiusGroup)
    [Finite H] (z : MobiusVertex H) :
    Nat.card (MulAction.orbit H z) * Nat.card (MulAction.stabilizer H z) = Nat.card H := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H z)

theorem finiteMobius_vertex_burnside (H : Subgroup Mobius.complexMobiusGroup) [Finite H] :
    Nat.card (MobiusVertexOrbit H) * Nat.card H =
      Nat.card (MobiusVertex H) + 2 * (Nat.card H - 1) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  let : Fintype (MobiusVertex H) := Fintype.ofFinite _
  let : Fintype (MobiusVertexOrbit H) := Fintype.ofFinite _
  let (g : H) : Fintype (MulAction.fixedBy (MobiusVertex H) g) := Fintype.ofFinite _
  have hfix (g : H) : Fintype.card (MulAction.fixedBy (MobiusVertex H) g) =
      if g = 1 then Fintype.card (MobiusVertex H) else 2 := by
    split_ifs with hg
    · subst g
      simpa only [Nat.card_eq_fintype_card] using finiteMobius_vertex_fixedBy_one_card H
    · simpa only [Nat.card_eq_fintype_card] using finiteMobius_vertex_fixedBy_card H g hg
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H (MobiusVertex H)
  simp only [Nat.card_eq_fintype_card]
  rw [← hb]
  simp_rw [hfix]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : H))]
  have he : ∑ g ∈ Finset.univ.erase (1 : H),
      (if g = 1 then Fintype.card (MobiusVertex H) else 2) =
      (Fintype.card H - 1) * 2 := by
    have hval : ∀ g ∈ Finset.univ.erase (1 : H),
        (if g = 1 then Fintype.card (MobiusVertex H) else 2) = 2 := by
      intro g hg
      exact ite_eq_right (Finset.ne_of_mem_erase hg)
    rw [Finset.sum_congr rfl hval]
    simp
  rw [he]
  simp only [ite_true]
  omega

theorem finiteMobius_vertex_card_sum_orbits (H : Subgroup Mobius.complexMobiusGroup) [Finite H] :
    Nat.card (MobiusVertex H) =
      ∑ o : MobiusVertexOrbit H, Nat.card (MulAction.orbit H o.out) := by
  classical
  let : Fintype (MobiusVertex H) := Fintype.ofFinite _
  let (o : MobiusVertexOrbit H) : Fintype (MulAction.orbit H o.out) := Fintype.ofFinite _
  simpa only [Fintype.card_sigma, Nat.card_eq_fintype_card] using
    Fintype.card_congr (MulAction.selfEquivSigmaOrbits H (MobiusVertex H))

theorem finiteMobius_vertex_card_twice_le (H : Subgroup Mobius.complexMobiusGroup) [Finite H] :
    2 * Nat.card (MobiusVertex H) ≤ Nat.card (MobiusVertexOrbit H) * Nat.card H := by
  classical
  rw [finiteMobius_vertex_card_sum_orbits, Finset.mul_sum]
  calc
    ∑ o : MobiusVertexOrbit H, 2 * Nat.card (MulAction.orbit H o.out) ≤
        ∑ _ : MobiusVertexOrbit H, Nat.card H := by
      apply Finset.sum_le_sum
      intro o _
      have hs := finiteMobius_vertex_stabilizer_card_ge_two H o.out
      have he := finiteMobius_vertex_orbit_stabilizer H o.out
      nlinarith
    _ = Nat.card (MobiusVertexOrbit H) * Nat.card H := by
      simp [Nat.card_eq_fintype_card]

theorem finiteMobius_vertex_card_ge_two (H : Subgroup Mobius.complexMobiusGroup)
    [Finite H] [Nontrivial H] : 2 ≤ Nat.card (MobiusVertex H) := by
  classical
  obtain ⟨g,hg⟩ := exists_ne (1 : H)
  obtain ⟨a,b,hab,hfix⟩ := finiteMobius_nonidentity_two_fixed H g hg
  have ha : a ∈ mobiusVertices H := ⟨g,hg,(hfix a).mpr (Or.inl rfl)⟩
  have hb : b ∈ mobiusVertices H := ⟨g,hg,(hfix b).mpr (Or.inr rfl)⟩
  have hsub : ({a,b} : Set Mobius.ExtendedComplex) ⊆ mobiusVertices H := by
    intro z hz
    rcases mem_insert_iff.mp hz with rfl | hz
    · exact ha
    · simpa only [mem_singleton_iff] using (hz ▸ hb)
  have hcard := Set.ncard_le_ncard hsub (mobiusVertices_finite H)
  rw [Set.ncard_pair hab] at hcard
  exact hcard

theorem finiteMobius_vertex_orbits_two_or_three (H : Subgroup Mobius.complexMobiusGroup)
    [Finite H] [Nontrivial H] :
    Nat.card (MobiusVertexOrbit H) = 2 ∨ Nat.card (MobiusVertexOrbit H) = 3 := by
  have hb := finiteMobius_vertex_burnside H
  have hu := finiteMobius_vertex_card_twice_le H
  have hl := finiteMobius_vertex_card_ge_two H
  have hh : 0 < Nat.card H := Nat.card_pos
  have hlow : 2 ≤ Nat.card (MobiusVertexOrbit H) := by
    nlinarith [Nat.sub_add_cancel hh]
  have hupp : Nat.card (MobiusVertexOrbit H) < 4 := by
    nlinarith [Nat.sub_add_cancel hh]
  omega

theorem finiteMobius_vertex_reciprocal_order (H : Subgroup Mobius.complexMobiusGroup)
    [Finite H] (z : MobiusVertex H) :
    (1 : ℚ) / Nat.card (MulAction.stabilizer H z) =
      (Nat.card (MulAction.orbit H z) : ℚ) / Nat.card H := by
  have hs : (Nat.card (MulAction.stabilizer H z) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (MulAction.stabilizer H z)).ne'
  have hh : (Nat.card H : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card H).ne'
  apply (div_eq_div_iff hs hh).mpr
  simp only [one_mul]
  exact_mod_cast (finiteMobius_vertex_orbit_stabilizer H z).symm

/-- The vertex-orbit stabilizer orders satisfy the rational Euler identity. -/
theorem finiteMobius_vertex_euler (H : Subgroup Mobius.complexMobiusGroup) [Finite H] :
    (∑ o : MobiusVertexOrbit H,
      (1 - (1 : ℚ) / Nat.card (MulAction.stabilizer H o.out))) =
      2 - 2 / (Nat.card H : ℚ) := by
  classical
  have hh : (Nat.card H : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card H).ne'
  have hcard : ∑ o : MobiusVertexOrbit H, (Nat.card (MulAction.orbit H o.out) : ℚ) =
      (Nat.card (MobiusVertex H) : ℚ) := by
    exact_mod_cast (finiteMobius_vertex_card_sum_orbits H).symm
  have hb := congrArg (fun n : ℕ => (n : ℚ)) (finiteMobius_vertex_burnside H)
  push_cast [Nat.cast_sub (Nat.card_pos : 0 < Nat.card H)] at hb
  simp_rw [finiteMobius_vertex_reciprocal_order]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, hcard]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Nat.card_eq_fintype_card]
  field_simp
  nlinarith

end LowDimensionalTopology.Geometry.DiscreteGroups
