/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteDihedralGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.SymmetricGroupOrder24

@[expose] public section
noncomputable section
open Set
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

def HasNoSmallVertexOrbit (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  ∀ z : MobiusVertex H,2 < Nat.card (MulAction.orbit H z)

theorem normal_cyclic_subgroup_eq_bot_of_no_small_vertex_orbit
    (H : Subgroup Mobius.complexMobiusGroup) [Finite H] (hH : HasNoSmallVertexOrbit H)
    (N : Subgroup H) [N.Normal] [IsCyclic N] : N = ⊥ := by
  by_contra hN
  have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  obtain ⟨f,hgen⟩ := exists_zpow_surjective N
  have hf : f ≠ 1 := by
    intro hf
    obtain ⟨g,hg⟩ := exists_ne (1 : N)
    obtain ⟨i,rfl⟩ := hgen g
    simp only [hf,one_zpow,ne_eq,not_true_eq_false] at hg
  have hfH : f.val ≠ 1 := fun h => hf (Subtype.ext h)
  obtain ⟨a,b,hab,hfix⟩ := finiteMobius_nonidentity_two_fixed H f.val hfH
  have hfa : f • a=a := (hfix a).mpr (Or.inl rfl)
  have hall (x : Mobius.ExtendedComplex) (hx : f • x=x) (g : N) : g • x=x := by
    obtain ⟨i,rfl⟩ := hgen g
    exact (MulAction.stabilizer N x).zpow_mem hx i
  have hsub : MulAction.orbit H a ⊆ ({a,b} : Set Mobius.ExtendedComplex) := by
    rintro x ⟨g,rfl⟩
    have hc : g⁻¹*f.val*g ∈ N := (inferInstance : N.Normal).conj_mem' f.val f.property g
    have ha : (g⁻¹*f.val*g) • a=a := hall a hfa ⟨g⁻¹*f.val*g,hc⟩
    have ha' := congrArg (fun x : Mobius.ExtendedComplex => g • x) ha
    have hfixed : f.val • (g • a)=g • a := by
      simpa only [mul_smul,smul_inv_smul] using ha'
    exact Set.mem_insert_iff.mpr ((hfix (g • a)).mp hfixed)
  have haVert : a ∈ mobiusVertices H := ⟨f.val,hfH,hfa⟩
  let va : MobiusVertex H := ⟨a,haVert⟩
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hab] at hcard
  have he := mobiusVertex_orbit_boundary_card H va
  change Nat.card (MulAction.orbit H a)=Nat.card (MulAction.orbit H va) at he
  change Nat.card (MulAction.orbit H a) ≤ 2 at hcard
  rw [he] at hcard
  have hh := hH va
  omega

theorem vertex_stabilizer_card_eq_branchOrder (H : Subgroup Mobius.complexMobiusGroup)
    (z : MobiusVertex H) :
    Nat.card (MulAction.stabilizer H z) =
      mobiusVertexBranchOrder H (Quotient.mk'' z) := by
  have hr : MulAction.orbitRel H (MobiusVertex H)
      (Quotient.out (Quotient.mk'' z)) z := Quotient.exact' (Quotient.out_eq' _)
  exact Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel hr).symm.toEquiv

theorem hasNoSmallVertexOrbit_of_branch_bound (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (b : ℕ) (hb : ∀ o : MobiusVertexOrbit H,mobiusVertexBranchOrder H o ≤ b)
    (hh : 2*b < Nat.card H) : HasNoSmallVertexOrbit H := by
  intro z
  have ho := finiteMobius_vertex_orbit_stabilizer H z
  have hs : Nat.card (MulAction.stabilizer H z) ≤ b := by
    rw [vertex_stabilizer_card_eq_branchOrder]
    exact hb _
  nlinarith

theorem hasNoSmallVertexOrbit_of_three_order_bound (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (e : Fin 3 ≃ MobiusVertexOrbit H) (b : ℕ)
    (hb : ∀ i : Fin 3,mobiusVertexBranchOrder H (e i) ≤ b)
    (hh : 2*b < Nat.card H) : HasNoSmallVertexOrbit H := by
  apply hasNoSmallVertexOrbit_of_branch_bound H b ?_ hh
  intro o
  obtain ⟨i,rfl⟩ := e.surjective o
  exact hb i

theorem hasNoSmallVertexOrbit_of_octahedral_profile (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (e : Fin 3 ≃ MobiusVertexOrbit H)
    (hp : (Nat.card H,mobiusVertexBranchOrder H (e 0),mobiusVertexBranchOrder H (e 1),
      mobiusVertexBranchOrder H (e 2))=(24,2,3,4)) : HasNoSmallVertexOrbit H := by
  have hH := congrArg Prod.fst hp
  have h0 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.1) hp
  have h1 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.2.1) hp
  have h2 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.2.2) hp
  change Nat.card H=24 at hH
  change mobiusVertexBranchOrder H (e 0)=2 at h0
  change mobiusVertexBranchOrder H (e 1)=3 at h1
  change mobiusVertexBranchOrder H (e 2)=4 at h2
  apply hasNoSmallVertexOrbit_of_three_order_bound H e 4 ?_ (by omega)
  intro i
  fin_cases i
  · change mobiusVertexBranchOrder H (e 0) ≤ 4
    omega
  · change mobiusVertexBranchOrder H (e 1) ≤ 4
    omega
  · change mobiusVertexBranchOrder H (e 2) ≤ 4
    omega

theorem hasNoSmallVertexOrbit_of_icosahedral_profile (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (e : Fin 3 ≃ MobiusVertexOrbit H)
    (hp : (Nat.card H,mobiusVertexBranchOrder H (e 0),mobiusVertexBranchOrder H (e 1),
      mobiusVertexBranchOrder H (e 2))=(60,2,3,5)) : HasNoSmallVertexOrbit H := by
  have hH := congrArg Prod.fst hp
  have h0 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.1) hp
  have h1 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.2.1) hp
  have h2 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.2.2) hp
  change Nat.card H=60 at hH
  change mobiusVertexBranchOrder H (e 0)=2 at h0
  change mobiusVertexBranchOrder H (e 1)=3 at h1
  change mobiusVertexBranchOrder H (e 2)=5 at h2
  apply hasNoSmallVertexOrbit_of_three_order_bound H e 5 ?_ (by omega)
  intro i
  fin_cases i
  · change mobiusVertexBranchOrder H (e 0) ≤ 5
    omega
  · change mobiusVertexBranchOrder H (e 1) ≤ 5
    omega
  · change mobiusVertexBranchOrder H (e 2) ≤ 5
    omega

/-- The genuine `(24,2,3,4)` branch is the symmetric group on four letters. -/
def finiteMobius_octahedral_branchEquiv (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (e : Fin 3 ≃ MobiusVertexOrbit H)
    (hp : (Nat.card H,mobiusVertexBranchOrder H (e 0),mobiusVertexBranchOrder H (e 1),
      mobiusVertexBranchOrder H (e 2))=(24,2,3,4)) : H ≃* Equiv.Perm (Fin 4) := by
  have hH : Nat.card H=24 := congrArg Prod.fst hp
  have hNo := hasNoSmallVertexOrbit_of_octahedral_profile H e hp
  apply groupOrder24EquivPermFour hH
  intro N hn hc
  let := hn
  let := hc
  exact normal_cyclic_subgroup_eq_bot_of_no_small_vertex_orbit H hNo N

end LowDimensionalTopology.Geometry.DiscreteGroups
