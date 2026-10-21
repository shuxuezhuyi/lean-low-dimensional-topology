/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteOctahedralGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusLocalDomains
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.AlternatingGroupOrder60

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

abbrev NonidentityInvolution (G : Type*) [Group G] := {g : G // g ≠ 1 ∧ g*g=1}

theorem nonidentityInvolution_iff_order_two {G : Type*} [Group G] (g : G) :
    g ≠ 1 ∧ g*g=1 ↔ orderOf g=2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime_iff]
  simp only [pow_two,and_comm]

theorem cyclic_nonidentityInvolution_card (G : Type*) [Group G] [Finite G] [IsCyclic G] :
    Nat.card (NonidentityInvolution G) = (Nat.card G).gcd 2 - 1 := by
  let : CommGroup G := IsCyclic.commGroup
  have he : {g : G | g ≠ 1 ∧ g*g=1} = {g : G | g^2=1} \ {1} := by
    ext g
    simp only [mem_ofPred_eq,mem_sdiff,mem_singleton_iff,pow_two,and_comm]
  change {g : G | g ≠ 1 ∧ g*g=1}.ncard = _
  rw [he,Set.ncard_sdiff_singleton_of_mem (by simp)]
  change Nat.card (powMonoidHom 2 : G →* G).ker - 1 = _
  rw [IsCyclic.card_powMonoidHom_ker]

theorem finiteMobius_vertex_stabilizer_isCyclic (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (z : MobiusVertex H) : IsCyclic (MulAction.stabilizer H z) := by
  let K := MulAction.stabilizer H z
  let L := K.map H.subtype
  let e : K ≃* L := K.equivMapOfInjective H.subtype Subtype.val_injective
  have : Finite L := Finite.of_surjective e e.surjective
  have hz : ∀ f ∈ L,f.val (z : Mobius.ExtendedComplex)=(z : Mobius.ExtendedComplex) := by
    rintro f ⟨g,hg,rfl⟩
    have h : g • z=z := hg
    exact congrArg Subtype.val h
  exact e.isCyclic.mpr (finiteMobius_fix_boundary_isCyclic L z.val hz)

abbrev IcosahedralBranchProfile (H : Subgroup Mobius.complexMobiusGroup)
    (e : Fin 3 ≃ MobiusVertexOrbit H) : Prop :=
  (Nat.card H,mobiusVertexBranchOrder H (e 0),mobiusVertexBranchOrder H (e 1),
    mobiusVertexBranchOrder H (e 2))=(60,2,3,5)

theorem icosahedral_vertex_stabilizer_orders (H : Subgroup Mobius.complexMobiusGroup)
    (e : Fin 3 ≃ MobiusVertexOrbit H) (hp : IcosahedralBranchProfile H e)
    (z : MobiusVertex H) :
    Nat.card (MulAction.stabilizer H z)=2 ∨ Nat.card (MulAction.stabilizer H z)=3 ∨
      Nat.card (MulAction.stabilizer H z)=5 := by
  have h0 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.1) hp
  have h1 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.2.1) hp
  have h2 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.2.2) hp
  change mobiusVertexBranchOrder H (e 0)=2 at h0
  change mobiusVertexBranchOrder H (e 1)=3 at h1
  change mobiusVertexBranchOrder H (e 2)=5 at h2
  rw [vertex_stabilizer_card_eq_branchOrder]
  obtain ⟨i,hi⟩ := e.surjective (Quotient.mk'' z)
  rw [← hi]
  fin_cases i
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h2)

theorem icosahedral_element_orders (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (e : Fin 3 ≃ MobiusVertexOrbit H) (hp : IcosahedralBranchProfile H e)
    (g : H) (hg : g ≠ 1) : orderOf g=2 ∨ orderOf g=3 ∨ orderOf g=5 := by
  obtain ⟨a,b,_,hfix⟩ := finiteMobius_nonidentity_two_fixed H g hg
  have ha : a ∈ mobiusVertices H := ⟨g,hg,(hfix a).mpr (Or.inl rfl)⟩
  let va : MobiusVertex H := ⟨a,ha⟩
  have hga : g ∈ MulAction.stabilizer H va := Subtype.ext ((hfix a).mpr (Or.inl rfl))
  have hd := (MulAction.stabilizer H va).orderOf_dvd_natCard hga
  have ho : orderOf g ≠ 1 := fun h => hg (orderOf_eq_one_iff.mp h)
  rcases icosahedral_vertex_stabilizer_orders H e hp va with h2 | h3 | h5
  · rw [h2] at hd
    exact Or.inl (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left ho)
  · rw [h3] at hd
    exact Or.inr (Or.inl (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left ho))
  · rw [h5] at hd
    exact Or.inr (Or.inr (((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd).resolve_left ho))

def mobiusOrderTwoVertices (H : Subgroup Mobius.complexMobiusGroup) : Set (MobiusVertex H) :=
  {z | Nat.card (MulAction.stabilizer H z)=2}

theorem icosahedral_orderTwoVertices_eq_orbit (H : Subgroup Mobius.complexMobiusGroup)
    (e : Fin 3 ≃ MobiusVertexOrbit H) (hp : IcosahedralBranchProfile H e) :
    mobiusOrderTwoVertices H=MulAction.orbit H (e 0).out := by
  have h0 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.1) hp
  have h1 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.2.1) hp
  have h2 := congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.2.2) hp
  change mobiusVertexBranchOrder H (e 0)=2 at h0
  change mobiusVertexBranchOrder H (e 1)=3 at h1
  change mobiusVertexBranchOrder H (e 2)=5 at h2
  ext z
  change Nat.card (MulAction.stabilizer H z)=2 ↔ z ∈ MulAction.orbit H (e 0).out
  rw [vertex_stabilizer_card_eq_branchOrder,
    ← MulAction.orbitRel.Quotient.orbit_eq_orbit_out (e 0) Quotient.out_eq',
    MulAction.orbitRel.Quotient.mem_orbit]
  constructor
  · intro hz
    obtain ⟨i,hi⟩ := e.surjective (Quotient.mk'' z)
    rw [← hi] at hz ⊢
    fin_cases i
    · rfl
    · change mobiusVertexBranchOrder H (e 1)=2 at hz
      omega
    · change mobiusVertexBranchOrder H (e 2)=2 at hz
      omega
  · intro hz
    rw [hz]
    exact h0

theorem icosahedral_orderTwoVertices_card (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (e : Fin 3 ≃ MobiusVertexOrbit H) (hp : IcosahedralBranchProfile H e) :
    Nat.card (mobiusOrderTwoVertices H)=30 := by
  have hH : Nat.card H=60 := congrArg Prod.fst hp
  have h0 : mobiusVertexBranchOrder H (e 0)=2 :=
    congrArg (fun t : ℕ×ℕ×ℕ×ℕ => t.2.1) hp
  have hs := finiteMobius_vertex_orbit_stabilizer H (e 0).out
  change Nat.card (MulAction.orbit H (e 0).out)*mobiusVertexBranchOrder H (e 0)=Nat.card H at hs
  rw [h0,hH] at hs
  rw [icosahedral_orderTwoVertices_eq_orbit H e hp]
  omega

def involutionIncidenceEquiv (G X : Type*) [Group G] [MulAction G X] :
    (Σ g : NonidentityInvolution G,MulAction.fixedBy X g.val) ≃
      Σ x : X,NonidentityInvolution (MulAction.stabilizer G x) where
  toFun p := by
    refine ⟨p.2.val,⟨⟨p.1.val,p.2.property⟩,?_,?_⟩⟩
    · intro h
      exact p.1.property.1 (congrArg Subtype.val h)
    · exact Subtype.ext p.1.property.2
  invFun p := by
    refine ⟨⟨p.2.val.val,?_,?_⟩,⟨p.1,p.2.val.property⟩⟩
    · intro h
      exact p.2.property.1 (Subtype.ext h)
    · exact congrArg Subtype.val p.2.property.2
  left_inv := by
    rintro ⟨⟨g,hneq,hsq⟩,⟨x,hfix⟩⟩
    rfl
  right_inv := by
    rintro ⟨x,⟨⟨g,hfix⟩,hneq,hsq⟩⟩
    rfl

theorem icosahedral_stabilizer_involution_card (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (e : Fin 3 ≃ MobiusVertexOrbit H) (hp : IcosahedralBranchProfile H e) (z : MobiusVertex H) :
    Nat.card (NonidentityInvolution (MulAction.stabilizer H z)) =
      if Nat.card (MulAction.stabilizer H z)=2 then 1 else 0 := by
  have : IsCyclic (MulAction.stabilizer H z) := finiteMobius_vertex_stabilizer_isCyclic H z
  rw [cyclic_nonidentityInvolution_card]
  rcases icosahedral_vertex_stabilizer_orders H e hp z with h2 | h3 | h5
  · rw [h2]
    norm_num
  · rw [h3]
    norm_num
  · rw [h5]
    norm_num

theorem icosahedral_involution_card (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (e : Fin 3 ≃ MobiusVertexOrbit H) (hp : IcosahedralBranchProfile H e) :
    Nat.card (NonidentityInvolution H)=15 := by
  classical
  let : Fintype (NonidentityInvolution H) := Fintype.ofFinite _
  let : Fintype (MobiusVertex H) := Fintype.ofFinite _
  have hsum : (∑ z : MobiusVertex H,
      if Nat.card (MulAction.stabilizer H z)=2 then (1 : ℕ) else 0) =
      Nat.card (mobiusOrderTwoVertices H) := by
    simp [Nat.card_eq_fintype_card,Fintype.card_subtype,mobiusOrderTwoVertices]
  have he := Nat.card_congr (involutionIncidenceEquiv H (MobiusVertex H))
  rw [Nat.card_sigma,Nat.card_sigma] at he
  have hf (g : NonidentityInvolution H) : Nat.card (MulAction.fixedBy (MobiusVertex H) g.val)=2 :=
    finiteMobius_vertex_fixedBy_card H g.val g.property.1
  simp_rw [hf,icosahedral_stabilizer_involution_card H e hp] at he
  rw [hsum,icosahedral_orderTwoVertices_card H e hp] at he
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card] at he
  change Nat.card (NonidentityInvolution H)*2=30 at he
  omega

/-- The genuine `(60,2,3,5)` branch is the alternating group on five letters. -/
def finiteMobius_icosahedral_branchEquiv (H : Subgroup Mobius.complexMobiusGroup) [Finite H]
    (e : Fin 3 ≃ MobiusVertexOrbit H) (hp : IcosahedralBranchProfile H e) :
    H ≃* alternatingGroup (Fin 5) := by
  have hH : Nat.card H=60 := congrArg Prod.fst hp
  have hNo : HasNoNontrivialCyclicNormalSubgroup H := by
    intro N hn hc
    let := hn
    let := hc
    exact normal_cyclic_subgroup_eq_bot_of_no_small_vertex_orbit H
      (hasNoSmallVertexOrbit_of_icosahedral_profile H e hp) N
  exact groupOrder60EquivAlternatingFive hH hNo (icosahedral_element_orders H e hp)
    (icosahedral_involution_card H e hp)

end LowDimensionalTopology.Geometry.DiscreteGroups
