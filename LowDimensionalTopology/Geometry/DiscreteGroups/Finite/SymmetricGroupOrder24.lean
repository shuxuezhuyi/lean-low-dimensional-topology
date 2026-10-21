module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
@[expose] public section
noncomputable section
namespace LowDimensionalTopology.Geometry.DiscreteGroups

/-- The genuine absence of nontrivial normal cyclic subgroups. -/
def HasNoNontrivialCyclicNormalSubgroup (G : Type*) [Group G] : Prop :=
  ∀ N : Subgroup G, N.Normal → IsCyclic N → N = ⊥

section Order24
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow three-subgroup has exact order three in an order-twenty-four group. -/
theorem order24_sylowThree_card (hG : Nat.card G = 24) (P : Sylow 3 G) : Nat.card P = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := P.card_eq_multiplicity
  have hv : (24 : ℕ).factorization 3 = 1 := by
    rw [show (24 : ℕ) = 2 ^ 3 * 3 from by norm_num,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    norm_num [Nat.Prime.factorization (by decide : Nat.Prime 2),
      Nat.Prime.factorization (by decide : Nat.Prime 3)]
  rw [hG, hv] at h
  norm_num at h
  exact h

/-- A normal Sylow three-subgroup would be an excluded nontrivial cyclic normal subgroup. -/
theorem order24_sylowThree_not_normal (hG : Nat.card G = 24)
    (hN : HasNoNontrivialCyclicNormalSubgroup G) (P : Sylow 3 G) : ¬P.Normal := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro hp
  have hc := order24_sylowThree_card hG P
  have he := hN (P : Subgroup G) hp (isCyclic_of_prime_card hc)
  change Nat.card (P : Subgroup G) = 3 at hc
  rw [he, Subgroup.card_bot] at hc
  omega

/-- Exactly four Sylow three-subgroups remain after excluding the normal cyclic case. -/
theorem order24_sylowThree_count (hG : Nat.card G = 24)
    (hN : HasNoNontrivialCyclicNormalSubgroup G) : Nat.card (Sylow 3 G) = 4 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 G := Classical.choice inferInstance
  have hidx : P.index = 8 := by
    have he := (P : Subgroup G).index_mul_card
    rw [hG, order24_sylowThree_card hG P] at he
    omega
  have hd := P.card_dvd_index
  rw [hidx] at hd
  have hm : Nat.card (Sylow 3 G) % 3 = 1 % 3 := card_sylow_modEq_one 3 G
  have hle : Nat.card (Sylow 3 G) ≤ 8 := Nat.le_of_dvd (by decide) hd
  have hcases : Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 ∨
      Nat.card (Sylow 3 G) = 7 := by omega
  rcases hcases with h | h | h
  · let : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp h).1
    exact (order24_sylowThree_not_normal hG hN P (Sylow.normal_of_subsingleton P)).elim
  · exact h
  · rw [h] at hd
    norm_num at hd

/-- The normalizer of each Sylow three-subgroup has exact order six. -/
theorem order24_sylowThree_normalizer_card (hG : Nat.card G = 24)
    (hN : HasNoNontrivialCyclicNormalSubgroup G) (P : Sylow 3 G) :
    Nat.card (Subgroup.normalizer (P : Set G)) = 6 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have he := (Subgroup.normalizer (P : Set G)).index_mul_card
  rw [hG, ← P.card_eq_index_normalizer, order24_sylowThree_count hG hN] at he
  omega

/-- The actual conjugation action on the Sylow three-subgroups. -/
def order24SylowThreeHom : G →* Equiv.Perm (Sylow 3 G) :=
  MulAction.toPermHom G (Sylow 3 G)

omit [Finite G] in
/-- Its kernel lies inside every actual Sylow normalizer. -/
theorem order24SylowThreeHom_ker_le_normalizer (P : Sylow 3 G) :
    (order24SylowThreeHom (G := G)).ker ≤ Subgroup.normalizer (P : Set G) := by
  intro g hg
  apply Sylow.smul_eq_iff_mem_normalizer.mp
  exact congrArg (fun f : Equiv.Perm (Sylow 3 G) => f P) hg

/-- The Sylow action is faithful: possible kernel orders two, three and six are all excluded. -/
theorem order24SylowThreeHom_injective (hG : Nat.card G = 24)
    (hN : HasNoNontrivialCyclicNormalSubgroup G) :
    Function.Injective (order24SylowThreeHom (G := G)) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 G := Classical.choice inferInstance
  let K := (order24SylowThreeHom (G := G)).ker
  have hle : K ≤ Subgroup.normalizer (P : Set G) := order24SylowThreeHom_ker_le_normalizer P
  have hcN := order24_sylowThree_normalizer_card hG hN P
  have hd : Nat.card K ∣ 6 := by
    simpa only [hcN] using Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hbound : Nat.card K ≤ 6 := Nat.le_of_dvd (by decide) hd
  have hcases : Nat.card K = 1 ∨ Nat.card K = 2 ∨ Nat.card K = 3 ∨ Nat.card K = 6 := by
    interval_cases hk : Nat.card K <;> norm_num [hk] at hd <;> omega
  apply (MonoidHom.ker_eq_bot_iff _).mp
  change K = ⊥
  rcases hcases with h1 | h2 | h3 | h6
  · exact K.eq_bot_of_card_eq h1
  · let : Fact (Nat.Prime 2) := ⟨by decide⟩
    exact hN K inferInstance (isCyclic_of_prime_card h2)
  · exact hN K inferInstance (isCyclic_of_prime_card h3)
  · have he : K = Subgroup.normalizer (P : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (by omega)
    have hn : (Subgroup.normalizer (P : Set G)).Normal := he ▸ (inferInstance : K.Normal)
    exact (order24_sylowThree_not_normal hG hN P (P.normal_of_normalizer_normal hn)).elim

/-- Label the four genuine Sylow subgroups. -/
def order24SylowThreeEquiv (hG : Nat.card G = 24)
    (hN : HasNoNontrivialCyclicNormalSubgroup G) : Sylow 3 G ≃ Fin 4 := by
  letI : Fintype (Sylow 3 G) := Fintype.ofFinite _
  exact Fintype.equivFinOfCardEq
    (by simpa only [Nat.card_eq_fintype_card] using order24_sylowThree_count hG hN)

/-- The faithful labeled conjugation representation into S4. -/
def order24PermFourHom (hG : Nat.card G = 24)
    (hN : HasNoNontrivialCyclicNormalSubgroup G) : G →* Equiv.Perm (Fin 4) :=
  (order24SylowThreeEquiv hG hN).permCongrHom.toMonoidHom.comp order24SylowThreeHom

/-- An order-twenty-four group without nontrivial normal cyclic subgroups is S4. -/
def groupOrder24EquivPermFour (hG : Nat.card G = 24)
    (hN : HasNoNontrivialCyclicNormalSubgroup G) : G ≃* Equiv.Perm (Fin 4) := by
  let f := order24PermFourHom hG hN
  have hf : Function.Injective f :=
    (order24SylowThreeEquiv hG hN).permCongrHom.injective.comp
      (order24SylowThreeHom_injective hG hN)
  have hc : Nat.card f.range = 24 := by
    rw [← hG]
    exact Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm
  have hp : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have hr : f.range = ⊤ := Subgroup.eq_top_of_card_eq _ (hc.trans hp.symm)
  exact MulEquiv.ofBijective f ⟨hf, MonoidHom.range_eq_top.mp hr⟩

end Order24
end LowDimensionalTopology.Geometry.DiscreteGroups
