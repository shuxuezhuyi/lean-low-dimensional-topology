module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.SymmetricGroupOrder24
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
@[expose] public section
noncomputable section
namespace LowDimensionalTopology.Geometry.DiscreteGroups

/-- The actual element-order restriction needed in the icosahedral branch. -/
def HasIcosahedralElementOrders (G : Type*) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 5

/-- Nonidentity involutions, expressed by their actual group multiplication. -/
abbrev NontrivialInvolution (G : Type*) [Group G] := {g : G // g ≠ 1 ∧ g * g = 1}

section Order60
variable {G : Type*} [Group G] [Finite G]

/-- The two-primary part of sixty is four. -/
theorem order60_sylowTwo_card (hG : Nat.card G = 60) (P : Sylow 2 G) : Nat.card (P : Subgroup G) = 4 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hv : (60 : ℕ).factorization 2 = 2 := by
    rw [show (60 : ℕ) = 2 ^ 2 * (3 * 5) from by norm_num,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow,
      Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.Prime.factorization (by decide : Nat.Prime 2),
      Nat.Prime.factorization (by decide : Nat.Prime 3),
      Nat.Prime.factorization (by decide : Nat.Prime 5)]
  have h := P.card_eq_multiplicity
  rw [hG, hv] at h
  norm_num at h
  exact h

/-- Every element of a Sylow two-subgroup squares to the identity; order four is excluded. -/
theorem order60_sylowTwo_mul_self (hG : Nat.card G = 60) (hO : HasIcosahedralElementOrders G)
    (P : Sylow 2 G) (x : (P : Subgroup G)) : x * x = 1 := by
  by_cases hx : x = 1
  · simp [hx]
  · have hxG : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
    have hd := orderOf_dvd_natCard x
    rw [order60_sylowTwo_card hG P] at hd
    have horder : orderOf x = 2 := by
      rcases hO x.val hxG with h | h | h
      · simpa only [Subgroup.orderOf_coe] using h
      · rw [← Subgroup.orderOf_coe, h] at hd
        norm_num at hd
      · rw [← Subgroup.orderOf_coe, h] at hd
        norm_num at hd
    have hp := pow_orderOf_eq_one x
    simpa only [horder, pow_two] using hp

/-- The actual order-four Sylow subgroups are abelian groups of exponent two. -/
theorem order60_sylowTwo_commute (hG : Nat.card G = 60) (hO : HasIcosahedralElementOrders G)
    (P : Sylow 2 G) (x y : (P : Subgroup G)) : Commute x y := by
  have hi (z : (P : Subgroup G)) : z⁻¹ = z := by
    apply inv_eq_of_mul_eq_one_left
    exact order60_sylowTwo_mul_self hG hO P z
  have hxy := hi (x * y)
  rw [mul_inv_rev, hi x, hi y] at hxy
  exact hxy.symm

/-- A nonidentity involution has exact order two. -/
theorem order60_involution_order (g : NontrivialInvolution G) : orderOf g.val = 2 := by
  have hd : orderOf g.val ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by simpa only [pow_two] using g.property.2)
  have hn : orderOf g.val ≠ 1 := fun h => g.property.1 (orderOf_eq_one_iff.mp h)
  have hp : 0 < orderOf g.val := orderOf_pos _
  have hle : orderOf g.val ≤ 2 := Nat.le_of_dvd (by decide) hd
  omega

/-- No odd prime of the allowed orders divides the centralizer of an involution. -/
theorem order60_involution_centralizer_not_dvd (hO : HasIcosahedralElementOrders G)
    (g : NontrivialInvolution G) {p : ℕ} (hp : p = 3 ∨ p = 5) :
    ¬p ∣ Nat.card (Subgroup.centralizer ({g.val} : Set G)) := by
  have hprime : Nat.Prime p := by rcases hp with rfl | rfl <;> decide
  let : Fact (Nat.Prime p) := ⟨hprime⟩
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({g.val} : Set G)) p hd
  have hxG : orderOf (x : G) = p := by simpa only [Subgroup.orderOf_coe] using hx
  have hcomm : Commute g.val (x : G) :=
    (Subgroup.mem_centralizer_singleton_iff.mp x.property).symm
  have hco : Nat.Coprime (orderOf g.val) (orderOf (x : G)) := by
    rw [order60_involution_order, hxG]
    rcases hp with rfl | rfl <;> decide
  have hprod := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco
  rw [order60_involution_order, hxG] at hprod
  have hne : g.val * (x : G) ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hprod
    rcases hp with rfl | rfl <;> omega
  rcases hO (g.val * (x : G)) hne with h | h | h <;>
    rcases hp with rfl | rfl <;> omega

/-- The centralizer of every actual involution has order at most four. -/
theorem order60_involution_centralizer_card_le (hG : Nat.card G = 60)
    (hO : HasIcosahedralElementOrders G) (g : NontrivialInvolution G) :
    Nat.card (Subgroup.centralizer ({g.val} : Set G)) ≤ 4 := by
  have hd := (Subgroup.centralizer ({g.val} : Set G)).card_subgroup_dvd_card
  rw [hG] at hd
  have h3 := order60_involution_centralizer_not_dvd hO g (Or.inl rfl)
  have h5 := order60_involution_centralizer_not_dvd hO g (Or.inr rfl)
  have hpos : 0 < Nat.card (Subgroup.centralizer ({g.val} : Set G)) := Nat.card_pos
  have hle : Nat.card (Subgroup.centralizer ({g.val} : Set G)) ≤ 60 := Nat.le_of_dvd (by decide) hd
  interval_cases hc : Nat.card (Subgroup.centralizer ({g.val} : Set G)) <;>
    norm_num [hc] at hd <;> norm_num [hc] at h3 <;> norm_num [hc] at h5 <;> omega

/-- Every actual involution lies in some actual Sylow two-subgroup. -/
theorem order60_involution_exists_sylow (g : NontrivialInvolution G) :
    ∃ P : Sylow 2 G, g.val ∈ P := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hc : Nat.card (Subgroup.zpowers g.val) = 2 ^ 1 := by
    rw [Nat.card_zpowers, order60_involution_order]
    norm_num
  obtain ⟨P, hP⟩ := (IsPGroup.of_card hc).exists_le_sylow
  exact ⟨P, hP (Subgroup.mem_zpowers g.val)⟩

/-- A Sylow two-subgroup containing an involution lies in its true centralizer. -/
theorem order60_sylowTwo_le_centralizer (hG : Nat.card G = 60)
    (hO : HasIcosahedralElementOrders G) (P : Sylow 2 G)
    (g : NontrivialInvolution G) (hg : g.val ∈ P) :
    (P : Subgroup G) ≤ Subgroup.centralizer ({g.val} : Set G) := by
  intro x hx
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (order60_sylowTwo_commute hG hO P ⟨x, hx⟩ ⟨g.val, hg⟩)

/-- Each Sylow two-subgroup through an involution equals its actual centralizer. -/
theorem order60_sylowTwo_eq_centralizer (hG : Nat.card G = 60)
    (hO : HasIcosahedralElementOrders G) (P : Sylow 2 G)
    (g : NontrivialInvolution G) (hg : g.val ∈ P) :
    (P : Subgroup G) = Subgroup.centralizer ({g.val} : Set G) := by
  exact Subgroup.eq_of_le_of_card_ge (order60_sylowTwo_le_centralizer hG hO P g hg)
    ((order60_sylowTwo_card hG P).symm ▸ order60_involution_centralizer_card_le hG hO g)

/-- Distinct Sylow two-subgroups share no nonidentity element. -/
theorem order60_sylowTwo_unique (hG : Nat.card G = 60) (hO : HasIcosahedralElementOrders G)
    (g : NontrivialInvolution G) {P Q : Sylow 2 G} (hP : g.val ∈ P) (hQ : g.val ∈ Q) : P = Q := by
  apply Sylow.ext
  exact (order60_sylowTwo_eq_centralizer hG hO P g hP).trans
    (order60_sylowTwo_eq_centralizer hG hO Q g hQ).symm

/-- The forgetful map from a nonidentity Sylow-two element to its actual involution. -/
def order60SylowInvolutionMap (hG : Nat.card G = 60) (hO : HasIcosahedralElementOrders G) :
    (Σ P : Sylow 2 G, {x : (P : Subgroup G) // x ≠ 1}) → NontrivialInvolution G :=
  fun a => ⟨a.2.val.val,
    (fun he => a.2.property (Subtype.ext he)),
    congrArg Subtype.val (order60_sylowTwo_mul_self hG hO a.1 a.2.val)⟩

/-- Uniqueness of the actual containing Sylow group makes this incidence map injective. -/
theorem order60SylowInvolutionMap_injective (hG : Nat.card G = 60)
    (hO : HasIcosahedralElementOrders G) :
    Function.Injective (order60SylowInvolutionMap hG hO) := by
  rintro ⟨P, x⟩ ⟨Q, y⟩ he
  have hval : (x.val : G) = (y.val : G) := congrArg Subtype.val he
  have hQ : (order60SylowInvolutionMap hG hO ⟨P, x⟩).val ∈ Q := by
    change (x.val : G) ∈ Q
    rw [hval]
    exact y.val.property
  have hP : P = Q := order60_sylowTwo_unique hG hO
    (order60SylowInvolutionMap hG hO ⟨P, x⟩) x.val.property hQ
  subst Q
  apply congrArg (Sigma.mk P)
  exact Subtype.ext (Subtype.ext hval)

/-- Every actual involution occurs in the incidence map. -/
theorem order60SylowInvolutionMap_surjective (hG : Nat.card G = 60)
    (hO : HasIcosahedralElementOrders G) :
    Function.Surjective (order60SylowInvolutionMap hG hO) := by
  intro g
  obtain ⟨P, hp⟩ := order60_involution_exists_sylow g
  let x : (P : Subgroup G) := ⟨g.val, hp⟩
  have hx : x ≠ 1 := fun he => g.property.1 (congrArg Subtype.val he)
  exact ⟨⟨P, ⟨x, hx⟩⟩, Subtype.ext rfl⟩

/-- Each order-four Sylow subgroup has precisely three nonidentity elements. -/
theorem order60_sylowTwo_nonidentity_card (hG : Nat.card G = 60) (P : Sylow 2 G) :
    Nat.card {x : (P : Subgroup G) // x ≠ 1} = 3 := by
  classical
  let : Fintype (P : Subgroup G) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x : (P : Subgroup G) => x = 1),
    Fintype.card_subtype_eq]
  have hc := order60_sylowTwo_card hG P
  rw [Nat.card_eq_fintype_card] at hc
  omega

/-- Fifteen genuine involutions partition into five disjoint three-element Sylow blocks. -/
theorem order60_sylowTwo_count (hG : Nat.card G = 60) (hO : HasIcosahedralElementOrders G)
    (hI : Nat.card (NontrivialInvolution G) = 15) : Nat.card (Sylow 2 G) = 5 := by
  classical
  let : Fintype (Sylow 2 G) := Fintype.ofFinite _
  let (P : Sylow 2 G) : Fintype {x : (P : Subgroup G) // x ≠ 1} := Fintype.ofFinite _
  have he := Nat.card_congr (Equiv.ofBijective (order60SylowInvolutionMap hG hO)
    ⟨order60SylowInvolutionMap_injective hG hO, order60SylowInvolutionMap_surjective hG hO⟩)
  have hcount : Nat.card (Σ P : Sylow 2 G, {x : (P : Subgroup G) // x ≠ 1}) =
      Nat.card (Sylow 2 G) * 3 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
    have hcard (P : Sylow 2 G) : Fintype.card {x : (P : Subgroup G) // x ≠ 1} = 3 := by
      simpa only [Nat.card_eq_fintype_card] using order60_sylowTwo_nonidentity_card hG P
    simp only [hcard, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [hcount, hI] at he
  omega

/-- No Sylow two-subgroup is normal once their actual number is five. -/
theorem order60_sylowTwo_not_normal (hG : Nat.card G = 60) (hO : HasIcosahedralElementOrders G)
    (hI : Nat.card (NontrivialInvolution G) = 15) (P : Sylow 2 G) : ¬P.Normal := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  intro hn
  let : Unique (Sylow 2 G) := Sylow.unique_of_normal P hn
  have hc : Nat.card (Sylow 2 G) = 1 := Nat.card_unique
  rw [order60_sylowTwo_count hG hO hI] at hc
  omega

/-- Every actual Sylow-two normalizer has exact order twelve. -/
theorem order60_sylowTwo_normalizer_card (hG : Nat.card G = 60) (hO : HasIcosahedralElementOrders G)
    (hI : Nat.card (NontrivialInvolution G) = 15) (P : Sylow 2 G) :
    Nat.card (Subgroup.normalizer (P : Set G)) = 12 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have he := (Subgroup.normalizer (P : Set G)).index_mul_card
  rw [hG, ← P.card_eq_index_normalizer, order60_sylowTwo_count hG hO hI] at he
  omega

/-- A normal subgroup of order six supplies a forbidden characteristic cyclic subgroup of order three. -/
theorem noCyclicNormal_subgroup_card_ne_six (hN : HasNoNontrivialCyclicNormalSubgroup G)
    (K : Subgroup G) [K.Normal] : Nat.card K ≠ 6 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro hK
  let P : Sylow 3 K := Classical.choice inferInstance
  have hv : (6 : ℕ).factorization 3 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.Prime.factorization (by decide : Nat.Prime 2),
      Nat.Prime.factorization (by decide : Nat.Prime 3)]
  have hP : Nat.card (P : Subgroup K) = 3 := by
    have he := P.card_eq_multiplicity
    rw [hK, hv] at he
    norm_num at he
    exact he
  have hidx : P.index = 2 := by
    have he := (P : Subgroup K).index_mul_card
    rw [hP, hK] at he
    omega
  have hd := P.card_dvd_index
  rw [hidx] at hd
  have hle : Nat.card (Sylow 3 K) ≤ 2 := Nat.le_of_dvd (by decide) hd
  have hm : Nat.card (Sylow 3 K) % 3 = 1 % 3 := card_sylow_modEq_one 3 K
  have hone : Nat.card (Sylow 3 K) = 1 := by omega
  let : Subsingleton (Sylow 3 K) := (Nat.card_eq_one_iff_unique.mp hone).1
  let : (P : Subgroup K).Characteristic := Sylow.characteristic_of_subsingleton P
  let L : Subgroup G := (P : Subgroup K).map K.subtype
  have hLN : L.Normal := inferInstance
  have hc : Nat.card L = 3 := by
    rw [show Nat.card L = Nat.card ((P : Subgroup K).map K.subtype) from rfl,
      Subgroup.card_map_of_injective K.subtype_injective]
    exact hP
  have hb := hN L hLN (isCyclic_of_prime_card hc)
  rw [hb, Subgroup.card_bot] at hc
  omega

/-- The genuine conjugation action on the actual Sylow two-subgroups. -/
def order60SylowTwoHom : G →* Equiv.Perm (Sylow 2 G) :=
  MulAction.toPermHom G (Sylow 2 G)

omit [Finite G] in
/-- Its kernel lies in each actual Sylow-two normalizer. -/
theorem order60SylowTwoHom_ker_le_normalizer (P : Sylow 2 G) :
    (order60SylowTwoHom (G := G)).ker ≤ Subgroup.normalizer (P : Set G) := by
  intro g hg
  apply Sylow.smul_eq_iff_mem_normalizer.mp
  exact congrArg (fun f : Equiv.Perm (Sylow 2 G) => f P) hg

/-- The degree-five Sylow action is faithful under the genuine algebraic branch hypotheses. -/
theorem order60SylowTwoHom_injective (hG : Nat.card G = 60)
    (hN : HasNoNontrivialCyclicNormalSubgroup G) (hO : HasIcosahedralElementOrders G)
    (hI : Nat.card (NontrivialInvolution G) = 15) :
    Function.Injective (order60SylowTwoHom (G := G)) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let P : Sylow 2 G := Classical.choice inferInstance
  let K := (order60SylowTwoHom (G := G)).ker
  have hle : K ≤ Subgroup.normalizer (P : Set G) := order60SylowTwoHom_ker_le_normalizer P
  have hcN := order60_sylowTwo_normalizer_card hG hO hI P
  have hd : Nat.card K ∣ 12 := by simpa only [hcN] using Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hbound : Nat.card K ≤ 12 := Nat.le_of_dvd (by decide) hd
  have hcases : Nat.card K = 1 ∨ Nat.card K = 2 ∨ Nat.card K = 3 ∨ Nat.card K = 4 ∨
      Nat.card K = 6 ∨ Nat.card K = 12 := by
    interval_cases hk : Nat.card K <;> norm_num [hk] at hd <;> omega
  apply (MonoidHom.ker_eq_bot_iff _).mp
  change K = ⊥
  rcases hcases with h1 | h2 | h3 | h4 | h6 | h12
  · exact K.eq_bot_of_card_eq h1
  · exact hN K inferInstance (isCyclic_of_prime_card h2)
  · let : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact hN K inferInstance (isCyclic_of_prime_card h3)
  · have hkp : IsPGroup 2 K := IsPGroup.of_card (show Nat.card K = 2 ^ 2 from by rw [h4]; norm_num)
    have hleP : K ≤ (P : Subgroup G) := hkp.le_sylow_of_normal P
    have he : K = (P : Subgroup G) := Subgroup.eq_of_le_of_card_ge hleP
      (by rw [h4, order60_sylowTwo_card hG P])
    have hn : P.Normal := he ▸ (inferInstance : K.Normal)
    exact (order60_sylowTwo_not_normal hG hO hI P hn).elim
  · exact (noCyclicNormal_subgroup_card_ne_six hN K h6).elim
  · have he : K = Subgroup.normalizer (P : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (by omega)
    have hn : (Subgroup.normalizer (P : Set G)).Normal := he ▸ (inferInstance : K.Normal)
    exact (order60_sylowTwo_not_normal hG hO hI P (P.normal_of_normalizer_normal hn)).elim

/-- Label the five genuine Sylow two-subgroups. -/
def order60SylowTwoEquiv (hG : Nat.card G = 60) (hO : HasIcosahedralElementOrders G)
    (hI : Nat.card (NontrivialInvolution G) = 15) : Sylow 2 G ≃ Fin 5 := by
  letI : Fintype (Sylow 2 G) := Fintype.ofFinite _
  exact Fintype.equivFinOfCardEq
    (by simpa only [Nat.card_eq_fintype_card] using order60_sylowTwo_count hG hO hI)

/-- The faithful labeled Sylow conjugation representation into S5. -/
def order60PermFiveHom (hG : Nat.card G = 60) (hO : HasIcosahedralElementOrders G)
    (hI : Nat.card (NontrivialInvolution G) = 15) : G →* Equiv.Perm (Fin 5) :=
  (order60SylowTwoEquiv hG hO hI).permCongrHom.toMonoidHom.comp order60SylowTwoHom

/-- The labeled genuine image is precisely A5. -/
theorem order60PermFiveHom_range_eq_alternating (hG : Nat.card G = 60)
    (hN : HasNoNontrivialCyclicNormalSubgroup G) (hO : HasIcosahedralElementOrders G)
    (hI : Nat.card (NontrivialInvolution G) = 15) :
    (order60PermFiveHom hG hO hI).range = alternatingGroup (Fin 5) := by
  let f := order60PermFiveHom hG hO hI
  have hf : Function.Injective f := (order60SylowTwoEquiv hG hO hI).permCongrHom.injective.comp
    (order60SylowTwoHom_injective hG hN hO hI)
  have hc : Nat.card f.range = 60 := by
    rw [← hG]
    exact Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm
  have hp : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have hi : f.range.index = 2 := by
    have he := f.range.index_mul_card
    rw [hc, hp] at he
    omega
  exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi

/-- An order-sixty group with the genuine icosahedral algebraic data is A5. -/
def groupOrder60EquivAlternatingFive (hG : Nat.card G = 60)
    (hN : HasNoNontrivialCyclicNormalSubgroup G) (hO : HasIcosahedralElementOrders G)
    (hI : Nat.card (NontrivialInvolution G) = 15) : G ≃* alternatingGroup (Fin 5) :=
  (MonoidHom.ofInjective ((order60SylowTwoEquiv hG hO hI).permCongrHom.injective.comp
    (order60SylowTwoHom_injective hG hN hO hI))).trans
    (MulEquiv.subgroupCongr (order60PermFiveHom_range_eq_alternating hG hN hO hI))

end Order60
end LowDimensionalTopology.Geometry.DiscreteGroups
