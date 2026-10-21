module
public import LowDimensionalTopology.Geometry.Mobius.CrossRatio.CrossRatioPermutations
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Perm

/-!
# The geometric anharmonic group
the actual Möbius stabilizer of zero, one and infinity,
its six finite formulas, and the S₄ surjection with Klein-four kernel.
The action uses inverse reindexing, agreeing with the explicit convention
correction in CrossRatioPermutations.
-/

@[expose] public section
noncomputable section
open scoped OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Mobius

/-- Zero, one and infinity, indexed without identifying any two of the points. -/
def standardTriplePoint : Fin 3 → ExtendedComplex := ![(0 : ℂ), (1 : ℂ), ∞]

theorem standardTriplePoint_injective : Function.Injective standardTriplePoint := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [standardTriplePoint]

/-- The three distinguished points fixed setwise. -/
def standardTripleSet : Set ExtendedComplex := Set.range standardTriplePoint

/-- The actual Möbius subgroup permuting zero, one and infinity. -/
abbrev zeroOneInftyStabilizer : Subgroup complexMobiusGroup :=
  MulAction.stabilizer complexMobiusGroup standardTripleSet

/-- The three-point set, identified with its three distinct indices. -/
def standardTripleEquiv : Fin 3 ≃ standardTripleSet :=
  Equiv.ofInjective standardTriplePoint standardTriplePoint_injective

/-- The action of the geometric stabilizer on its actual three points. -/
def zeroOneInftyPermutationHom : zeroOneInftyStabilizer →* Equiv.Perm (Fin 3) :=
  standardTripleEquiv.symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom zeroOneInftyStabilizer standardTripleSet)

/-- Evaluation of the permutation action agrees with the underlying complex Möbius action. -/
theorem zeroOneInftyPermutationHom_apply (f : zeroOneInftyStabilizer) (i : Fin 3) :
    standardTriplePoint (zeroOneInftyPermutationHom f i) =
      (f.val : Equiv.Perm ExtendedComplex) (standardTriplePoint i) := by
  change (standardTripleEquiv (standardTripleEquiv.symm (f • standardTripleEquiv i))).val = _
  rw [standardTripleEquiv.apply_symm_apply]
  rfl

/-- Sharp triple transitivity makes the three-point permutation action faithful. -/
theorem zeroOneInftyPermutationHom_injective : Function.Injective zeroOneInftyPermutationHom := by
  intro f g h
  apply Subtype.ext
  apply mobius_eq_of_agree_triple f.val g.val (0 : ℂ) (1 : ℂ) ∞ (by simp [TripleDistinct])
  all_goals
    have hp (i : Fin 3) := congrArg (fun p : Equiv.Perm (Fin 3) => standardTriplePoint (p i)) h
    simp only [zeroOneInftyPermutationHom_apply] at hp
  · exact hp 0
  · exact hp 1
  · exact hp 2

/-- Every permutation of the three distinguished points comes from a geometric Möbius transformation. -/
theorem zeroOneInftyPermutationHom_surjective : Function.Surjective zeroOneInftyPermutationHom := by
  intro σ
  have hD : TripleDistinct (standardTriplePoint (σ 0)) (standardTriplePoint (σ 1)) (standardTriplePoint (σ 2)) := by
    apply And.intro
    · exact standardTriplePoint_injective.ne (σ.injective.ne (by decide))
    · exact ⟨standardTriplePoint_injective.ne (σ.injective.ne (by decide)),
        standardTriplePoint_injective.ne (σ.injective.ne (by decide))⟩
  obtain ⟨f, hf0, hf1, hf2⟩ :=
    (mobius_existsUnique_map_triple (0 : ℂ) (1 : ℂ) ∞ _ _ _ (by simp [TripleDistinct]) hD).exists
  have hf (i : Fin 3) : (f : Equiv.Perm ExtendedComplex) (standardTriplePoint i) = standardTriplePoint (σ i) := by
    fin_cases i
    · exact hf0
    · exact hf1
    · exact hf2
  have hmem : f ∈ zeroOneInftyStabilizer := by
    change (f : Equiv.Perm ExtendedComplex) '' Set.range standardTriplePoint = Set.range standardTriplePoint
    rw [← Set.range_comp']
    simp only [hf]
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨σ i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨σ⁻¹ i, by simp⟩
  refine ⟨⟨f, hmem⟩, ?_⟩
  apply Equiv.ext
  intro i
  apply standardTriplePoint_injective
  rw [zeroOneInftyPermutationHom_apply, hf]

/-- The geometric stabilizer of zero, one and infinity is isomorphic to S₃. -/
def zeroOneInftyEquivPermThree : zeroOneInftyStabilizer ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective zeroOneInftyPermutationHom
    ⟨zeroOneInftyPermutationHom_injective, zeroOneInftyPermutationHom_surjective⟩

/-- The geometric three-point stabilizer has exactly six elements. -/
theorem zeroOneInftyStabilizer_card : Nat.card zeroOneInftyStabilizer = 6 := by
  rw [Nat.card_congr zeroOneInftyEquivPermThree.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num

def crossRatioPairing (i : Fin 3) : Equiv.Perm (Fin 4) :=
  ![Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 3 * Equiv.swap 1 2,
    Equiv.swap 0 1 * Equiv.swap 2 3] i

def crossRatioPairingIndex (σ : Equiv.Perm (Fin 4)) (i : Fin 3) : Fin 3 :=
  if σ * crossRatioPairing i * σ⁻¹ = crossRatioPairing 0 then 0
  else if σ * crossRatioPairing i * σ⁻¹ = crossRatioPairing 1 then 1 else 2

theorem crossRatioPairing_injective : Function.Injective crossRatioPairing := by decide

theorem crossRatioPairingIndex_conjugation (σ : Equiv.Perm (Fin 4)) (i : Fin 3) :
    σ * crossRatioPairing i * σ⁻¹ = crossRatioPairing (crossRatioPairingIndex σ i) := by
  revert σ i
  decide

theorem crossRatioPairingIndex_bijective (σ : Equiv.Perm (Fin 4)) :
    Function.Bijective (crossRatioPairingIndex σ) := by
  revert σ
  decide


noncomputable def crossRatioPairingPerm (σ : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (crossRatioPairingIndex σ) (crossRatioPairingIndex_bijective σ)

noncomputable def crossRatioPairingHom : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 3) where
  toFun := crossRatioPairingPerm
  map_one' := by
    apply Equiv.ext
    intro i
    apply crossRatioPairing_injective
    change crossRatioPairing (crossRatioPairingIndex 1 i) = crossRatioPairing i
    rw [← crossRatioPairingIndex_conjugation]
    simp
  map_mul' π σ := by
    apply Equiv.ext
    intro i
    apply crossRatioPairing_injective
    change crossRatioPairing (crossRatioPairingIndex (π * σ) i) =
      crossRatioPairing (crossRatioPairingIndex π (crossRatioPairingIndex σ i))
    rw [← crossRatioPairingIndex_conjugation (π * σ) i,
      ← crossRatioPairingIndex_conjugation π (crossRatioPairingIndex σ i),
      ← crossRatioPairingIndex_conjugation σ i]
    group

theorem crossRatioPairingHom_surjective : Function.Surjective crossRatioPairingHom := by
  have h : ∀ τ : Equiv.Perm (Fin 3), ∃ σ : Equiv.Perm (Fin 4), ∀ i,
      crossRatioPairingIndex σ i = τ i := by decide
  intro τ
  obtain ⟨σ, hσ⟩ := h τ
  exact ⟨σ, Equiv.ext hσ⟩

theorem crossRatioPairingIndex_eq_id_iff (σ : Equiv.Perm (Fin 4)) :
    (∀ i, crossRatioPairingIndex σ i = i) ↔
      σ = 1 ∨ σ = crossRatioPairing 0 ∨ σ = crossRatioPairing 1 ∨ σ = crossRatioPairing 2 := by
  revert σ
  decide


theorem crossRatioPairing_mem_mul (σ τ : Equiv.Perm (Fin 4)) :
    (σ = 1 ∨ σ = crossRatioPairing 0 ∨ σ = crossRatioPairing 1 ∨ σ = crossRatioPairing 2) →
    (τ = 1 ∨ τ = crossRatioPairing 0 ∨ τ = crossRatioPairing 1 ∨ τ = crossRatioPairing 2) →
    (σ * τ = 1 ∨ σ * τ = crossRatioPairing 0 ∨ σ * τ = crossRatioPairing 1 ∨ σ * τ = crossRatioPairing 2) := by
  revert σ τ
  decide

theorem crossRatioPairing_mem_inv (σ : Equiv.Perm (Fin 4)) :
    (σ = 1 ∨ σ = crossRatioPairing 0 ∨ σ = crossRatioPairing 1 ∨ σ = crossRatioPairing 2) →
    (σ⁻¹ = 1 ∨ σ⁻¹ = crossRatioPairing 0 ∨ σ⁻¹ = crossRatioPairing 1 ∨ σ⁻¹ = crossRatioPairing 2) := by
  revert σ
  decide

/-- The identity and the three double transpositions, as an actual subgroup of S₄. -/
def crossRatioKleinFour : Subgroup (Equiv.Perm (Fin 4)) where
  carrier σ := σ = 1 ∨ σ = crossRatioPairing 0 ∨ σ = crossRatioPairing 1 ∨ σ = crossRatioPairing 2
  one_mem' := Or.inl rfl
  mul_mem' {σ τ} hσ hτ := crossRatioPairing_mem_mul σ τ hσ hτ
  inv_mem' {σ} hσ := crossRatioPairing_mem_inv σ hσ

theorem crossRatioPairingHom_kernel : crossRatioPairingHom.ker = crossRatioKleinFour := by
  ext σ
  change crossRatioPairingPerm σ = 1 ↔ _
  rw [Equiv.ext_iff]
  change (∀ i, crossRatioPairingIndex σ i = i) ↔ _
  exact crossRatioPairingIndex_eq_id_iff σ

theorem crossRatioKleinFour_card : Nat.card crossRatioKleinFour = 4 := by
  let : DecidablePred (fun σ : Equiv.Perm (Fin 4) => σ ∈ crossRatioKleinFour) :=
    fun σ => inferInstanceAs (Decidable (σ = 1 ∨ σ = crossRatioPairing 0 ∨ σ = crossRatioPairing 1 ∨ σ =
      crossRatioPairing 2))
  rw [Nat.card_eq_fintype_card]
  decide


/-- The genuine inverse-index homomorphism from S₄ into the actual geometric three-point stabilizer. -/
def crossRatioStabilizerHom : Equiv.Perm (Fin 4) →* zeroOneInftyStabilizer :=
  zeroOneInftyEquivPermThree.symm.toMonoidHom.comp crossRatioPairingHom

theorem crossRatioStabilizerHom_surjective : Function.Surjective crossRatioStabilizerHom :=
  zeroOneInftyEquivPermThree.symm.surjective.comp crossRatioPairingHom_surjective

theorem crossRatioStabilizerHom_kernel : crossRatioStabilizerHom.ker = crossRatioKleinFour := by
  ext σ
  have h : crossRatioStabilizerHom σ = 1 ↔ crossRatioPairingHom σ = 1 := by
    constructor
    · intro h
      have he := congrArg zeroOneInftyEquivPermThree h
      simpa only [crossRatioStabilizerHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply, map_one] using he
    · intro h
      change zeroOneInftyEquivPermThree.symm (crossRatioPairingHom σ) = 1
      rw [h, map_one]
  exact h.trans (show crossRatioPairingHom σ = 1 ↔ σ ∈ crossRatioKleinFour by
    rw [← crossRatioPairingHom_kernel]; rfl)

/-- The same homomorphism, viewed in the ambient actual Möbius group. -/
def crossRatioMobiusHom : Equiv.Perm (Fin 4) →* complexMobiusGroup :=
  zeroOneInftyStabilizer.subtype.comp crossRatioStabilizerHom

theorem crossRatioMobiusHom_standard (σ : Equiv.Perm (Fin 4)) (i : Fin 3) :
    (crossRatioMobiusHom σ : Equiv.Perm ExtendedComplex) (standardTriplePoint i) =
      standardTriplePoint (crossRatioPairingHom σ i) := by
  have h := zeroOneInftyPermutationHom_apply (crossRatioStabilizerHom σ) i
  have he : zeroOneInftyPermutationHom (crossRatioStabilizerHom σ) = crossRatioPairingHom σ :=
    zeroOneInftyEquivPermThree.apply_symm_apply _
  rw [he] at h
  exact h.symm

/-- The geometric element whose finite expression is one minus z. -/
def crossRatioOneMinus : complexMobiusGroup :=
  mobiusMatrixProjection (coefficientMatrix (-1) 1 0 1 (by norm_num))

theorem crossRatioOneMinus_coe (z : ℂ) :
    (crossRatioOneMinus : Equiv.Perm ExtendedComplex) z = ((1 - z : ℂ) : ExtendedComplex) := by
  simp only [crossRatioOneMinus, mobiusMatrixProjection_apply, fractionalLinear_coe, coefficientMatrix]
  simp
  ring

def crossRatioQuotient : complexMobiusGroup :=
  mobiusMatrixProjection (coefficientMatrix 1 0 1 (-1) (by norm_num))

theorem crossRatioQuotient_coe (z : ℂ) (hz : z ≠ 1) :
    (crossRatioQuotient : Equiv.Perm ExtendedComplex) z = ((z / (z - 1) : ℂ) : ExtendedComplex) := by
  have hd : z + -1 ≠ 0 := by simpa only [← sub_eq_add_neg] using sub_ne_zero.mpr hz
  simp [crossRatioQuotient, mobiusMatrixProjection_apply, fractionalLinear_coe, coefficientMatrix,
    sub_eq_add_neg, hd]

def crossRatioReciprocal : complexMobiusGroup :=
  mobiusMatrixProjection (coefficientMatrix 0 1 1 0 (by norm_num))

theorem crossRatioReciprocal_coe (z : ℂ) (hz : z ≠ 0) :
    (crossRatioReciprocal : Equiv.Perm ExtendedComplex) z = ((1 / z : ℂ) : ExtendedComplex) := by
  simp [crossRatioReciprocal, mobiusMatrixProjection_apply, fractionalLinear_coe, coefficientMatrix, hz]

theorem crossRatioOneMinus_standard (i : Fin 3) :
    (crossRatioOneMinus : Equiv.Perm ExtendedComplex) (standardTriplePoint i) =
      standardTriplePoint (Equiv.swap 0 1 i) := by
  fin_cases i <;> norm_num [standardTriplePoint, crossRatioOneMinus, mobiusMatrixProjection_apply,
    fractionalLinear_coe, fractionalLinear_infty, coefficientMatrix, Equiv.swap_apply_def]

theorem crossRatioQuotient_standard (i : Fin 3) :
    (crossRatioQuotient : Equiv.Perm ExtendedComplex) (standardTriplePoint i) =
      standardTriplePoint (Equiv.swap 1 2 i) := by
  fin_cases i <;> norm_num [standardTriplePoint, crossRatioQuotient, mobiusMatrixProjection_apply,
    fractionalLinear_coe, fractionalLinear_infty, coefficientMatrix, Equiv.swap_apply_def]

theorem crossRatioReciprocal_standard (i : Fin 3) :
    (crossRatioReciprocal : Equiv.Perm ExtendedComplex) (standardTriplePoint i) =
      standardTriplePoint (Equiv.swap 0 2 i) := by
  fin_cases i <;> norm_num [standardTriplePoint, crossRatioReciprocal, mobiusMatrixProjection_apply,
    fractionalLinear_coe, fractionalLinear_infty, coefficientMatrix, Equiv.swap_apply_def]

theorem crossRatioPairingHom_swap01 : crossRatioPairingHom (Equiv.swap 0 1) = Equiv.swap 0 1 := by
  apply Equiv.ext
  intro i
  fin_cases i <;> decide

theorem crossRatioPairingHom_swap02 : crossRatioPairingHom (Equiv.swap 0 2) = Equiv.swap 1 2 := by
  apply Equiv.ext
  intro i
  fin_cases i <;> decide

theorem crossRatioPairingHom_swap03 : crossRatioPairingHom (Equiv.swap 0 3) = Equiv.swap 0 2 := by
  apply Equiv.ext
  intro i
  fin_cases i <;> decide

theorem crossRatioMobiusHom_eq_of_standard (σ : Equiv.Perm (Fin 4)) (f : complexMobiusGroup)
    (τ : Equiv.Perm (Fin 3)) (hσ : crossRatioPairingHom σ = τ)
    (hf : ∀ i, (f : Equiv.Perm ExtendedComplex) (standardTriplePoint i) = standardTriplePoint (τ i)) :
    crossRatioMobiusHom σ = f := by
  have he (i : Fin 3) : (crossRatioMobiusHom σ : Equiv.Perm ExtendedComplex) (standardTriplePoint i) =
      (f : Equiv.Perm ExtendedComplex) (standardTriplePoint i) := by
    rw [crossRatioMobiusHom_standard, hσ, hf]
  exact mobius_eq_of_agree_triple _ _ (0 : ℂ) (1 : ℂ) ∞ (by simp [TripleDistinct]) (he 0) (he 1) (he 2)

theorem crossRatioMobiusHom_swap01 : crossRatioMobiusHom (Equiv.swap 0 1) = crossRatioOneMinus :=
  crossRatioMobiusHom_eq_of_standard _ _ _ crossRatioPairingHom_swap01 crossRatioOneMinus_standard

theorem crossRatioMobiusHom_swap02 : crossRatioMobiusHom (Equiv.swap 0 2) = crossRatioQuotient :=
  crossRatioMobiusHom_eq_of_standard _ _ _ crossRatioPairingHom_swap02 crossRatioQuotient_standard

theorem crossRatioMobiusHom_swap03 : crossRatioMobiusHom (Equiv.swap 0 3) = crossRatioReciprocal :=
  crossRatioMobiusHom_eq_of_standard _ _ _ crossRatioPairingHom_swap03 crossRatioReciprocal_standard

/-- Six representatives for the action on the three pairings. -/
def crossRatioPermutationWord (i : Fin 6) : Equiv.Perm (Fin 4) :=
  ![1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 3,
    Equiv.swap 0 1 * Equiv.swap 0 2, Equiv.swap 0 2 * Equiv.swap 0 1] i

theorem crossRatioPermutationWord_cover (σ : Equiv.Perm (Fin 4)) :
    ∃ i, crossRatioPairingHom σ = crossRatioPairingHom (crossRatioPermutationWord i) := by
  have h : ∀ τ : Equiv.Perm (Fin 4), ∃ i : Fin 6, ∀ j,
      crossRatioPairingIndex τ j = crossRatioPairingIndex (crossRatioPermutationWord i) j := by decide
  obtain ⟨i, hi⟩ := h σ
  exact ⟨i, Equiv.ext hi⟩

theorem rawCrossRatioPermutation_pairing (i : Fin 3) (z : ℂ) :
    rawCrossRatioPermutation (crossRatioPairing i) z = z := by
  fin_cases i
  · change extendedCrossRatio z ∞ (0 : ℂ) (1 : ℂ) = z
    rw [extendedCrossRatio_infty_second]
    simp
  · change extendedCrossRatio ∞ z (1 : ℂ) (0 : ℂ) = z
    rw [extendedCrossRatio_infty_first]
    simp
  · change extendedCrossRatio (1 : ℂ) (0 : ℂ) ∞ z = z
    rw [extendedCrossRatio_infty_third]
    simp

theorem crossRatioKleinFour_le_value_kernel : crossRatioKleinFour ≤ crossRatioPermutationHom.ker := by
  intro σ hσ
  change crossRatioPermutationHom σ = 1
  apply Equiv.ext
  intro z
  apply Subtype.ext
  change rawCrossRatioPermutation σ⁻¹ z.val = z.val
  have hi : σ⁻¹ ∈ crossRatioKleinFour := crossRatioKleinFour.inv_mem hσ
  rcases hi with h | h | h | h
  · rw [h, rawCrossRatioPermutation_one]
  · rw [h, rawCrossRatioPermutation_pairing]
  · rw [h, rawCrossRatioPermutation_pairing]
  · rw [h, rawCrossRatioPermutation_pairing]

theorem crossRatioPermutationHom_eq_of_pairing_eq (σ τ : Equiv.Perm (Fin 4))
    (h : crossRatioPairingHom σ = crossRatioPairingHom τ) :
    crossRatioPermutationHom σ = crossRatioPermutationHom τ := by
  have hk : σ * τ⁻¹ ∈ crossRatioKleinFour := by
    rw [← crossRatioPairingHom_kernel]
    change crossRatioPairingHom (σ * τ⁻¹) = 1
    simp [h]
  have hv := crossRatioKleinFour_le_value_kernel hk
  change crossRatioPermutationHom (σ * τ⁻¹) = 1 at hv
  rw [map_mul, map_inv, mul_inv_eq_one] at hv
  exact hv

theorem crossRatioMobiusHom_eq_of_pairing_eq (σ τ : Equiv.Perm (Fin 4))
    (h : crossRatioPairingHom σ = crossRatioPairingHom τ) :
    crossRatioMobiusHom σ = crossRatioMobiusHom τ := by
  exact congrArg (fun p => (zeroOneInftyEquivPermThree.symm p).val) h

/-- Compatibility of the geometric action and the corrected ratio action. -/
def CrossRatioActionCompatible (σ : Equiv.Perm (Fin 4)) : Prop :=
  ∀ z : CrossRatioValue, (crossRatioMobiusHom σ : Equiv.Perm ExtendedComplex) (z.val : ExtendedComplex) =
    ((crossRatioPermutationHom σ z).val : ExtendedComplex)

theorem crossRatioActionCompatible_one : CrossRatioActionCompatible 1 := by
  intro z
  simp

theorem CrossRatioActionCompatible.mul {π σ : Equiv.Perm (Fin 4)}
    (hπ : CrossRatioActionCompatible π) (hσ : CrossRatioActionCompatible σ) :
    CrossRatioActionCompatible (π * σ) := by
  intro z
  change ((crossRatioMobiusHom (π * σ)).val) ↑z.val = _
  rw [map_mul]
  change (crossRatioMobiusHom π : Equiv.Perm ExtendedComplex)
      ((crossRatioMobiusHom σ : Equiv.Perm ExtendedComplex) ↑z.val) = _
  rw [hσ z, hπ (crossRatioPermutationHom σ z), map_mul]
  rfl

theorem crossRatioActionCompatible_swap01 : CrossRatioActionCompatible (Equiv.swap 0 1) := by
  intro z
  rw [crossRatioMobiusHom_swap01, crossRatioOneMinus_coe, crossRatioPermutationHom_apply]
  simp only [Equiv.swap_inv, rawCrossRatioPermutation_swap01]

theorem crossRatioActionCompatible_swap02 : CrossRatioActionCompatible (Equiv.swap 0 2) := by
  intro z
  rw [crossRatioMobiusHom_swap02, crossRatioQuotient_coe z.val z.property.2, crossRatioPermutationHom_apply]
  simp only [Equiv.swap_inv, rawCrossRatioPermutation_swap02]

theorem crossRatioActionCompatible_swap03 : CrossRatioActionCompatible (Equiv.swap 0 3) := by
  intro z
  rw [crossRatioMobiusHom_swap03, crossRatioReciprocal_coe z.val z.property.1, crossRatioPermutationHom_apply]
  simp only [Equiv.swap_inv, rawCrossRatioPermutation_swap03]

theorem crossRatioActionCompatible_word (i : Fin 6) : CrossRatioActionCompatible (crossRatioPermutationWord i) := by
  fin_cases i
  · exact crossRatioActionCompatible_one
  · exact crossRatioActionCompatible_swap01
  · exact crossRatioActionCompatible_swap02
  · exact crossRatioActionCompatible_swap03
  · exact crossRatioActionCompatible_swap01.mul crossRatioActionCompatible_swap02
  · exact crossRatioActionCompatible_swap02.mul crossRatioActionCompatible_swap01

/-- The geometric S₄ homomorphism acts by the source formula with inverse reindexing. -/
theorem crossRatioMobiusHom_apply (σ : Equiv.Perm (Fin 4)) (z : CrossRatioValue) :
    (crossRatioMobiusHom σ : Equiv.Perm ExtendedComplex) (z.val : ExtendedComplex) =
      (rawCrossRatioPermutation σ⁻¹ z.val : ExtendedComplex) := by
  obtain ⟨i, hi⟩ := crossRatioPermutationWord_cover σ
  have hm := crossRatioMobiusHom_eq_of_pairing_eq σ _ hi
  have hv := crossRatioPermutationHom_eq_of_pairing_eq σ _ hi
  rw [← crossRatioPermutationHom_apply, hm, hv]
  exact crossRatioActionCompatible_word i z

/-- The six finite rational expressions; values zero and one are excluded at evaluation. -/
def crossRatioSixFunctions (i : Fin 6) (z : ℂ) : ℂ :=
  ![z, 1 - z, z / (z - 1), 1 / z, 1 / (1 - z), (z - 1) / z] i

theorem crossRatioPermutation_word (i : Fin 6) (z : ℂ) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    crossRatioPermutation (crossRatioPermutationWord i) z = crossRatioSixFunctions i z := by
  fin_cases i
  · exact crossRatioPermutation_one z
  · exact rawCrossRatioPermutation_swap01 z
  · exact rawCrossRatioPermutation_swap02 z
  · exact rawCrossRatioPermutation_swap03 z
  · change crossRatioPermutation (Equiv.swap 0 1 * Equiv.swap 0 2) z = 1 / (1 - z)
    rw [crossRatioPermutation_mul _ _ z h0 h1]
    simp only [crossRatioPermutation, Equiv.swap_inv, rawCrossRatioPermutation_swap01, rawCrossRatioPermutation_swap02]
    field_simp [h0, sub_ne_zero.mpr h1]
    ring
  · change crossRatioPermutation (Equiv.swap 0 2 * Equiv.swap 0 1) z = (z - 1) / z
    rw [crossRatioPermutation_mul _ _ z h0 h1]
    simp only [crossRatioPermutation, Equiv.swap_inv, rawCrossRatioPermutation_swap01, rawCrossRatioPermutation_swap02]
    field_simp [h0, sub_ne_zero.mpr h1]
    ring

theorem crossRatioMobiusHom_word (i : Fin 6) (z : ℂ) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    (crossRatioMobiusHom (crossRatioPermutationWord i) : Equiv.Perm ExtendedComplex) (z : ExtendedComplex) =
      (crossRatioSixFunctions i z : ExtendedComplex) := by
  have h := crossRatioMobiusHom_apply (crossRatioPermutationWord i) ⟨z, h0, h1⟩
  change _ = (crossRatioPermutation (crossRatioPermutationWord i) z : ExtendedComplex) at h
  rw [crossRatioPermutation_word i z h0 h1] at h
  exact h

/-- Every geometric element is one of the six rational maps, with its action on the distinguished points also fixed. -/
theorem zeroOneInftyStabilizer_six_functions (f : zeroOneInftyStabilizer) :
    ∃ i : Fin 6, ∀ z : ℂ, z ≠ 0 → z ≠ 1 →
      (f.val : Equiv.Perm ExtendedComplex) (z : ExtendedComplex) =
        (crossRatioSixFunctions i z : ExtendedComplex) := by
  obtain ⟨σ, hσ⟩ := crossRatioStabilizerHom_surjective f
  obtain ⟨i, hi⟩ := crossRatioPermutationWord_cover σ
  refine ⟨i, ?_⟩
  intro z h0 h1
  rw [← hσ]
  change (crossRatioMobiusHom σ : Equiv.Perm ExtendedComplex) ↑z = _
  rw [crossRatioMobiusHom_eq_of_pairing_eq σ _ hi]
  exact crossRatioMobiusHom_word i z h0 h1

/-- With inverse reindexing explicitly supplying the homomorphism convention. -/
theorem crossRatioStabilizerHom_surjective_and_ker : Function.Surjective crossRatioStabilizerHom ∧
    crossRatioStabilizerHom.ker = crossRatioKleinFour :=
  ⟨crossRatioStabilizerHom_surjective, crossRatioStabilizerHom_kernel⟩

end LowDimensionalTopology.Geometry.Mobius
