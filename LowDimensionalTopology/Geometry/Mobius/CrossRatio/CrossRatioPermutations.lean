module
public import LowDimensionalTopology.Geometry.Mobius.CrossRatio.CrossRatioGeometry

/-!
# Reindexing complex cross-ratios

The raw function directly reindexes z_i ↦ z_(sigma i).
It is well-defined independently of the quadruple and reverses composition
order. Inverse reindexing gives a genuine homomorphism on the complex ratio
domain with zero and one removed. Six transposition formulas and a concrete
noncommuting example distinguish these two conventions.
-/

@[expose] public section
noncomputable section
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Mobius

def quadrupleCrossRatio (z : Fin 4 → ExtendedComplex) : ℂ := extendedCrossRatio (z 0) (z 1) (z 2) (z 3)

theorem quadrupleDistinct_iff_injective (z : Fin 4 → ExtendedComplex) :
    QuadrupleDistinct (z 0) (z 1) (z 2) (z 3) ↔ Function.Injective z := by
  constructor
  · intro hd i j hij
    fin_cases i <;> fin_cases j <;> simp_all [QuadrupleDistinct]
  · intro h
    exact ⟨h.ne (by decide), h.ne (by decide), h.ne (by decide), h.ne (by decide), h.ne (by decide), h.ne (by decide)⟩

/-- The standard quadruple with cross-ratio lambda. -/
def canonicalCrossRatioQuadruple (z : ℂ) : Fin 4 → ExtendedComplex := ![(0 : ℂ), (1 : ℂ), z, ∞]

theorem canonicalCrossRatioQuadruple_distinct (z : ℂ) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    Function.Injective (canonicalCrossRatioQuadruple z) := by
  apply (quadrupleDistinct_iff_injective _).mp
  simp [QuadrupleDistinct, canonicalCrossRatioQuadruple, Ne.symm h0, Ne.symm h1]

theorem canonicalCrossRatioQuadruple_ratio (z : ℂ) : quadrupleCrossRatio (canonicalCrossRatioQuadruple z) = z :=
  extendedCrossRatio_zero_one_infty z

/-- The geometric raw permutation convention: the entries become z_(sigma i). -/
def rawCrossRatioPermutation (σ : Equiv.Perm (Fin 4)) (z : ℂ) : ℂ :=
  quadrupleCrossRatio (fun i => canonicalCrossRatioQuadruple z (σ i))

/-- The raw value depends only on the permutation and original cross-ratio, not on the quadruple. -/
theorem quadrupleCrossRatio_permutation (z : Fin 4 → ExtendedComplex) (hz : Function.Injective z)
    (σ : Equiv.Perm (Fin 4)) :
    quadrupleCrossRatio (fun i => z (σ i)) = rawCrossRatioPermutation σ (quadrupleCrossRatio z) := by
  have hd := (quadrupleDistinct_iff_injective z).mpr hz
  have h0 := extendedCrossRatio_ne_zero (z 0) (z 1) (z 2) (z 3) hd
  have h1 := extendedCrossRatio_ne_one (z 0) (z 1) (z 2) (z 3) hd
  have hc := (quadrupleDistinct_iff_injective _).mpr (canonicalCrossRatioQuadruple_distinct (quadrupleCrossRatio
    z) h0 h1)
  obtain ⟨f, hf0, hf1, hf2, hf3⟩ :=
    (extendedCrossRatio_eq_iff_exists_mobius (z 0) (z 1) (z 2) (z 3) _ _ _ _ hd hc).mp
      (canonicalCrossRatioQuadruple_ratio (quadrupleCrossRatio z)).symm
  have hf (i : Fin 4) : (f : Equiv.Perm ExtendedComplex) (z i) = canonicalCrossRatioQuadruple (quadrupleCrossRatio
    z) i := by
    fin_cases i
    · exact hf0
    · exact hf1
    · exact hf2
    · exact hf3
  have hi := extendedCrossRatio_mobius f (z (σ 0)) (z (σ 1)) (z (σ 2)) (z (σ 3))
  simp only [hf] at hi
  exact hi.symm

theorem rawCrossRatioPermutation_ne_zero_one (σ : Equiv.Perm (Fin 4)) (z : ℂ) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    rawCrossRatioPermutation σ z ≠ 0 ∧ rawCrossRatioPermutation σ z ≠ 1 := by
  have hz := (canonicalCrossRatioQuadruple_distinct z h0 h1).comp σ.injective
  have hd := (quadrupleDistinct_iff_injective _).mpr hz
  exact ⟨extendedCrossRatio_ne_zero _ _ _ _ hd, extendedCrossRatio_ne_one _ _ _ _ hd⟩

theorem rawCrossRatioPermutation_one (z : ℂ) : rawCrossRatioPermutation 1 z = z :=
  canonicalCrossRatioQuadruple_ratio z

/-- Correct order for the source's raw convention: reindexing gives an antihomomorphism. -/
theorem rawCrossRatioPermutation_comp (π σ : Equiv.Perm (Fin 4)) (z : ℂ) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    rawCrossRatioPermutation π (rawCrossRatioPermutation σ z) = rawCrossRatioPermutation (σ * π) z := by
  have h := quadrupleCrossRatio_permutation (fun i => canonicalCrossRatioQuadruple z (σ i))
    ((canonicalCrossRatioQuadruple_distinct z h0 h1).comp σ.injective) π
  exact h.symm

/-- Inverse reindexing supplies the left-action convention needed for a genuine homomorphism. -/
def crossRatioPermutation (σ : Equiv.Perm (Fin 4)) (z : ℂ) : ℂ := rawCrossRatioPermutation σ⁻¹ z

theorem crossRatioPermutation_mul (π σ : Equiv.Perm (Fin 4)) (z : ℂ) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    crossRatioPermutation (π * σ) z = crossRatioPermutation π (crossRatioPermutation σ z) := by
  unfold crossRatioPermutation
  rw [mul_inv_rev, rawCrossRatioPermutation_comp π⁻¹ σ⁻¹ z h0 h1]


/-- For the transposition of the first two positions. -/
theorem rawCrossRatioPermutation_swap01 (z : ℂ) : rawCrossRatioPermutation (Equiv.swap 0 1) z = 1 - z := by
  change extendedCrossRatio (1 : ℂ) (0 : ℂ) z ∞ = _
  rw [extendedCrossRatio_infty_fourth]
  simp

/-- The disjoint partner of the preceding transposition has the same ratio function. -/
theorem rawCrossRatioPermutation_swap23 (z : ℂ) : rawCrossRatioPermutation (Equiv.swap 2 3) z = 1 - z := by
  change extendedCrossRatio (0 : ℂ) (1 : ℂ) ∞ z = _
  rw [extendedCrossRatio_infty_third]
  simp

/-- For the transposition of the first and third positions. -/
theorem rawCrossRatioPermutation_swap02 (z : ℂ) : rawCrossRatioPermutation (Equiv.swap 0 2) z = z / (z - 1) := by
  change extendedCrossRatio z (1 : ℂ) (0 : ℂ) ∞ = _
  rw [extendedCrossRatio_infty_fourth]
  simp

theorem rawCrossRatioPermutation_swap13 (z : ℂ) : rawCrossRatioPermutation (Equiv.swap 1 3) z = z / (z - 1) := by
  change extendedCrossRatio (0 : ℂ) ∞ z (1 : ℂ) = _
  rw [extendedCrossRatio_infty_second]
  simp

/-- For the transposition of the first and fourth positions. -/
theorem rawCrossRatioPermutation_swap03 (z : ℂ) : rawCrossRatioPermutation (Equiv.swap 0 3) z = 1 / z := by
  change extendedCrossRatio ∞ (1 : ℂ) z (0 : ℂ) = _
  rw [extendedCrossRatio_infty_first]
  simp

theorem rawCrossRatioPermutation_swap12 (z : ℂ) : rawCrossRatioPermutation (Equiv.swap 1 2) z = 1 / z := by
  change extendedCrossRatio (0 : ℂ) z (1 : ℂ) ∞ = _
  rw [extendedCrossRatio_infty_fourth]
  simp

/-- A concrete pair of noncommuting transpositions exhibits the source order discrepancy. -/
theorem rawCrossRatioPermutation_wrong_order_values :
    rawCrossRatioPermutation (Equiv.swap 0 1) (rawCrossRatioPermutation (Equiv.swap 0 2) (3 : ℂ)) = -(1 : ℂ) / 2 ∧
      rawCrossRatioPermutation ((Equiv.swap 0 1) * (Equiv.swap 0 2)) (3 : ℂ) = (2 : ℂ) / 3 := by
  constructor
  · rw [rawCrossRatioPermutation_swap01, rawCrossRatioPermutation_swap02]
    norm_num
  · change extendedCrossRatio (3 : ℂ) (0 : ℂ) (1 : ℂ) ∞ = _
    rw [extendedCrossRatio_infty_fourth]
    norm_num

/-- The geometric literal homomorphism order fails for its raw indexing definition. -/
theorem rawCrossRatioPermutation_wrong_order_counterexample :
    rawCrossRatioPermutation (Equiv.swap 0 1) (rawCrossRatioPermutation (Equiv.swap 0 2) (3 : ℂ)) ≠
      rawCrossRatioPermutation ((Equiv.swap 0 1) * (Equiv.swap 0 2)) (3 : ℂ) := by
  rw [rawCrossRatioPermutation_wrong_order_values.1, rawCrossRatioPermutation_wrong_order_values.2]
  norm_num


/-- The actual possible complex cross-ratio values of distinct quadruples. -/
abbrev CrossRatioValue := {z : ℂ // z ≠ 0 ∧ z ≠ 1}

theorem crossRatioPermutation_one (z : ℂ) : crossRatioPermutation 1 z = z := by
  simpa only [crossRatioPermutation, inv_one] using rawCrossRatioPermutation_one z

theorem crossRatioPermutation_ne_zero_one (σ : Equiv.Perm (Fin 4)) (z : ℂ) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    crossRatioPermutation σ z ≠ 0 ∧ crossRatioPermutation σ z ≠ 1 :=
  rawCrossRatioPermutation_ne_zero_one σ⁻¹ z h0 h1

/-- Inverse reindexing acts bijectively on the punctured complex ratio domain. -/
def crossRatioPermutationEquiv (σ : Equiv.Perm (Fin 4)) : Equiv.Perm CrossRatioValue where
  toFun z := ⟨crossRatioPermutation σ z.val, crossRatioPermutation_ne_zero_one σ z.val z.property.1 z.property.2⟩
  invFun z := ⟨crossRatioPermutation σ⁻¹ z.val, crossRatioPermutation_ne_zero_one σ⁻¹ z.val z.property.1 z.property.2⟩
  left_inv z := by
    apply Subtype.ext
    change crossRatioPermutation σ⁻¹ (crossRatioPermutation σ z.val) = z.val
    rw [← crossRatioPermutation_mul σ⁻¹ σ z.val z.property.1 z.property.2,
      inv_mul_cancel, crossRatioPermutation_one]
  right_inv z := by
    apply Subtype.ext
    change crossRatioPermutation σ (crossRatioPermutation σ⁻¹ z.val) = z.val
    rw [← crossRatioPermutation_mul σ σ⁻¹ z.val z.property.1 z.property.2,
      mul_inv_cancel, crossRatioPermutation_one]

/-- A genuine homomorphism to permutations of the ratio domain, with the inverse-index convention explicit. -/
def crossRatioPermutationHom : Equiv.Perm (Fin 4) →* Equiv.Perm CrossRatioValue where
  toFun := crossRatioPermutationEquiv
  map_one' := by
    apply Equiv.ext
    intro z
    apply Subtype.ext
    exact crossRatioPermutation_one z.val
  map_mul' π σ := by
    apply Equiv.ext
    intro z
    apply Subtype.ext
    exact crossRatioPermutation_mul π σ z.val z.property.1 z.property.2

theorem crossRatioPermutationHom_apply (σ : Equiv.Perm (Fin 4)) (z : CrossRatioValue) :
    (crossRatioPermutationHom σ z).val = rawCrossRatioPermutation σ⁻¹ z.val := rfl

end LowDimensionalTopology.Geometry.Mobius
