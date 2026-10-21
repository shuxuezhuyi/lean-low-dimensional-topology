/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto

/-!
Mathlib's real quaternions are related explicitly to the standard complex-matrix model.
The coordinate, group, basis, conjugation, inverse and determinant statements use that identification.
-/

@[expose] public section

namespace LowDimensionalTopology.Geometry.Auxiliary.Algebra

/-- real Hamilton quaternions, using Mathlib's algebra. -/
abbrev RealQuaternion := Quaternion ℝ

/-- The first imaginary unit. -/
def quaternionI : RealQuaternion := ⟨0, 1, 0, 0⟩
/-- The second imaginary unit. -/
def quaternionJ : RealQuaternion := ⟨0, 0, 1, 0⟩
/-- The third imaginary unit. -/
def quaternionK : RealQuaternion := ⟨0, 0, 0, 1⟩

/-- equation: two complex coordinates. -/
def complexPair (z w : ℂ) : RealQuaternion := ⟨z.re, z.im, w.re, w.im⟩

/-- equation: the coordinates agree with the embedded-complex expression. -/
theorem complexPair_eq (z w : ℂ) :
    complexPair z w = (z : RealQuaternion) + (w : RealQuaternion) * quaternionJ := by
  ext <;> simp [complexPair, quaternionJ]

/-- existence and uniqueness of the two complex coordinates. -/
def complexPairEquiv : ℂ × ℂ ≃ RealQuaternion where
  toFun zw := complexPair zw.1 zw.2
  invFun q := (⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩)
  left_inv zw := by rcases zw with ⟨z,w⟩; rfl
  right_inv q := by rfl

/-- multiplication in complex coordinates. -/
theorem complexPair_mul (z₁ w₁ z₂ w₂ : ℂ) :
    complexPair z₁ w₁ * complexPair z₂ w₂ =
      complexPair (z₁ * z₂ - w₁ * star w₂) (z₁ * w₂ + w₁ * star z₂) := by
  ext <;> simp [complexPair] <;> ring

/-- exchanging the second imaginary unit with a complex scalar. -/
theorem quaternionJ_mul_complex (z : ℂ) :
    quaternionJ * (z : RealQuaternion) = (star z : ℂ) * quaternionJ := by
  ext <;> simp [quaternionJ]

/-- conjugation in complex coordinates. -/
theorem star_complexPair (z w : ℂ) :
    star (complexPair z w) = complexPair (star z) (-w) := by
  ext <;> simp [complexPair]

/-- squared norm in complex coordinates. -/
theorem normSq_complexPair (z w : ℂ) :
    Quaternion.normSq (complexPair z w) = Complex.normSq z + Complex.normSq w := by
  simp [Quaternion.normSq_def', Complex.normSq_apply, complexPair]
  ring

/-- multiplication by the conjugate. -/
theorem complexPair_mul_star (z w : ℂ) :
    complexPair z w * complexPair (star z) (-w) =
      ((Complex.normSq z + Complex.normSq w : ℝ) : RealQuaternion) := by
  rw [← star_complexPair, Quaternion.self_mul_star, normSq_complexPair]

/-- The inverse formula; the identity also holds at zero in Lean. -/
theorem complexPair_inverse (z w : ℂ) :
    (complexPair z w)⁻¹ =
      (Complex.normSq z + Complex.normSq w)⁻¹ • complexPair (star z) (-w) := by
  change (Quaternion.normSq (complexPair z w))⁻¹ • star (complexPair z w) = _
  rw [normSq_complexPair, star_complexPair]

/-- equation: the complex matrix model. -/
def quaternionMatrix (q : RealQuaternion) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩;
    -star (⟨q.imJ, q.imK⟩ : ℂ), star (⟨q.re, q.imI⟩ : ℂ)]

/-- equations –: matching the two descriptions. -/
theorem quaternionMatrix_complexPair (z w : ℂ) :
    quaternionMatrix (complexPair z w) = !![z, w; -star w, star z] := rfl

/-- The matrix representation identifies no distinct quaternions. -/
theorem quaternionMatrix_injective : Function.Injective quaternionMatrix := by
  intro q r h
  have hz := congrArg (fun A => A 0 0) h
  have hw := congrArg (fun A => A 0 1) h
  ext
  · exact congrArg Complex.re hz
  · exact congrArg Complex.im hz
  · exact congrArg Complex.re hw
  · exact congrArg Complex.im hw

/-- The representation preserves addition. -/
theorem quaternionMatrix_add (q r : RealQuaternion) :
    quaternionMatrix (q + r) = quaternionMatrix q + quaternionMatrix r := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [quaternionMatrix] <;> ring

/-- The representation preserves multiplication. -/
theorem quaternionMatrix_mul (q r : RealQuaternion) :
    quaternionMatrix (q * r) = quaternionMatrix q * quaternionMatrix r := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [quaternionMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The representation respects real scalar multiplication. -/
theorem quaternionMatrix_smul (c : ℝ) (q : RealQuaternion) :
    quaternionMatrix (c • q) = c • quaternionMatrix q := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quaternionMatrix]

/-- The matrix representation as a real linear map. -/
def quaternionMatrixLinear : RealQuaternion →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := quaternionMatrix
  map_add' := quaternionMatrix_add
  map_smul' := quaternionMatrix_smul

/-- The matrix representation as a unital ring homomorphism. -/
def quaternionMatrixHom : RealQuaternion →+* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := quaternionMatrix
  map_zero' := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quaternionMatrix]
  map_one' := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [quaternionMatrix]
  map_add' := quaternionMatrix_add
  map_mul' := quaternionMatrix_mul

/-- equation: the image is precisely the specified matrix family. -/
theorem quaternionMatrix_range (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A ∈ Set.range quaternionMatrix ↔ ∃ z w : ℂ, A = !![z, w; -star w, star z] := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩, rfl⟩
  · rintro ⟨z, w, rfl⟩
    exact ⟨complexPair z w, rfl⟩

/-- determinant in the complex matrix model. -/
theorem quaternionMatrix_determinant (z w : ℂ) :
    (quaternionMatrix (complexPair z w)).det =
      ((Complex.normSq z + Complex.normSq w : ℝ) : ℂ) := by
  rw [quaternionMatrix_complexPair, Matrix.det_fin_two]
  apply Complex.ext <;> simp [Complex.normSq_apply]
  ring

/-- The additive abelian group structure. -/
abbrev quaternionAdditiveGroup : AddCommGroup RealQuaternion := inferInstance

/-- nonzero quaternions represented by units. -/
abbrev NonzeroQuaternion := RealQuaternionˣ

/-- The multiplicative group structure. -/
abbrev nonzeroQuaternionGroup : Group NonzeroQuaternion := inferInstance

/-- units are exactly the nonzero quaternions. -/
theorem nonzeroQuaternion_representation (q : RealQuaternion) :
    q ≠ 0 ↔ ∃ u : NonzeroQuaternion, (u : RealQuaternion) = q := by
  constructor
  · intro h
    exact ⟨Units.mk0 q h, rfl⟩
  · rintro ⟨u, rfl⟩
    exact Units.ne_zero u

/-- The multiplication relations of the imaginary units. -/
theorem quaternion_unit_products :
    quaternionI ^ 2 = -1 ∧ quaternionJ ^ 2 = -1 ∧ quaternionK ^ 2 = -1 ∧
    quaternionI * quaternionJ = quaternionK ∧
    quaternionJ * quaternionK = quaternionI ∧
    quaternionK * quaternionI = quaternionJ ∧
    quaternionJ * quaternionI = -quaternionK ∧
    quaternionK * quaternionJ = -quaternionI ∧
    quaternionI * quaternionK = -quaternionJ := by
  repeat' constructor
  all_goals ext <;> norm_num [quaternionI, quaternionJ, quaternionK, pow_two]

/-- The first imaginary unit is nonzero. -/
theorem quaternionI_ne_zero : quaternionI ≠ 0 := by
  intro h
  have := congrArg (fun q : RealQuaternion => q.imI) h
  norm_num [quaternionI] at this

/-- The second imaginary unit is nonzero. -/
theorem quaternionJ_ne_zero : quaternionJ ≠ 0 := by
  intro h
  have := congrArg (fun q : RealQuaternion => q.imJ) h
  norm_num [quaternionJ] at this

/-- The first imaginary unit in the multiplicative group. -/
noncomputable def quaternionIUnit : NonzeroQuaternion := Units.mk0 quaternionI quaternionI_ne_zero
/-- The second imaginary unit in the multiplicative group. -/
noncomputable def quaternionJUnit : NonzeroQuaternion := Units.mk0 quaternionJ quaternionJ_ne_zero

/-- The multiplicative group is not abelian. -/
theorem nonzeroQuaternion_not_commutative :
    quaternionIUnit * quaternionJUnit ≠ quaternionJUnit * quaternionIUnit := by
  intro h
  have hcoord := congrArg (fun u : NonzeroQuaternion => (u : RealQuaternion).imK) h
  norm_num [quaternionIUnit, quaternionJUnit, quaternionI, quaternionJ] at hcoord

/-- The real coordinate basis. -/
noncomputable def quaternionRealBasis : Module.Basis (Fin 4) ℝ RealQuaternion :=
  QuaternionAlgebra.basisOneIJK (-1) 0 (-1)

/-- The basis consists of the standard four units. -/
theorem quaternionRealBasis_values :
    quaternionRealBasis 0 = 1 ∧ quaternionRealBasis 1 = quaternionI ∧
    quaternionRealBasis 2 = quaternionJ ∧ quaternionRealBasis 3 = quaternionK := by
  repeat' constructor
  all_goals
    apply quaternionRealBasis.repr.injective
    ext k
    fin_cases k <;>
      simp [quaternionRealBasis, QuaternionAlgebra.coe_basisOneIJK_repr,
        quaternionI, quaternionJ, quaternionK]

/-- The real dimension. -/
theorem quaternion_dimension : Module.finrank ℝ RealQuaternion = 4 :=
  Quaternion.finrank_eq_four

/-- The complex numbers as a real subalgebra. -/
abbrev complexQuaternionEmbedding : ℂ →ₐ[ℝ] RealQuaternion := Quaternion.ofComplex

/-- The complex embedding is injective. -/
theorem complexQuaternionEmbedding_injective : Function.Injective complexQuaternionEmbedding :=
  (RingHom.injective complexQuaternionEmbedding.toRingHom)

/-- The embedding has the prescribed real coordinates. -/
theorem complexQuaternionEmbedding_coordinates (z : ℂ) :
    complexQuaternionEmbedding z = (z.re : RealQuaternion) + z.im • quaternionI := by
  ext <;> simp [quaternionI, complexQuaternionEmbedding]

/-- The matrices of the three imaginary units. -/
theorem quaternionMatrix_units :
    quaternionMatrix quaternionI = !![Complex.I, 0; 0, -Complex.I] ∧
    quaternionMatrix quaternionJ = !![0, 1; -1, 0] ∧
    quaternionMatrix quaternionK = !![0, Complex.I; Complex.I, 0] := by
  repeat' constructor
  all_goals ext i j : 1
  all_goals fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;> norm_num [quaternionMatrix, quaternionI, quaternionJ, quaternionK]

/-- The eight signed standard units, enumerated for the subgroup construction. -/
def quaternionEightValues (i : Fin 8) : RealQuaternion :=
  ![1, -1, quaternionI, -quaternionI, quaternionJ, -quaternionJ,
    quaternionK, -quaternionK] i

/-- All signed standard units are nonzero. -/
theorem quaternionEightValues_ne_zero (i : Fin 8) : quaternionEightValues i ≠ 0 := by
  fin_cases i <;>
    norm_num [quaternionEightValues, quaternionI, quaternionJ, quaternionK,
      QuaternionAlgebra.ext_iff]

/-- The signed standard units as multiplicative units. -/
noncomputable def quaternionEightUnit (i : Fin 8) : NonzeroQuaternion :=
  Units.mk0 (quaternionEightValues i) (quaternionEightValues_ne_zero i)

/-- The enumeration contains eight distinct elements. -/
theorem quaternionEightUnit_injective : Function.Injective quaternionEightUnit := by
  intro i j h
  have hq := congrArg (fun u : NonzeroQuaternion => (u : RealQuaternion)) h
  fin_cases i <;> fin_cases j <;>
    first | rfl | norm_num [quaternionEightUnit, quaternionEightValues, quaternionI,
      quaternionJ, quaternionK, QuaternionAlgebra.ext_iff] at hq

/-- The subgroup of signed standard units. -/
noncomputable def quaternionEightGroup : Subgroup NonzeroQuaternion where
  carrier := Set.range quaternionEightUnit
  one_mem' := ⟨0, by apply Units.ext; ext <;> norm_num [quaternionEightUnit, quaternionEightValues]⟩
  mul_mem' := by
    rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    change ∃ k : Fin 8, quaternionEightUnit k = quaternionEightUnit i * quaternionEightUnit j
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.exists_fin_succ, quaternionEightUnit, quaternionEightValues,
        Units.ext_iff, quaternionI, quaternionJ, quaternionK, QuaternionAlgebra.ext_iff]
  inv_mem' := by
    rintro a ⟨i, rfl⟩
    change ∃ k : Fin 8, quaternionEightUnit k = (quaternionEightUnit i)⁻¹
    fin_cases i <;>
      norm_num [Fin.exists_fin_succ, quaternionEightUnit, quaternionEightValues,
        Units.ext_iff, quaternionI, quaternionJ, quaternionK, QuaternionAlgebra.ext_iff,
        Quaternion.inv_def, Quaternion.normSq_def']

/-- An explicit enumeration of the subgroup by eight indices. -/
noncomputable def quaternionEightEquiv : Fin 8 ≃ quaternionEightGroup :=
  Equiv.ofBijective (fun i => ⟨quaternionEightUnit i, ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => quaternionEightUnit_injective (congrArg Subtype.val h), by
      rintro ⟨u, i, rfl⟩
      exact ⟨i, rfl⟩⟩

/-- The subgroup has order eight. -/
theorem quaternionEightGroup_card : Nat.card quaternionEightGroup = 8 := by
  rw [Nat.card_congr quaternionEightEquiv.symm]
  exact Nat.card_fin 8

/-- Every signed standard unit is a word in the first two imaginary units. -/
theorem quaternionEightUnit_words (i : Fin 8) :
    quaternionEightUnit i =
      ![1, quaternionIUnit * quaternionIUnit, quaternionIUnit,
        quaternionIUnit * quaternionIUnit * quaternionIUnit, quaternionJUnit,
        quaternionIUnit * quaternionIUnit * quaternionJUnit,
        quaternionIUnit * quaternionJUnit,
        (quaternionIUnit * quaternionIUnit) * (quaternionIUnit * quaternionJUnit)] i := by
  fin_cases i <;> apply Units.ext <;> ext <;>
    norm_num [quaternionEightUnit, quaternionEightValues, quaternionIUnit,
      quaternionJUnit, quaternionI, quaternionJ, quaternionK]

/-- The signed-unit subgroup is generated by the first two imaginary units. -/
theorem quaternionEightGroup_eq_closure :
    quaternionEightGroup = Subgroup.closure ({quaternionIUnit, quaternionJUnit} : Set NonzeroQuaternion) := by
  let G := Subgroup.closure ({quaternionIUnit, quaternionJUnit} : Set NonzeroQuaternion)
  have hi : quaternionIUnit ∈ G := Subgroup.subset_closure (by simp)
  have hj : quaternionJUnit ∈ G := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · rintro u ⟨i, rfl⟩
    rw [quaternionEightUnit_words]
    fin_cases i
    · exact G.one_mem
    · exact G.mul_mem hi hi
    · exact hi
    · exact G.mul_mem (G.mul_mem hi hi) hi
    · exact hj
    · exact G.mul_mem (G.mul_mem hi hi) hj
    · exact G.mul_mem hi hj
    · exact G.mul_mem (G.mul_mem hi hi) (G.mul_mem hi hj)
  · apply (Subgroup.closure_le _).mpr
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact ⟨2, rfl⟩
    · exact ⟨4, rfl⟩

/-- The standard units generate the eight-element subgroup. -/
theorem quaternion_standard_units_generate_eight :
    Subgroup.closure ({1, quaternionIUnit, quaternionJUnit, quaternionEightUnit 6} :
      Set NonzeroQuaternion) = quaternionEightGroup := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact quaternionEightGroup.one_mem
    · exact ⟨2, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨6, rfl⟩
  · rw [quaternionEightGroup_eq_closure]
    apply (Subgroup.closure_le _).mpr
    intro u hu
    apply Subgroup.subset_closure
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
    tauto

end LowDimensionalTopology.Geometry.Auxiliary.Algebra
