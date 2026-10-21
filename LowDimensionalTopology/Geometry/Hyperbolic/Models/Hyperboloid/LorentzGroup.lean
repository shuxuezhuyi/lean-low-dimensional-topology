/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Basic

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Hyperboloid.Coordinates
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Tactic

@[expose] public section

open Set Matrix
open scoped MatrixGroups InnerProductSpace

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

/-- Native Lorentz coordinates with the time coordinate at index zero. -/
def lorentzCoordinates (n : ℕ) : LorentzVector n ≃ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun x := Fin.cons x.1 (fun i => x.2 i)
  invFun v := (v 0, WithLp.toLp 2 (fun i => v i.succ))
  left_inv x := by apply Prod.ext rfl; ext i; rfl
  right_inv v := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_add' x y := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_smul' r x := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem lorentzCoordinates_zero (n : ℕ) (x : LorentzVector n) : lorentzCoordinates n x 0 = x.1 := rfl

theorem lorentzCoordinates_succ (n : ℕ) (x : LorentzVector n) (i : Fin n) :
    lorentzCoordinates n x i.succ = x.2 i := rfl

/-- The Lorentz signature matrix in the source's row-vector convention. -/
def lorentzJ (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else -1)

theorem lorentzJ_transpose (n : ℕ) : (lorentzJ n)ᵀ = lorentzJ n := by
  simp [lorentzJ]

theorem lorentzJ_mul_self (n : ℕ) : lorentzJ n * lorentzJ n = 1 := by
  rw [lorentzJ, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0 <;> simp [hi]
  · simp [hij]

theorem lorentzJ_det_ne_zero (n : ℕ) : (lorentzJ n).det ≠ 0 := by
  have h := congrArg Matrix.det (lorentzJ_mul_self n)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact fun hz => by rw [hz, zero_mul] at h; exact zero_ne_one h

theorem lorentzForm_coordinates {n : ℕ} (x y : LorentzVector n) :
    lorentzForm x y = lorentzCoordinates n x ⬝ᵥ (lorentzJ n *ᵥ lorentzCoordinates n y) := by
  simp only [lorentzForm, lorentzJ, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_succ,
    lorentzCoordinates_zero, lorentzCoordinates_succ, ite_true, one_mul, Fin.succ_ne_zero,
    ite_false, neg_one_mul, mul_neg]
  rw [Finset.sum_neg_distrib, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  ring

/-- Right multiplication by a matrix, transported to the fixed native Lorentz vectors. -/
def lorentzRowLinearMap {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    LorentzVector n →ₗ[ℝ] LorentzVector n :=
  (lorentzCoordinates n).symm.toLinearMap.comp (A.vecMulLinear.comp (lorentzCoordinates n).toLinearMap)

theorem lorentzRowLinearMap_coordinates {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : LorentzVector n) :
    lorentzCoordinates n (lorentzRowLinearMap A x) = lorentzCoordinates n x ᵥ* A := by
  simp [lorentzRowLinearMap]

theorem lorentzRowLinearMap_one {n : ℕ} (x : LorentzVector n) :
    lorentzRowLinearMap (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) x = x := by
  apply (lorentzCoordinates n).injective
  simp only [lorentzRowLinearMap_coordinates, Matrix.vecMul_one]

/-- Row vectors compose in the reverse order of left actions. -/
theorem lorentzRowLinearMap_mul {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : LorentzVector n) :
    lorentzRowLinearMap (A * B) x = lorentzRowLinearMap B (lorentzRowLinearMap A x) := by
  apply (lorentzCoordinates n).injective
  simp only [lorentzRowLinearMap_coordinates, Matrix.vecMul_vecMul]

theorem lorentzForm_row_matrix {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x y : LorentzVector n) :
    lorentzForm (lorentzRowLinearMap A x) (lorentzRowLinearMap A y) =
      lorentzCoordinates n x ⬝ᵥ ((A * lorentzJ n * Aᵀ) *ᵥ lorentzCoordinates n y) := by
  rw [lorentzForm_coordinates, lorentzRowLinearMap_coordinates, lorentzRowLinearMap_coordinates]
  calc
    _ = (lorentzCoordinates n x ᵥ* A) ⬝ᵥ
        ((lorentzJ n * Aᵀ) *ᵥ lorentzCoordinates n y) := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]
    _ = ((lorentzCoordinates n x ᵥ* A) ᵥ* (lorentzJ n * Aᵀ)) ⬝ᵥ lorentzCoordinates n y :=
      Matrix.dotProduct_mulVec _ _ _
    _ = (lorentzCoordinates n x ᵥ* (A * lorentzJ n * Aᵀ)) ⬝ᵥ lorentzCoordinates n y := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_assoc]
    _ = _ := (Matrix.dotProduct_mulVec _ _ _).symm

/-- O(1,n), as the actual invertible real matrices satisfying the row-vector Lorentz identity. -/
def lorentzOrthogonalGroup (n : ℕ) : Subgroup (GL (Fin (n + 1)) ℝ) where
  carrier := {A | A.val * lorentzJ n * A.valᵀ = lorentzJ n}
  one_mem' := by
    change (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) * lorentzJ n * (1 : Matrix (Fin (n + 1)) (Fin (n + 1))
      ℝ)ᵀ = lorentzJ n
    simp
  mul_mem' {A B} hA hB := by
    change A.val * lorentzJ n * A.valᵀ = lorentzJ n at hA
    change B.val * lorentzJ n * B.valᵀ = lorentzJ n at hB
    change (A.val * B.val) * lorentzJ n * (A.val * B.val)ᵀ = lorentzJ n
    rw [Matrix.transpose_mul]
    calc
      _ = A.val * (B.val * lorentzJ n * B.valᵀ) * A.valᵀ := by simp [Matrix.mul_assoc]
      _ = _ := by rw [hB, hA]
  inv_mem' {A} hA := by
    change A.val * lorentzJ n * A.valᵀ = lorentzJ n at hA
    change A⁻¹.val * lorentzJ n * A⁻¹.valᵀ = lorentzJ n
    have h := congrArg (fun M => A⁻¹.val * M * A⁻¹.valᵀ) hA
    have hc : A⁻¹.val * (A.val * lorentzJ n * A.valᵀ) * A⁻¹.valᵀ = lorentzJ n := by
      calc
        _ = (A⁻¹.val * A.val) * lorentzJ n * (A.valᵀ * A⁻¹.valᵀ) := by simp [Matrix.mul_assoc]
        _ = _ := by rw [← Matrix.transpose_mul, A.inv_mul]; simp
    exact h.symm.trans hc

theorem mem_lorentzOrthogonalGroup {n : ℕ} (A : GL (Fin (n + 1)) ℝ) :
    A ∈ lorentzOrthogonalGroup n ↔ A.val * lorentzJ n * A.valᵀ = lorentzJ n := Iff.rfl

theorem lorentzOrthogonal_preserves_form {n : ℕ} {A : GL (Fin (n + 1)) ℝ}
    (hA : A ∈ lorentzOrthogonalGroup n) (x y : LorentzVector n) :
    lorentzForm (lorentzRowLinearMap A.val x) (lorentzRowLinearMap A.val y) = lorentzForm x y := by
  rw [lorentzForm_row_matrix, (mem_lorentzOrthogonalGroup A).mp hA, ← lorentzForm_coordinates]

theorem lorentzOrthogonal_inverse_matrix {n : ℕ} {A : GL (Fin (n + 1)) ℝ}
    (hA : A ∈ lorentzOrthogonalGroup n) : A⁻¹.val = (lorentzJ n * A.val * lorentzJ n)ᵀ := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [Matrix.transpose_mul, Matrix.transpose_mul, lorentzJ_transpose]
  calc
    _ = (A.val * lorentzJ n * A.valᵀ) * lorentzJ n := by simp [Matrix.mul_assoc]
    _ = 1 := by rw [(mem_lorentzOrthogonalGroup A).mp hA, lorentzJ_mul_self]

theorem lorentzOrthogonal_det_sq {n : ℕ} {A : GL (Fin (n + 1)) ℝ}
    (hA : A ∈ lorentzOrthogonalGroup n) : A.val.det ^ 2 = 1 := by
  have h := congrArg Matrix.det ((mem_lorentzOrthogonalGroup A).mp hA)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  apply (mul_right_cancel₀ (lorentzJ_det_ne_zero n))
  nlinarith only [h]

theorem lorentzOrthogonal_det_eq_one_or_neg_one {n : ℕ} {A : GL (Fin (n + 1)) ℝ}
    (hA : A ∈ lorentzOrthogonalGroup n) : A.val.det = 1 ∨ A.val.det = -1 :=
  (sq_eq_one_iff).mp (lorentzOrthogonal_det_sq hA)

theorem lorentzForm_add_self {n : ℕ} (x y : LorentzVector n) :
    lorentzForm (x + y) (x + y) = lorentzForm x x + 2 * lorentzForm x y + lorentzForm y y := by
  simp only [lorentzForm, Prod.fst_add, Prod.snd_add, inner_add_left, inner_add_right]
  rw [real_inner_comm y.2 x.2]
  ring

theorem lorentz_matrix_identity_iff_preserves_form {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    M * lorentzJ n * Mᵀ = lorentzJ n ↔
      ∀ x y : LorentzVector n, lorentzForm (lorentzRowLinearMap M x) (lorentzRowLinearMap M y) =
        lorentzForm x y := by
  constructor
  · intro h x y
    rw [lorentzForm_row_matrix, h, ← lorentzForm_coordinates]
  · intro h
    ext i j
    have he := h ((lorentzCoordinates n).symm (Pi.single i 1))
      ((lorentzCoordinates n).symm (Pi.single j 1))
    rw [lorentzForm_row_matrix, lorentzForm_coordinates] at he
    simp only [LinearEquiv.apply_symm_apply, single_dotProduct, one_mul,
      Matrix.mulVec_single_one] at he
    exact he

theorem lorentz_matrix_identity_iff_preserves_quadratic {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    M * lorentzJ n * Mᵀ = lorentzJ n ↔
      ∀ x : LorentzVector n, lorentzForm (lorentzRowLinearMap M x) (lorentzRowLinearMap M x) =
        lorentzForm x x := by
  rw [lorentz_matrix_identity_iff_preserves_form]
  constructor
  · exact fun h x => h x x
  · intro h x y
    have hsum := h (x + y)
    rw [map_add, lorentzForm_add_self, lorentzForm_add_self, h x, h y] at hsum
    linarith

theorem lorentz_matrix_det_sq {n : ℕ}
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hM : M * lorentzJ n * Mᵀ = lorentzJ n) : M.det ^ 2 = 1 := by
  have h := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  apply mul_right_cancel₀ (lorentzJ_det_ne_zero n)
  nlinarith only [h]

/-- A quadratic-form preserver is automatically invertible, so the GL-based group
definition imposes no additional mathematical hypothesis. -/
theorem lorentz_quadratic_preserver_exists_group {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hM : ∀ x : LorentzVector n,
      lorentzForm (lorentzRowLinearMap M x) (lorentzRowLinearMap M x) = lorentzForm x x) :
    ∃ A : GL (Fin (n + 1)) ℝ, A ∈ lorentzOrthogonalGroup n ∧ A.val = M := by
  have hid := (lorentz_matrix_identity_iff_preserves_quadratic M).mpr hM
  have hdet : M.det ≠ 0 := by
    have hsq := lorentz_matrix_det_sq hid
    intro hzero
    rw [hzero, zero_pow (by norm_num)] at hsq
    exact zero_ne_one hsq
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, hid, rfl⟩

/-- SO(1,n) is the determinant-one subgroup of the actual Lorentz matrix group. -/
def lorentzSpecialOrthogonalGroup (n : ℕ) : Subgroup (GL (Fin (n + 1)) ℝ) :=
  lorentzOrthogonalGroup n ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin (n + 1)) ℝ →* ℝˣ).ker

theorem mem_lorentzSpecialOrthogonalGroup {n : ℕ} (A : GL (Fin (n + 1)) ℝ) :
    A ∈ lorentzSpecialOrthogonalGroup n ↔ A ∈ lorentzOrthogonalGroup n ∧ A.val.det = 1 := by
  change (A ∈ lorentzOrthogonalGroup n ∧ Matrix.GeneralLinearGroup.det A = 1) ↔ _
  constructor
  · rintro ⟨hA, hdet⟩
    exact ⟨hA, congrArg Units.val hdet⟩
  · rintro ⟨hA, hdet⟩
    exact ⟨hA, Units.ext hdet⟩

def lorentzTimeUnit (n : ℕ) : LorentzVector n := (1, 0)

theorem lorentzTimeUnit_mem (n : ℕ) : lorentzTimeUnit n ∈ hyperboloidSet n := by
  simp [lorentzTimeUnit, hyperboloidSet, lorentzForm]

theorem lorentzRowLinearMap_timeUnit_time {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (lorentzRowLinearMap M (lorentzTimeUnit n)).1 = M 0 0 := by
  rw [← lorentzCoordinates_zero n, lorentzRowLinearMap_coordinates]
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, lorentzCoordinates, lorentzTimeUnit]

theorem lorentz_hyperboloid_preconnected (n : ℕ) : IsPreconnected (univ : Set (Hyperboloid n)) := by
  have hball : IsPreconnected (univ : Set (unitBallDomain n)) := isPreconnected_univ
  have h := hball.image (hyperboloidBallHomeomorph n).symm
    (hyperboloidBallHomeomorph n).symm.continuous.continuousOn
  simpa only [image_univ, (hyperboloidBallHomeomorph n).symm.surjective.range_eq] using h

theorem lorentzOrthogonal_time_ne_zero_on_sheet {n : ℕ} {A : GL (Fin (n + 1)) ℝ}
    (hA : A ∈ lorentzOrthogonalGroup n) (x : Hyperboloid n) :
    (lorentzRowLinearMap A.val x.val).1 ≠ 0 := by
  have hq := (lorentzOrthogonal_preserves_form hA x.val x.val).trans x.property.1
  rw [lorentzForm_self] at hq
  intro hz
  rw [hz, zero_pow (by norm_num)] at hq
  nlinarith [sq_nonneg ‖(lorentzRowLinearMap A.val x.val).2‖]

/-- Positive time orientation means preservation of the positive hyperboloid sheet.
It does not assert preservation of the entire ambient affine half-space. -/
theorem lorentzOrthogonal_positive_iff_maps_sheet {n : ℕ} {A : GL (Fin (n + 1)) ℝ}
    (hA : A ∈ lorentzOrthogonalGroup n) :
    0 < A 0 0 ↔ MapsTo (lorentzRowLinearMap A.val) (hyperboloidSet n) (hyperboloidSet n) := by
  constructor
  · intro hpos x hx
    have hc : Continuous (fun x : Hyperboloid n => (lorentzRowLinearMap A.val x.val).1) :=
      (continuous_fst.comp (lorentzRowLinearMap A.val).continuous_of_finiteDimensional).comp
        continuous_subtype_val
    have hbase : ∃ x : Hyperboloid n, x ∈ (univ : Set (Hyperboloid n)) ∧
        0 < (lorentzRowLinearMap A.val x.val).1 := by
      refine ⟨⟨lorentzTimeUnit n, lorentzTimeUnit_mem n⟩, mem_univ _, ?_⟩
      simpa only [lorentzRowLinearMap_timeUnit_time] using hpos
    have htime := (lorentz_hyperboloid_preconnected n).lt_of_ne hc.continuousOn
      (fun x _ => lorentzOrthogonal_time_ne_zero_on_sheet hA x) hbase
      (show (⟨x, hx⟩ : Hyperboloid n) ∈ univ from mem_univ _)
    exact ⟨(lorentzOrthogonal_preserves_form hA x x).trans hx.1, htime⟩
  · intro h
    have hp := (h (lorentzTimeUnit_mem n)).2
    simpa only [lorentzRowLinearMap_timeUnit_time] using hp

theorem lorentzOrthogonal_inverse_time_entry {n : ℕ} {A : GL (Fin (n + 1)) ℝ}
    (hA : A ∈ lorentzOrthogonalGroup n) : A⁻¹ 0 0 = A 0 0 := by
  rw [lorentzOrthogonal_inverse_matrix hA]
  simp [lorentzJ, Matrix.mul_apply, Matrix.diagonal_apply]

/-- O⁺(1,n), the positive-time subgroup of the actual Lorentz matrix group. -/
def lorentzPositiveOrthogonalGroup (n : ℕ) : Subgroup (GL (Fin (n + 1)) ℝ) where
  carrier := {A | A ∈ lorentzOrthogonalGroup n ∧ 0 < A 0 0}
  one_mem' := ⟨(lorentzOrthogonalGroup n).one_mem, by norm_num⟩
  mul_mem' {A B} hA hB := by
    refine ⟨(lorentzOrthogonalGroup n).mul_mem hA.1 hB.1, ?_⟩
    have hma := (lorentzOrthogonal_positive_iff_maps_sheet hA.1).mp hA.2
    have hmb := (lorentzOrthogonal_positive_iff_maps_sheet hB.1).mp hB.2
    have hm := hmb (hma (lorentzTimeUnit_mem n))
    have hp := hm.2
    rw [← lorentzRowLinearMap_mul, lorentzRowLinearMap_timeUnit_time] at hp
    exact hp
  inv_mem' {A} hA := by
    refine ⟨(lorentzOrthogonalGroup n).inv_mem hA.1, ?_⟩
    rw [lorentzOrthogonal_inverse_time_entry hA.1]
    exact hA.2

theorem mem_lorentzPositiveOrthogonalGroup {n : ℕ} (A : GL (Fin (n + 1)) ℝ) :
    A ∈ lorentzPositiveOrthogonalGroup n ↔ A ∈ lorentzOrthogonalGroup n ∧ 0 < A 0 0 := Iff.rfl

/-- SO⁺(1,n) is the intersection of determinant-one and positive-time Lorentz matrices. -/
def lorentzSpecialPositiveOrthogonalGroup (n : ℕ) : Subgroup (GL (Fin (n + 1)) ℝ) :=
  lorentzSpecialOrthogonalGroup n ⊓ lorentzPositiveOrthogonalGroup n

theorem mem_lorentzSpecialPositiveOrthogonalGroup {n : ℕ} (A : GL (Fin (n + 1)) ℝ) :
    A ∈ lorentzSpecialPositiveOrthogonalGroup n ↔
      A ∈ lorentzOrthogonalGroup n ∧ A.val.det = 1 ∧ 0 < A 0 0 := by
  change (A ∈ lorentzSpecialOrthogonalGroup n ∧ A ∈ lorentzPositiveOrthogonalGroup n) ↔ _
  rw [mem_lorentzSpecialOrthogonalGroup, mem_lorentzPositiveOrthogonalGroup]
  tauto

theorem lorentzOrthogonal_positive_iff_sheet_image {n : ℕ} {A : GL (Fin (n + 1)) ℝ}
    (hA : A ∈ lorentzOrthogonalGroup n) :
    0 < A 0 0 ↔ lorentzRowLinearMap A.val '' hyperboloidSet n = hyperboloidSet n := by
  constructor
  · intro hpos
    have hforw := (lorentzOrthogonal_positive_iff_maps_sheet hA).mp hpos
    have hinv := (lorentzOrthogonal_positive_iff_maps_sheet ((lorentzOrthogonalGroup n).inv_mem hA)).mp
      (by simpa only [lorentzOrthogonal_inverse_time_entry hA] using hpos)
    apply Subset.antisymm (image_subset_iff.mpr hforw)
    intro x hx
    refine ⟨lorentzRowLinearMap A⁻¹.val x, hinv hx, ?_⟩
    rw [← lorentzRowLinearMap_mul, A.inv_mul, lorentzRowLinearMap_one]
  · intro h
    exact (lorentzOrthogonal_positive_iff_maps_sheet hA).mpr (image_subset_iff.mp h.le)

/-- A genuine rational Lorentz boost shows why time orientation concerns the hyperboloid
or future timelike cone, rather than the entire ambient half-space. -/
theorem lorentz_positive_not_ambient_halfspace :
    ∃ A : GL (Fin 2) ℝ, A ∈ lorentzSpecialPositiveOrthogonalGroup 1 ∧
      ∃ x : LorentzVector 1, 0 < x.1 ∧ (lorentzRowLinearMap A.val x).1 < 0 := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![5 / 3, 4 / 3; 4 / 3, 5 / 3]
  have hdet : M.det = 1 := by norm_num [M, Matrix.det_fin_two]
  let A : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; norm_num)
  have hmat : M * lorentzJ 1 * Mᵀ = lorentzJ 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [M, lorentzJ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.diagonal_apply, Fin.sum_univ_succ]
  have hA : A ∈ lorentzSpecialPositiveOrthogonalGroup 1 := by
    rw [mem_lorentzSpecialPositiveOrthogonalGroup]
    exact ⟨hmat, hdet, by norm_num [A, M]⟩
  let x : LorentzVector 1 := (1, WithLp.toLp 2 (fun _ => -2))
  refine ⟨A, hA, x, by norm_num [x], ?_⟩
  rw [← lorentzCoordinates_zero 1, lorentzRowLinearMap_coordinates]
  norm_num [A, M, x, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, lorentzCoordinates]

end
end LowDimensionalTopology.Geometry.Hyperbolic
