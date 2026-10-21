/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Euclidean.EuclideanIsometries
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.LinearAlgebra.Matrix.Orthogonal
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
Every finite-dimensional real orthogonal automorphism has an orthonormal basis
of planar rotation blocks and positive or negative unit eigenvectors. The real
symmetric part supplies the first invariant block; dimension induction on its
invariant orthogonal complement supplies the others. The resulting orthogonal
change of basis proves the matrix normal form, including dimension zero.
-/

@[expose] public section

namespace LowDimensionalTopology.Geometry.Euclidean

universe u

noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real self-adjoint part of an orthogonal automorphism. -/
def orthogonalSymmetricPart (U : E ≃ₗᵢ[ℝ] E) : Module.End ℝ E :=
  (1 / 2 : ℝ) • (U.toLinearMap + U.symm.toLinearMap)

theorem orthogonalSymmetricPart_apply (U : E ≃ₗᵢ[ℝ] E) (x : E) :
    orthogonalSymmetricPart U x = (1 / 2 : ℝ) • (U x + U.symm x) := rfl

/-- The real symmetric part is genuinely self-adjoint. -/
theorem orthogonalSymmetricPart_isSymmetric (U : E ≃ₗᵢ[ℝ] E) :
    (orthogonalSymmetricPart U).IsSymmetric := by
  intro x y
  simp only [orthogonalSymmetricPart_apply, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, RCLike.conj_to_real,
    U.inner_map_eq_flip, U.symm.inner_map_eq_flip, LinearIsometryEquiv.symm_symm]
  ring

/-- An eigenvector of the real symmetric part generates an invariant subspace of dimension at most
 two, since the orthogonal map obeys this quadratic relation on its cyclic span. -/
theorem orthogonal_cyclic_quadratic (U : E ≃ₗᵢ[ℝ] E) (x : E) (a : ℝ)
    (hx : orthogonalSymmetricPart U x = a • x) :
    U (U x) = (2 * a) • U x - x := by
  have h := congrArg (fun y => (2 : ℝ) • U y) hx
  simp only [orthogonalSymmetricPart_apply, map_smul, map_add, U.apply_symm_apply,
    smul_smul] at h
  norm_num at h
  exact eq_sub_of_add_eq h

/-- The real spectral theorem supplies a unit vector for extracting the first orthogonal block. -/
theorem orthogonal_exists_symmetric_eigenvector [FiniteDimensional ℝ E] [Nontrivial E]
    (U : E ≃ₗᵢ[ℝ] E) :
    ∃ a : ℝ, ∃ x : E, ‖x‖ = 1 ∧ orthogonalSymmetricPart U x = a • x := by
  have hS := orthogonalSymmetricPart_isSymmetric U
  let i : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
  let b := hS.eigenvectorBasis rfl
  exact ⟨hS.eigenvalues rfl i, b i, b.orthonormal.norm_eq_one i,
    hS.apply_eigenvectorBasis rfl i⟩

/-- The symmetric-part eigenvalue is the real inner product with the image of a unit vector. -/
theorem orthogonal_eigenvalue_eq_inner (U : E ≃ₗᵢ[ℝ] E) (x : E) (a : ℝ)
    (hn : ‖x‖ = 1) (hx : orthogonalSymmetricPart U x = a • x) :
    a = ⟪x, U x⟫_ℝ := by
  have h := congrArg (fun y => ⟪x, y⟫_ℝ) hx
  simp only [orthogonalSymmetricPart_apply, inner_smul_right, inner_add_right,
    ← U.inner_map_eq_flip, real_inner_comm (U x) x, real_inner_self_eq_norm_sq, hn,
    one_pow, mul_one] at h
  calc
    a = ⟪U x, x⟫_ℝ := by linarith
    _ = ⟪x, U x⟫_ℝ := real_inner_comm _ _

/-- Every eigenvalue used in the real orthogonal block extraction lies in [-1,1]. -/
theorem orthogonal_eigenvalue_bounds (U : E ≃ₗᵢ[ℝ] E) (x : E) (a : ℝ)
    (hn : ‖x‖ = 1) (hx : orthogonalSymmetricPart U x = a • x) :
    -1 ≤ a ∧ a ≤ 1 := by
  rw [orthogonal_eigenvalue_eq_inner U x a hn hx]
  have h := abs_real_inner_le_norm x (U x)
  rw [U.norm_map, hn, mul_one] at h
  exact abs_le.mp h

/-- The part perpendicular to the first unit vector has the expected squared sine length. -/
theorem orthogonal_eigenvector_defect (U : E ≃ₗᵢ[ℝ] E) (x : E) (a : ℝ)
    (hn : ‖x‖ = 1) (hx : orthogonalSymmetricPart U x = a • x) :
    ⟪x, U x - a • x⟫_ℝ = 0 ∧ ‖U x - a • x‖ ^ 2 = 1 - a ^ 2 := by
  have hi := orthogonal_eigenvalue_eq_inner U x a hn hx
  constructor
  · simp only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hn,
      one_pow, mul_one, ← hi, sub_self]
  · rw [norm_sub_sq_real, U.norm_map, norm_smul, Real.norm_eq_abs, hn, mul_one,
      inner_smul_right, real_inner_comm x (U x), ← hi, sq_abs]
    ring

/-- Interior eigenvalues extract a genuine invariant orthonormal two-plane. -/
theorem orthogonal_rotation_pair (U : E ≃ₗᵢ[ℝ] E) (x : E) (a : ℝ)
    (hn : ‖x‖ = 1) (hx : orthogonalSymmetricPart U x = a • x) (ha : a ^ 2 < 1) :
    ∃ y : E, ‖y‖ = 1 ∧ ⟪x, y⟫_ℝ = 0 ∧
      U x = a • x + Real.sqrt (1 - a ^ 2) • y ∧
      U y = -Real.sqrt (1 - a ^ 2) • x + a • y := by
  let s := Real.sqrt (1 - a ^ 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = 1 - a ^ 2 := Real.sq_sqrt (by linarith)
  have hd := orthogonal_eigenvector_defect U x a hn hx
  have hdn : ‖U x - a • x‖ = s :=
    (sq_eq_sq₀ (norm_nonneg _) hs.le).mp (hd.2.trans hs2.symm)
  let y := s⁻¹ • (U x - a • x)
  have hsy : s • y = U x - a • x := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hnx : ‖y‖ = 1 := by
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, hdn, inv_mul_cancel₀ hs.ne']
  have hxy : ⟪x, y⟫_ℝ = 0 := by
    simp only [y, inner_smul_right, hd.1, mul_zero]
  have hUx : U x = a • x + s • y := by rw [hsy]; module
  have hUy : U y = -s • x + a • y := by
    apply smul_right_injective E hs.ne'
    have hc : a * a - 1 = -s * s := by nlinarith [hs2]
    calc
      s • U y = U (s • y) := (U.map_smul s y).symm
      _ = a • U x - x := by
        rw [hsy, map_sub, map_smul, orthogonal_cyclic_quadratic U x a hx]
        module
      _ = (a * a - 1) • x + (a * s) • y := by rw [hUx]; module
      _ = (-s * s) • x + (s * a) • y := by rw [hc, mul_comm a s]
      _ = s • (-s • x + a • y) := by module
  exact ⟨y, hnx, hxy, hUx, hUy⟩

/-- The extracted two-plane carries exactly the trigonometric rotation block used in the source. -/
theorem orthogonal_trigonometric_rotation_pair (U : E ≃ₗᵢ[ℝ] E) (x : E) (a : ℝ)
    (hn : ‖x‖ = 1) (hx : orthogonalSymmetricPart U x = a • x) (ha : a ^ 2 < 1) :
    ∃ θ : ℝ, ∃ y : E, 0 < Real.sin θ ∧ ‖y‖ = 1 ∧ ⟪x, y⟫_ℝ = 0 ∧
      U x = Real.cos θ • x + Real.sin θ • y ∧
      U y = -Real.sin θ • x + Real.cos θ • y := by
  obtain ⟨y, hyn, hxy, hUx, hUy⟩ := orthogonal_rotation_pair U x a hn hx ha
  have hb := orthogonal_eigenvalue_bounds U x a hn hx
  refine ⟨Real.arccos a, y, ?_, hyn, hxy, ?_, ?_⟩
  · rw [Real.sin_arccos]
    exact Real.sqrt_pos.mpr (by linarith)
  · simpa only [Real.cos_arccos hb.1 hb.2, Real.sin_arccos] using hUx
  · simpa only [Real.cos_arccos hb.1 hb.2, Real.sin_arccos] using hUy

/-- Every nonzero real orthogonal space has a fixed/reversed line or an invariant rotation plane. -/
theorem orthogonal_exists_invariant_block [FiniteDimensional ℝ E] [Nontrivial E]
    (U : E ≃ₗᵢ[ℝ] E) :
    (∃ x : E, ‖x‖ = 1 ∧ (U x = x ∨ U x = -x)) ∨
      (∃ θ : ℝ, ∃ x y : E, 0 < Real.sin θ ∧ ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
        ⟪x, y⟫_ℝ = 0 ∧ U x = Real.cos θ • x + Real.sin θ • y ∧
          U y = -Real.sin θ • x + Real.cos θ • y) := by
  obtain ⟨a, x, hn, hx⟩ := orthogonal_exists_symmetric_eigenvector U
  have hb := orthogonal_eigenvalue_bounds U x a hn hx
  have ha : a ^ 2 ≤ 1 := by
    have := mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ 1 + a by linarith)
    nlinarith
  by_cases heq : a ^ 2 = 1
  · left
    have hd := (orthogonal_eigenvector_defect U x a hn hx).2
    have hzero : U x - a • x = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (U x - a • x)])
    have hUx := sub_eq_zero.mp hzero
    refine ⟨x, hn, ?_⟩
    rcases sq_eq_one_iff.mp heq with h | h
    · exact Or.inl (by simpa [h] using hUx)
    · exact Or.inr (by simpa [h] using hUx)
  · right
    obtain ⟨θ, y, hsin, hyn, hxy, hUx, hUy⟩ :=
      orthogonal_trigonometric_rotation_pair U x a hn hx (lt_of_le_of_ne ha heq)
    exact ⟨θ, x, y, hsin, hn, hyn, hxy, hUx, hUy⟩

/-- A finite-dimensional invariant subspace of an orthogonal automorphism is mapped onto itself. -/
theorem orthogonal_invariant_subspace_map_eq [FiniteDimensional ℝ E]
    (U : E ≃ₗᵢ[ℝ] E) (S : Submodule ℝ E) (hS : ∀ x ∈ S, U x ∈ S) :
    S.map U.toLinearMap = S := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact Submodule.map_le_iff_le_comap.mpr hS
  · exact U.toLinearEquiv.finrank_map_eq S

/-- The orthogonal complement is invariant, permitting the dimension induction in the normal form. -/
theorem orthogonal_invariant_complement_map_eq [FiniteDimensional ℝ E]
    (U : E ≃ₗᵢ[ℝ] E) (S : Submodule ℝ E) (hS : ∀ x ∈ S, U x ∈ S) :
    Sᗮ.map U.toLinearMap = Sᗮ := by
  rw [Submodule.map_orthogonal_equiv, orthogonal_invariant_subspace_map_eq U S hS]

/-- Restrict an orthogonal automorphism to a genuine invariant subspace. -/
def orthogonalInvariantRestriction (U : E ≃ₗᵢ[ℝ] E) (S : Submodule ℝ E)
    (hS : S.map U.toLinearMap = S) : S ≃ₗᵢ[ℝ] S := by
  let f : S →ₗᵢ[ℝ] S :=
    { toFun := fun x => ⟨U x, hS.le (Submodule.mem_map.mpr ⟨x, x.property, rfl⟩)⟩
      map_add' := fun x y => Subtype.ext (map_add U (x : E) (y : E))
      map_smul' := fun a x => Subtype.ext (map_smul U a (x : E))
      norm_map' := fun x => U.norm_map x }
  apply LinearIsometryEquiv.ofSurjective f
  intro y
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp (hS.symm.le y.property)
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem orthogonalInvariantRestriction_apply (U : E ≃ₗᵢ[ℝ] E) (S : Submodule ℝ E)
    (hS : S.map U.toLinearMap = S) (x : S) :
    (orthogonalInvariantRestriction U S hS x : E) = U x := rfl

/-- A finite orthonormal family is an explicitly indexed basis of its span. -/
def orthonormalSpanBasis {ι : Type*} [Fintype ι] (v : ι → E) (hv : Orthonormal ℝ v) :
    OrthonormalBasis ι ℝ (Submodule.span ℝ (Set.range v)) :=
  (Module.Basis.span hv.linearIndependent).toOrthonormalBasis
    (by
      change Orthonormal ℝ (fun i => (Module.Basis.span hv.linearIndependent) i)
      simpa only [Module.Basis.span_apply] using orthonormal_span hv)

theorem orthonormalSpanBasis_apply {ι : Type*} [Fintype ι]
    (v : ι → E) (hv : Orthonormal ℝ v) (i : ι) :
    (orthonormalSpanBasis v hv i : E) = v i := by
  simp [orthonormalSpanBasis, Module.Basis.span_apply]

/-- Checking the image of a spanning family is sufficient for invariance of its span. -/
theorem orthogonal_span_invariant {ι : Type*} (U : E ≃ₗᵢ[ℝ] E) (v : ι → E)
    (hv : ∀ i, U (v i) ∈ Submodule.span ℝ (Set.range v)) :
    ∀ x ∈ Submodule.span ℝ (Set.range v), U x ∈ Submodule.span ℝ (Set.range v) := by
  have hle : Submodule.span ℝ (Set.range v) ≤
      (Submodule.span ℝ (Set.range v)).comap U.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hv i
  exact hle

/-- Assemble prescribed orthonormal bases on a subspace and its orthogonal complement. -/
def orthogonalSumBasis [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Submodule ℝ E) (b : OrthonormalBasis ι ℝ S)
    (c : OrthonormalBasis κ ℝ Sᗮ) : OrthonormalBasis (ι ⊕ κ) ℝ E := by
  classical
  let v : ι ⊕ κ → E := Sum.elim (fun i => (b i : E)) (fun j => (c j : E))
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simpa [v] using (orthonormal_iff_ite.mp b.orthonormal i j)
      | inr j => simpa [v] using
          (Submodule.inner_right_of_mem_orthogonal (b i).property (c j).property)
    | inr i =>
      cases j with
      | inl j => simpa [v] using
          (Submodule.inner_left_of_mem_orthogonal (b j).property (c i).property)
      | inr j => simpa [v] using (orthonormal_iff_ite.mp c.orthonormal i j)
  have hb : Submodule.span ℝ (Set.range fun i => (b i : E)) = S := by
    calc
      _ = (Submodule.span ℝ (Set.range b)).map S.subtype := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = S := by
        have hbspan : Submodule.span ℝ (Set.range b) = ⊤ := by
          simpa only [OrthonormalBasis.coe_toBasis] using b.toBasis.span_eq
        rw [hbspan, Submodule.map_subtype_top]
  have hc : Submodule.span ℝ (Set.range fun i => (c i : E)) = Sᗮ := by
    calc
      _ = (Submodule.span ℝ (Set.range c)).map Sᗮ.subtype := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = Sᗮ := by
        have hcspan : Submodule.span ℝ (Set.range c) = ⊤ := by
          simpa only [OrthonormalBasis.coe_toBasis] using c.toBasis.span_eq
        rw [hcspan, Submodule.map_subtype_top]
  apply OrthonormalBasis.mk hv
  change ⊤ ≤ Submodule.span ℝ (Set.range (Sum.elim _ _))
  rw [Set.Sum.elim_range, Submodule.span_union, hb, hc,
    Submodule.sup_orthogonal_of_hasOrthogonalProjection]

theorem orthogonalSumBasis_inl [FiniteDimensional ℝ E] {ι κ : Type*}
    [Fintype ι] [Fintype κ] (S : Submodule ℝ E) (b : OrthonormalBasis ι ℝ S)
    (c : OrthonormalBasis κ ℝ Sᗮ) (i : ι) : orthogonalSumBasis S b c (.inl i) = b i := by
  simp [orthogonalSumBasis]

theorem orthogonalSumBasis_inr [FiniteDimensional ℝ E] {ι κ : Type*}
    [Fintype ι] [Fintype κ] (S : Submodule ℝ E) (b : OrthonormalBasis ι ℝ S)
    (c : OrthonormalBasis κ ℝ Sᗮ) (i : κ) : orthogonalSumBasis S b c (.inr i) = c i := by
  simp [orthogonalSumBasis]

/-- The rotation block with the source's sign convention. -/
def orthogonalRotationBlock (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem orthogonalRotationBlock_mul_transpose (θ : ℝ) :
    orthogonalRotationBlock θ * (orthogonalRotationBlock θ).transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orthogonalRotationBlock, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem orthogonalRotationBlock_mem_orthogonalGroup (θ : ℝ) :
    orthogonalRotationBlock θ ∈ Matrix.orthogonalGroup (Fin 2) ℝ :=
  (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mpr (orthogonalRotationBlock_mul_transpose θ)

theorem orthogonalRotationBlock_det (θ : ℝ) : (orthogonalRotationBlock θ).det = 1 := by
  simp [orthogonalRotationBlock, Matrix.det_fin_two]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Block coordinates retain separate planar rotations, fixed directions and reversed directions. -/
abbrev OrthogonalBlockIndex (r s t : ℕ) := (Fin 2 × Fin r) ⊕ (Fin s ⊕ Fin t)

/-- The complete matrix shape. -/
def orthogonalBlockForm {r s t : ℕ} (θ : Fin r → ℝ) :
    Matrix (OrthogonalBlockIndex r s t) (OrthogonalBlockIndex r s t) ℝ :=
  Matrix.fromBlocks (Matrix.blockDiagonal fun k => orthogonalRotationBlock (θ k)) 0 0
    (Matrix.fromBlocks 1 0 0 (-1))

/-- Every displayed block matrix is genuinely orthogonal. -/
theorem orthogonalBlockForm_mul_transpose {r s t : ℕ} (θ : Fin r → ℝ) :
    orthogonalBlockForm (s := s) (t := t) θ *
      (orthogonalBlockForm (s := s) (t := t) θ).transpose = 1 := by
  simp [orthogonalBlockForm, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.blockDiagonal_transpose, ← Matrix.blockDiagonal_mul,
    orthogonalRotationBlock_mul_transpose, Matrix.fromBlocks_one]
  change Matrix.fromBlocks (Matrix.blockDiagonal (1 : Fin r → Matrix (Fin 2) (Fin 2) ℝ))
    0 0 (1 : Matrix (Fin s ⊕ Fin t) (Fin s ⊕ Fin t) ℝ) = 1
  rw [Matrix.blockDiagonal_one, Matrix.fromBlocks_one]

theorem orthogonalBlockForm_mem_orthogonalGroup {r s t : ℕ} (θ : Fin r → ℝ) :
    orthogonalBlockForm (s := s) (t := t) θ ∈
      Matrix.orthogonalGroup (OrthogonalBlockIndex r s t) ℝ :=
  (Matrix.mem_orthogonalGroup_iff (OrthogonalBlockIndex r s t) ℝ).mpr
    (orthogonalBlockForm_mul_transpose θ)

/-- A global orthonormal basis displaying all rotation, fixed and reversed blocks. -/
structure OrthogonalNormalBasis (U : E ≃ₗᵢ[ℝ] E) where
  rotations : ℕ
  fixed : ℕ
  reversed : ℕ
  angles : Fin rotations → ℝ
  basis : OrthonormalBasis (OrthogonalBlockIndex rotations fixed reversed) ℝ E
  rotation_zero (k : Fin rotations) :
    U (basis (.inl (0, k))) = Real.cos (angles k) • basis (.inl (0, k)) +
      Real.sin (angles k) • basis (.inl (1, k))
  rotation_one (k : Fin rotations) :
    U (basis (.inl (1, k))) = -Real.sin (angles k) • basis (.inl (0, k)) +
      Real.cos (angles k) • basis (.inl (1, k))
  fixed_apply (k : Fin fixed) : U (basis (.inr (.inl k))) = basis (.inr (.inl k))
  reversed_apply (k : Fin reversed) : U (basis (.inr (.inr k))) = -basis (.inr (.inr k))

/-- Reorder a newly extracted rotation plane before the previous normal blocks. -/
def prependRotationBlockEquiv (r s t : ℕ) :
    Fin 2 ⊕ OrthogonalBlockIndex r s t ≃ OrthogonalBlockIndex (r + 1) s t where
  toFun
    | .inl i => .inl (i, 0)
    | .inr (.inl (i, k)) => .inl (i, k.succ)
    | .inr (.inr side) => .inr side
  invFun
    | .inl (i, k) => Fin.cases (.inl i) (fun j => .inr (.inl (i, j))) k
    | .inr side => .inr (.inr side)
  left_inv x := by
    rcases x with i | x
    · rfl
    · rcases x with ⟨i, k⟩ | side <;> rfl
  right_inv x := by
    rcases x with ⟨i, k⟩ | side
    · cases k using Fin.cases <;> rfl
    · rfl

/-- Reorder a newly extracted fixed line into the positive identity block. -/
def prependFixedBlockEquiv (r s t : ℕ) :
    Fin 1 ⊕ OrthogonalBlockIndex r s t ≃ OrthogonalBlockIndex r (s + 1) t where
  toFun
    | .inl _ => .inr (.inl 0)
    | .inr (.inl pair) => .inl pair
    | .inr (.inr (.inl k)) => .inr (.inl k.succ)
    | .inr (.inr (.inr k)) => .inr (.inr k)
  invFun
    | .inl pair => .inr (.inl pair)
    | .inr (.inl k) => Fin.cases (.inl 0) (fun j => .inr (.inr (.inl j))) k
    | .inr (.inr k) => .inr (.inr (.inr k))
  left_inv x := by
    rcases x with i | x
    · have : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    · rcases x with pair | (k | k) <;> rfl
  right_inv x := by
    rcases x with pair | (k | k)
    · rfl
    · cases k using Fin.cases <;> rfl
    · rfl

/-- Reorder a newly extracted reversed line into the negative identity block. -/
def prependReversedBlockEquiv (r s t : ℕ) :
    Fin 1 ⊕ OrthogonalBlockIndex r s t ≃ OrthogonalBlockIndex r s (t + 1) where
  toFun
    | .inl _ => .inr (.inr 0)
    | .inr (.inl pair) => .inl pair
    | .inr (.inr (.inl k)) => .inr (.inl k)
    | .inr (.inr (.inr k)) => .inr (.inr k.succ)
  invFun
    | .inl pair => .inr (.inl pair)
    | .inr (.inl k) => .inr (.inr (.inl k))
    | .inr (.inr k) => Fin.cases (.inl 0) (fun j => .inr (.inr (.inr j))) k
  left_inv x := by
    rcases x with i | x
    · have : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    · rcases x with pair | (k | k) <;> rfl
  right_inv x := by
    rcases x with pair | (k | k)
    · rfl
    · rfl
    · cases k using Fin.cases <;> rfl

/-- Add a prescribed fixed unit line to a normal basis of its invariant orthogonal complement. -/
def prependFixedNormalBasis [FiniteDimensional ℝ E]
    (U : E ≃ₗᵢ[ℝ] E) (S : Submodule ℝ E) (b : OrthonormalBasis (Fin 1) ℝ S)
    (hb : ∀ i, U (b i : E) = b i) (hc : Sᗮ.map U.toLinearMap = Sᗮ)
    (d : OrthogonalNormalBasis (orthogonalInvariantRestriction U Sᗮ hc)) :
    OrthogonalNormalBasis U := by
  let B := (orthogonalSumBasis S b d.basis).reindex
    (prependFixedBlockEquiv d.rotations d.fixed d.reversed)
  refine
    { rotations := d.rotations
      fixed := d.fixed + 1
      reversed := d.reversed
      angles := d.angles
      basis := B
      rotation_zero := ?_
      rotation_one := ?_
      fixed_apply := ?_
      reversed_apply := ?_ }
  · intro k
    have h := congrArg (fun x : Sᗮ => (x : E)) (d.rotation_zero k)
    simpa [B, OrthonormalBasis.reindex_apply, prependFixedBlockEquiv,
      orthogonalSumBasis_inr, orthogonalInvariantRestriction_apply] using h
  · intro k
    have h := congrArg (fun x : Sᗮ => (x : E)) (d.rotation_one k)
    simpa [B, OrthonormalBasis.reindex_apply, prependFixedBlockEquiv,
      orthogonalSumBasis_inr, orthogonalInvariantRestriction_apply] using h
  · intro k
    cases k using Fin.cases with
    | zero =>
      simpa [B, OrthonormalBasis.reindex_apply, prependFixedBlockEquiv,
        orthogonalSumBasis_inl] using hb 0
    | succ k =>
      have h := congrArg (fun x : Sᗮ => (x : E)) (d.fixed_apply k)
      simpa [B, OrthonormalBasis.reindex_apply, prependFixedBlockEquiv,
        orthogonalSumBasis_inr, orthogonalInvariantRestriction_apply] using h
  · intro k
    have h := congrArg (fun x : Sᗮ => (x : E)) (d.reversed_apply k)
    simpa [B, OrthonormalBasis.reindex_apply, prependFixedBlockEquiv,
      orthogonalSumBasis_inr, orthogonalInvariantRestriction_apply] using h

/-- Add a prescribed reversed unit line to the normal basis on its orthogonal complement. -/
def prependReversedNormalBasis [FiniteDimensional ℝ E]
    (U : E ≃ₗᵢ[ℝ] E) (S : Submodule ℝ E) (b : OrthonormalBasis (Fin 1) ℝ S)
    (hb : ∀ i, U (b i : E) = -(b i : E)) (hc : Sᗮ.map U.toLinearMap = Sᗮ)
    (d : OrthogonalNormalBasis (orthogonalInvariantRestriction U Sᗮ hc)) :
    OrthogonalNormalBasis U := by
  let B := (orthogonalSumBasis S b d.basis).reindex
    (prependReversedBlockEquiv d.rotations d.fixed d.reversed)
  refine
    { rotations := d.rotations
      fixed := d.fixed
      reversed := d.reversed + 1
      angles := d.angles
      basis := B
      rotation_zero := ?_
      rotation_one := ?_
      fixed_apply := ?_
      reversed_apply := ?_ }
  · intro k
    have h := congrArg (fun x : Sᗮ => (x : E)) (d.rotation_zero k)
    simpa [B, OrthonormalBasis.reindex_apply, prependReversedBlockEquiv,
      orthogonalSumBasis_inr, orthogonalInvariantRestriction_apply] using h
  · intro k
    have h := congrArg (fun x : Sᗮ => (x : E)) (d.rotation_one k)
    simpa [B, OrthonormalBasis.reindex_apply, prependReversedBlockEquiv,
      orthogonalSumBasis_inr, orthogonalInvariantRestriction_apply] using h
  · intro k
    have h := congrArg (fun x : Sᗮ => (x : E)) (d.fixed_apply k)
    simpa [B, OrthonormalBasis.reindex_apply, prependReversedBlockEquiv,
      orthogonalSumBasis_inr, orthogonalInvariantRestriction_apply] using h
  · intro k
    cases k using Fin.cases with
    | zero =>
      simpa [B, OrthonormalBasis.reindex_apply, prependReversedBlockEquiv,
        orthogonalSumBasis_inl] using hb 0
    | succ k =>
      have h := congrArg (fun x : Sᗮ => (x : E)) (d.reversed_apply k)
      simpa [B, OrthonormalBasis.reindex_apply, prependReversedBlockEquiv,
        orthogonalSumBasis_inr, orthogonalInvariantRestriction_apply] using h

/-- Add the prescribed rotation plane while retaining every previous normal block. -/
def prependRotationNormalBasis [FiniteDimensional ℝ E]
    (U : E ≃ₗᵢ[ℝ] E) (S : Submodule ℝ E) (b : OrthonormalBasis (Fin 2) ℝ S) (θ : ℝ)
    (hb0 : U (b 0 : E) = Real.cos θ • (b 0 : E) + Real.sin θ • (b 1 : E))
    (hb1 : U (b 1 : E) = -Real.sin θ • (b 0 : E) + Real.cos θ • (b 1 : E))
    (hc : Sᗮ.map U.toLinearMap = Sᗮ)
    (d : OrthogonalNormalBasis (orthogonalInvariantRestriction U Sᗮ hc)) :
    OrthogonalNormalBasis U := by
  let B := (orthogonalSumBasis S b d.basis).reindex
    (prependRotationBlockEquiv d.rotations d.fixed d.reversed)
  refine
    { rotations := d.rotations + 1
      fixed := d.fixed
      reversed := d.reversed
      angles := Fin.cons θ d.angles
      basis := B
      rotation_zero := ?_
      rotation_one := ?_
      fixed_apply := ?_
      reversed_apply := ?_ }
  · intro k
    cases k using Fin.cases with
    | zero =>
      simpa [B, OrthonormalBasis.reindex_apply, prependRotationBlockEquiv,
        orthogonalSumBasis_inl] using hb0
    | succ k =>
      have h := congrArg (fun x : Sᗮ => (x : E)) (d.rotation_zero k)
      simpa [B, OrthonormalBasis.reindex_apply, prependRotationBlockEquiv,
        orthogonalSumBasis_inr, orthogonalInvariantRestriction_apply] using h
  · intro k
    cases k using Fin.cases with
    | zero =>
      simpa [B, OrthonormalBasis.reindex_apply, prependRotationBlockEquiv,
        orthogonalSumBasis_inl] using hb1
    | succ k =>
      have h := congrArg (fun x : Sᗮ => (x : E)) (d.rotation_one k)
      simpa [B, OrthonormalBasis.reindex_apply, prependRotationBlockEquiv,
        orthogonalSumBasis_inr, orthogonalInvariantRestriction_apply] using h
  · intro k
    have h := congrArg (fun x : Sᗮ => (x : E)) (d.fixed_apply k)
    simpa [B, OrthonormalBasis.reindex_apply, prependRotationBlockEquiv,
      orthogonalSumBasis_inr, orthogonalInvariantRestriction_apply] using h
  · intro k
    have h := congrArg (fun x : Sᗮ => (x : E)) (d.reversed_apply k)
    simpa [B, OrthonormalBasis.reindex_apply, prependRotationBlockEquiv,
      orthogonalSumBasis_inr, orthogonalInvariantRestriction_apply] using h

/-- The empty normal basis handles zero-dimensional spaces without a positive-dimension assumption. -/
def emptyOrthogonalNormalBasis [Subsingleton E] (U : E ≃ₗᵢ[ℝ] E) :
    OrthogonalNormalBasis U := by
  let v : OrthogonalBlockIndex 0 0 0 → E := fun i => isEmptyElim i
  have hv : Orthonormal ℝ v := Orthonormal.of_isEmpty v
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    intro x _
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  exact
    { rotations := 0
      fixed := 0
      reversed := 0
      angles := fun i => Fin.elim0 i
      basis := OrthonormalBasis.mk hv hspan
      rotation_zero := fun k => Fin.elim0 k
      rotation_one := fun k => Fin.elim0 k
      fixed_apply := fun k => Fin.elim0 k
      reversed_apply := fun k => Fin.elim0 k }

/-- Removing a nonempty orthonormal first block strictly decreases the complement's dimension. -/
theorem orthogonal_span_complement_finrank_lt [FiniteDimensional ℝ E]
    {ι : Type*} [Nonempty ι] (v : ι → E) (hv : Orthonormal ℝ v) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range v))ᗮ < Module.finrank ℝ E := by
  classical
  let S := Submodule.span ℝ (Set.range v)
  let i : ι := Classical.choice inferInstance
  have hne : (⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ : S) ≠ 0 := by
    intro h
    have hz : v i = 0 := congrArg Subtype.val h
    have hn := hv.norm_eq_one i
    simp [hz] at hn
  have hpos : 0 < Module.finrank ℝ S :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩
  have hdim := S.finrank_add_finrank_orthogonal
  change Module.finrank ℝ Sᗮ < Module.finrank ℝ E
  omega

/-- Dimension induction assembles the extracted invariant blocks into a global orthonormal basis. -/
theorem exists_orthogonalNormalBasis_by_finrank :
    ∀ n : ℕ, ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] (U : F ≃ₗᵢ[ℝ] F), Module.finrank ℝ F = n →
        Nonempty (OrthogonalNormalBasis U) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F _ _ _ U hdim
    rcases subsingleton_or_nontrivial F with hsub | hnon
    · have := hsub
      exact ⟨emptyOrthogonalNormalBasis U⟩
    · have := hnon
      rcases orthogonal_exists_invariant_block U with hline | hplane
      · obtain ⟨x, hn, hx⟩ := hline
        let v : Fin 1 → F := fun _ => x
        have hv : Orthonormal ℝ v := by
          refine ⟨fun _ => hn, ?_⟩
          intro i j hij
          exact (hij (Subsingleton.elim _ _)).elim
        let S := Submodule.span ℝ (Set.range v)
        let b := orthonormalSpanBasis v hv
        have hxS : x ∈ S := Submodule.subset_span ⟨0, rfl⟩
        have hS : ∀ y ∈ S, U y ∈ S := by
          apply orthogonal_span_invariant U v
          intro i
          change U x ∈ S
          rcases hx with h | h
          · simpa only [h] using hxS
          · simpa only [h] using S.neg_mem hxS
        have hc := orthogonal_invariant_complement_map_eq U S hS
        let R := orthogonalInvariantRestriction U Sᗮ hc
        have hrank : Module.finrank ℝ Sᗮ < n := by
          rw [← hdim]
          exact orthogonal_span_complement_finrank_lt v hv
        obtain ⟨d⟩ := ih (Module.finrank ℝ Sᗮ) hrank Sᗮ R rfl
        rcases hx with h | h
        · refine ⟨prependFixedNormalBasis U S b ?_ hc d⟩
          intro i
          change U (orthonormalSpanBasis v hv i : F) = _
          rw [orthonormalSpanBasis_apply]
          change U x = _
          simpa only [orthonormalSpanBasis_apply] using h
        · refine ⟨prependReversedNormalBasis U S b ?_ hc d⟩
          intro i
          change U (orthonormalSpanBasis v hv i : F) = _
          rw [orthonormalSpanBasis_apply]
          change U x = _
          simpa only [orthonormalSpanBasis_apply] using h
      · obtain ⟨θ, x, y, hsin, hxn, hyn, hxy, hUx, hUy⟩ := hplane
        let v : Fin 2 → F := ![x, y]
        have hv : Orthonormal ℝ v := by
          simp [v, orthonormal_vecCons_iff, hxn, hyn, hxy]
        let S := Submodule.span ℝ (Set.range v)
        let b := orthonormalSpanBasis v hv
        have hxS : x ∈ S := Submodule.subset_span ⟨0, rfl⟩
        have hyS : y ∈ S := Submodule.subset_span ⟨1, rfl⟩
        have hS : ∀ z ∈ S, U z ∈ S := by
          apply orthogonal_span_invariant U v
          intro i
          fin_cases i
          · change U x ∈ S
            rw [hUx]
            exact S.add_mem (S.smul_mem _ hxS) (S.smul_mem _ hyS)
          · change U y ∈ S
            rw [hUy]
            exact S.add_mem (S.smul_mem _ hxS) (S.smul_mem _ hyS)
        have hc := orthogonal_invariant_complement_map_eq U S hS
        let R := orthogonalInvariantRestriction U Sᗮ hc
        have hrank : Module.finrank ℝ Sᗮ < n := by
          rw [← hdim]
          exact orthogonal_span_complement_finrank_lt v hv
        obtain ⟨d⟩ := ih (Module.finrank ℝ Sᗮ) hrank Sᗮ R rfl
        have hbval (i : Fin 2) : (b i : F) = v i := orthonormalSpanBasis_apply v hv i
        refine ⟨prependRotationNormalBasis U S b θ ?_ ?_ hc d⟩
        · simp only [hbval]
          exact hUx
        · simp only [hbval]
          exact hUy

/-- Every finite-dimensional real orthogonal automorphism has the full block orthonormal basis. -/
theorem exists_orthogonalNormalBasis [FiniteDimensional ℝ E] (U : E ≃ₗᵢ[ℝ] E) :
    Nonempty (OrthogonalNormalBasis U) :=
  exists_orthogonalNormalBasis_by_finrank (Module.finrank ℝ E) E U rfl

/-- The rotation, fixed and reversed blocks account for the entire dimension. -/
theorem OrthogonalNormalBasis.dimension [FiniteDimensional ℝ E] (U : E ≃ₗᵢ[ℝ] E)
    (d : OrthogonalNormalBasis U) :
    2 * d.rotations + d.fixed + d.reversed = Module.finrank ℝ E := by
  simpa [OrthogonalBlockIndex, Nat.add_assoc] using
    (Module.finrank_eq_card_basis d.basis.toBasis).symm

/-- The matrix in the assembled orthonormal basis has exactly the prescribed block entries. -/
theorem OrthogonalNormalBasis.toMatrix (U : E ≃ₗᵢ[ℝ] E) (d : OrthogonalNormalBasis U) :
    LinearMap.toMatrix d.basis.toBasis d.basis.toBasis U.toLinearMap =
      orthogonalBlockForm d.angles := by
  classical
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis]
  change d.basis.repr (U (d.basis j)) i = _
  rcases j with ⟨j, k⟩ | (j | j)
  · fin_cases j
    · change d.basis.repr (U (d.basis (.inl (0, k)))) i =
        orthogonalBlockForm (s := d.fixed) (t := d.reversed) d.angles i (.inl (0, k))
      rw [d.rotation_zero]
      simp only [map_add, map_smul, OrthonormalBasis.repr_self]
      rcases i with ⟨i, l⟩ | (i | i)
      · fin_cases i <;> by_cases h : l = k <;>
          simp [orthogonalBlockForm, Matrix.blockDiagonal_apply, orthogonalRotationBlock, h]
      · simp [orthogonalBlockForm]
      · simp [orthogonalBlockForm]
    · change d.basis.repr (U (d.basis (.inl (1, k)))) i =
        orthogonalBlockForm (s := d.fixed) (t := d.reversed) d.angles i (.inl (1, k))
      rw [d.rotation_one]
      simp only [map_add, map_smul, OrthonormalBasis.repr_self]
      rcases i with ⟨i, l⟩ | (i | i)
      · fin_cases i <;> by_cases h : l = k <;>
          simp [orthogonalBlockForm, Matrix.blockDiagonal_apply, orthogonalRotationBlock, h]
      · simp [orthogonalBlockForm]
      · simp [orthogonalBlockForm]
  · rw [d.fixed_apply]
    simp only [OrthonormalBasis.repr_self]
    rcases i with ⟨i, l⟩ | (i | i) <;> simp [orthogonalBlockForm, Matrix.one_apply]
  · rw [d.reversed_apply]
    simp only [map_neg, OrthonormalBasis.repr_self]
    rcases i with ⟨i, l⟩ | (i | i) <;> simp [orthogonalBlockForm, Matrix.one_apply]

/-- The column action of a real orthogonal matrix, bundled as an orthogonal automorphism. -/
def orthogonalMatrixEquiv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n := by
  let f : Inversive.Euclidean n → Inversive.Euclidean n := fun x => WithLp.toLp 2 (A.mulVec x.ofLp)
  have hAt : Auxiliary.Algebra.OrthogonalMatrix A.transpose :=
    (Auxiliary.Algebra.orthogonalMatrix_iff_mem_orthogonalGroup A.transpose).mpr
      (Matrix.transpose_mem_unitaryGroup_iff.mpr hA)
  have hf : Isometry f := by
    simpa only [add_zero, Matrix.vecMul_transpose] using
      orthogonal_affine_isometry A.transpose hAt 0
  exact (Inversive.euclideanIsometryEquiv f hf).toRealLinearIsometryEquivOfMapZero
    (by simp [f])

theorem orthogonalMatrixEquiv_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (x : Inversive.Euclidean n) :
    orthogonalMatrixEquiv A hA x = WithLp.toLp 2 (A.mulVec x.ofLp) := by
  simp [orthogonalMatrixEquiv,
    IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero]

/-- The bundled action still has the input matrix in the standard coordinate basis. -/
theorem orthogonalMatrixEquiv_toMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (orthogonalMatrixEquiv A hA).toLinearMap =
        A := by
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis]
  change (orthogonalMatrixEquiv A hA ((EuclideanSpace.basisFun (Fin n) ℝ) j)) i = A i j
  rw [orthogonalMatrixEquiv_apply]
  simp [EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct]

/-- Transposing an orthonormal change-of-basis matrix reverses the change of basis. -/
theorem orthonormalBasis_toMatrix_transpose {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (b.toBasis.toMatrix c).transpose = c.toBasis.toMatrix b := by
  ext i j
  simp only [Matrix.transpose_apply, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  exact real_inner_comm _ _

/-- Reindexing a chosen orthonormal coordinate basis reindexes its matrix by the same bijection. -/
theorem orthonormalBasis_toMatrix_reindex {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (e : Fin n ≃ ι) (U : E ≃ₗᵢ[ℝ] E) :
    Matrix.reindex e e (LinearMap.toMatrix (b.reindex e.symm).toBasis
      (b.reindex e.symm).toBasis U.toLinearMap) =
        LinearMap.toMatrix b.toBasis b.toBasis U.toLinearMap := by
  classical
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.reindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    OrthonormalBasis.repr_reindex]

/-- The exact target property, without assuming that a normalizing basis already exists. -/
def HasOrthogonalBlockNormalForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ r s t : ℕ, 2 * r + s + t = n ∧ ∃ θ : Fin r → ℝ,
    ∃ e : Fin n ≃ OrthogonalBlockIndex r s t,
    ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      Q ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
        Matrix.reindex e e (Q * A * Q.transpose) = orthogonalBlockForm θ

/--
Every real orthogonal matrix is orthogonally conjugate to its
planar rotation blocks, positive identity block and negative identity block.
-/
theorem orthogonal_matrix_has_block_normal_form {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Auxiliary.Algebra.OrthogonalMatrix A) : HasOrthogonalBlockNormalForm A := by
  classical
  let U := orthogonalMatrixEquiv A
    ((Auxiliary.Algebra.orthogonalMatrix_iff_mem_orthogonalGroup A).mp hA)
  obtain ⟨d⟩ := exists_orthogonalNormalBasis U
  have hdim : 2 * d.rotations + d.fixed + d.reversed = n := by
    simpa only [finrank_euclideanSpace_fin] using d.dimension U
  have hcard : Fintype.card (Fin n) =
      Fintype.card (OrthogonalBlockIndex d.rotations d.fixed d.reversed) := by
    simpa [OrthogonalBlockIndex, Nat.add_assoc] using hdim.symm
  let e := Fintype.equivOfCardEq hcard
  let b := d.basis.reindex e.symm
  let b₀ := EuclideanSpace.basisFun (Fin n) ℝ
  let Q := b.toBasis.toMatrix b₀
  refine ⟨d.rotations, d.fixed, d.reversed, hdim, d.angles, e, Q,
    b.toMatrix_orthonormalBasis_mem_orthogonal b₀, ?_⟩
  have hconj : Q * A * Q.transpose = LinearMap.toMatrix b.toBasis b.toBasis U.toLinearMap := by
    change b.toBasis.toMatrix b₀ * A * (b.toBasis.toMatrix b₀).transpose = _
    rw [orthonormalBasis_toMatrix_transpose]
    rw [← orthogonalMatrixEquiv_toMatrix A
      ((Auxiliary.Algebra.orthogonalMatrix_iff_mem_orthogonalGroup A).mp hA)]
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      b.toBasis b₀.toBasis b.toBasis b₀.toBasis U.toLinearMap
  rw [hconj, orthonormalBasis_toMatrix_reindex]
  exact d.toMatrix U

end
end LowDimensionalTopology.Geometry.Euclidean
