/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.Group
public import LowDimensionalTopology.Geometry.Auxiliary.Algebra.Matrix
/-!
A Euclidean isometry is exactly an affine map with an orthogonal row matrix.
The finite-dimensional argument also includes dimension zero and does not
assume surjectivity of the input distance-preserving map.
-/

@[expose] public section
noncomputable section
namespace LowDimensionalTopology.Geometry.Euclidean
variable {n : ℕ}

def isometryRowMatrix (φ : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ.toLinearMap).transpose

theorem isometryRowMatrix_apply (φ : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) (x : Inversive.Euclidean n) :
    WithLp.toLp 2 (Matrix.vecMul x.ofLp (isometryRowMatrix φ)) = φ x := by
  apply WithLp.ofLp_injective
  rw [isometryRowMatrix, Matrix.vecMul_transpose]
  have h := LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis φ.toLinearMap x
  exact h

theorem isometryRowMatrix_orthogonal (φ : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) :
    Auxiliary.Algebra.OrthogonalMatrix (isometryRowMatrix φ) := by
  intro x
  rw [isometryRowMatrix_apply, φ.norm_map]

theorem euclideanIsometry_orthogonal_affine (f : Inversive.Euclidean n → Inversive.Euclidean n) (hf : Isometry f) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, Auxiliary.Algebra.OrthogonalMatrix A ∧
      ∀ x, f x = WithLp.toLp 2 (Matrix.vecMul x.ofLp A) + f 0 := by
  let F := (Inversive.euclideanIsometryEquiv f hf).toRealAffineIsometryEquiv
  let φ := F.linearIsometryEquiv
  refine ⟨isometryRowMatrix φ, isometryRowMatrix_orthogonal φ, ?_⟩
  intro x
  rw [isometryRowMatrix_apply]
  have hF (y : Inversive.Euclidean n) : F y = f y := by
    change Inversive.euclideanIsometryEquiv f hf y = f y
    rfl
  have h := F.map_vadd 0 x
  simp only [vadd_eq_add, add_zero, hF] at h
  exact h

theorem orthogonal_affine_isometry (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Auxiliary.Algebra.OrthogonalMatrix A) (b : Inversive.Euclidean n) :
    Isometry (fun x : Inversive.Euclidean n => WithLp.toLp 2 (Matrix.vecMul x.ofLp A) + b) := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  simp only [dist_eq_norm, add_sub_add_right_eq_sub]
  have h : WithLp.toLp 2 (Matrix.vecMul x.ofLp A) -
      WithLp.toLp 2 (Matrix.vecMul y.ofLp A) =
      WithLp.toLp 2 (Matrix.vecMul (x-y).ofLp A) := by
    apply WithLp.ofLp_injective
    change Matrix.vecMul x.ofLp A - Matrix.vecMul y.ofLp A = _
    rw [← Matrix.sub_vecMul]
    rfl
  rw [h]
  exact hA (x-y)

theorem isometry_iff_orthogonal_matrix_add_translation (f : Inversive.Euclidean n → Inversive.Euclidean n) :
    Isometry f ↔ ∃ A : Matrix (Fin n) (Fin n) ℝ, ∃ b : Inversive.Euclidean n,
      Auxiliary.Algebra.OrthogonalMatrix A ∧
      ∀ x, f x = WithLp.toLp 2 (Matrix.vecMul x.ofLp A) + b := by
  constructor
  · intro hf
    obtain ⟨A, hA, h⟩ := euclideanIsometry_orthogonal_affine f hf
    exact ⟨A, f 0, hA, h⟩
  · rintro ⟨A, b, hA, hf⟩
    have hfun : f = fun x => WithLp.toLp 2 (Matrix.vecMul x.ofLp A) + b := funext hf
    rw [hfun]
    exact orthogonal_affine_isometry A hA b
end LowDimensionalTopology.Geometry.Euclidean
