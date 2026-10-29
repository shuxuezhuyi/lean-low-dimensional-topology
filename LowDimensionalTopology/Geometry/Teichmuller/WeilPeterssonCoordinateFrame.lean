module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCoordinateExpressions
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# A complete complex frame for the actual Weil–Petersson coefficients

The square root of the transposed inverse metric gives a genuine complex
coordinate basis. Only finite matrix algebra is used; the norm and tangent
objects are unchanged. This does not identify any expression with curvature.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix
open scoped UpperHalfPlane ComplexConjugate ComplexOrder MatrixOrder

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

private theorem inverse_transpose_frame {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.PosDef) :
    ∃ b : Module.Basis (Fin n) ℂ (Fin n → ℂ),
      ∀ l r, M⁻¹ r l = ∑ α, b α l * conj (b α r) := by
  classical
  let A := (M⁻¹)ᵀ
  have hA : A.PosDef := hM.inv.transpose
  let S := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hunit : IsUnit S := isUnit_mul_self_iff.mp (hSS.symm ▸ hA.isUnit)
  let e := Matrix.toLinearEquiv (Pi.basisFun ℂ (Fin n)) S
    ((Matrix.isUnit_iff_isUnit_det S).mp hunit)
  let b := (Pi.basisFun ℂ (Fin n)).map e
  have hb (α l : Fin n) : b α l = S l α := by
    change (e ((Pi.basisFun ℂ (Fin n)) α)) l = S l α
    change (Matrix.toLin (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) S
      ((Pi.basisFun ℂ (Fin n)) α)) l = S l α
    simp only [Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Pi.basisFun_apply,
      Matrix.mulVec_single_one, Matrix.col_apply]
  refine ⟨b, fun l r => ?_⟩
  change A l r = _
  calc
    A l r = (S * Sᴴ) l r := by rw [hS.isHermitian.eq, hSS]
    _ = ∑ α, b α l * conj (b α r) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, hb]

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3*g-3)
local notation "E" => I → ℂ
local notation "M" => nativeWeilPeterssonCoefficientMatrix R hp hg hgenus hΓ hfree hsmooth
local notation "raised" =>
  nativeWeilPeterssonRaisedInverseCoefficient R hp hg hgenus hΓ hfree hsmooth

/-- A genuine complex coordinate basis with completeness for the unchanged
raised metric coefficients. Existence uses the original positive WP matrix. -/
theorem nativeWeilPeterssonCoordinateFrame_exists
    (a : TeichmullerSpace.{0,0} R) (t : E) :
    ∃ b : Module.Basis I ℂ E,
      ∀ l r, raised a l r t = ∑ α, b α l * conj (b α r) := by
  exact inverse_transpose_frame (M a t)
    (nativeWeilPeterssonCoefficientMatrix_posDef R hp hg hgenus hΓ hfree hsmooth a t)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
