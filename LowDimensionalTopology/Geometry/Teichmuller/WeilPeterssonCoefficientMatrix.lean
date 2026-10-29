module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonRealCoefficients
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.Linarith

/-!
# The actual Weil–Petersson coefficient matrix and its inverse

The entries are the unchanged original Hermitian form on inverse images of
coordinate vectors under the actual Bers differential. Positivity does not
use local smoothness. This supplies the inverse matrix used in the source's
curvature formulas, without asserting those analytic formulas.

Actual coordinate applications use the chart target. The algebraic statements
also evaluate the total inverse function outside that target.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Matrix
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate ComplexOrder

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3*g-3)
local notation "E" => I → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "H" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "coeff" => nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree hsmooth
local notation "realPair" => nativeWeilPeterssonRealCoordinatePairing R hp hg hgenus hΓ hfree hsmooth

/-- The actual coefficient matrix, with the source's first-linear convention. -/
def nativeWeilPeterssonCoefficientMatrix (a : TeichmullerSpace.{0,0} R) (t : E) :
    Matrix I I ℂ := fun j k => coeff a j k t

local notation "M" => nativeWeilPeterssonCoefficientMatrix R hp hg hgenus hΓ hfree hsmooth

/-- Conjugation exchanges the two original coordinate coefficients. -/
theorem nativeWeilPeterssonLocalCoefficient_conj
    (a : TeichmullerSpace.{0,0} R) (j k : I) (t : E) :
    conj (coeff a j k t) = coeff a k j t := by
  let := C
  let q := (chart a).symm t
  exact (H q).conj_inner_symm
    ((K q).symm (Pi.single j 1)) ((K q).symm (Pi.single k 1))

/-- The original WP matrix is Hermitian in the actual Bers coordinates. -/
theorem nativeWeilPeterssonCoefficientMatrix_isHermitian
    (a : TeichmullerSpace.{0,0} R) (t : E) : (M a t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro j k
  exact nativeWeilPeterssonLocalCoefficient_conj R hp hg hgenus hΓ hfree hsmooth a k j t

private theorem realCoordinatePairing_self_pos
    (a : TeichmullerSpace.{0,0} R) (v t : E) (hv : v ≠ 0) :
    0 < realPair a v v t := by
  let := C
  let q := (chart a).symm t
  let c := H q
  let L := K q
  let x := L.symm v
  have hx : x ≠ 0 := by
    intro hzero
    apply hv
    calc
      v = L x := (L.apply_symm_apply v).symm
      _ = 0 := by rw [hzero, map_zero]
  have hconj := congrArg Complex.im (c.conj_inner_symm x x)
  have him : (c.inner x x).im = 0 := by
    simp only [Complex.conj_im] at hconj
    linarith
  have hpos : 0 < (c.inner x x).re := by
    apply lt_of_le_of_ne (c.re_inner_nonneg x)
    intro heq
    apply hx
    apply c.definite x
    exact Complex.ext heq.symm him
  change 0 < 2 * (c.inner x x).re
  exact mul_pos (by norm_num) hpos

/-- The finite quadratic expansion is strictly positive for every nonzero
actual coordinate vector; no analytic regularity input is assumed. -/
theorem nativeWeilPeterssonCoefficientQuadratic_pos
    (a : TeichmullerSpace.{0,0} R) (v t : E) (hv : v ≠ 0) :
    0 < (∑ j, ∑ k, v j * conj (v k) * coeff a j k t).re := by
  have hpos := realCoordinatePairing_self_pos R hp hg hgenus hΓ hfree hsmooth a v t hv
  rw [nativeWeilPeterssonRealCoordinatePairing_eq_sum] at hpos
  linarith

/-- Positivity is also available in Mathlib's standard matrix convention. -/
theorem nativeWeilPeterssonCoefficientMatrix_posDef
    (a : TeichmullerSpace.{0,0} R) (t : E) : (M a t).PosDef := by
  classical
  have hM := nativeWeilPeterssonCoefficientMatrix_isHermitian
    R hp hg hgenus hΓ hfree hsmooth a t
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hM ?_
  intro v hv
  have hconj : (fun j => conj (v j)) ≠ 0 := by
    intro hzero
    apply hv
    funext j
    have h := congrArg conj (congrFun hzero j)
    simpa using h
  have hpos := nativeWeilPeterssonCoefficientQuadratic_pos
    R hp hg hgenus hΓ hfree hsmooth a (fun j => conj (v j)) t hconj
  have hsum : star v ⬝ᵥ ((M a t) *ᵥ v) =
      ∑ j, ∑ k, conj (v j) * conj (conj (v k)) * coeff a j k t := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def,
      nativeWeilPeterssonCoefficientMatrix, Complex.conj_conj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hc := congrArg Complex.im (hM.star_dotProduct_mulVec_comm v v)
  have him : (star v ⬝ᵥ ((M a t) *ᵥ v)).im = 0 := by
    simp only [RCLike.star_def, Complex.conj_im] at hc
    linarith
  exact Complex.pos_iff.mpr ⟨by rwa [hsum], him.symm⟩

/-- The inverse used in the source is the genuine inverse of this matrix. -/
theorem nativeWeilPeterssonCoefficientMatrix_det_ne_zero
    (a : TeichmullerSpace.{0,0} R) (t : E) : (M a t).det ≠ 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (nativeWeilPeterssonCoefficientMatrix_posDef R hp hg hgenus hΓ hfree hsmooth a t).isUnit).ne_zero

/-- The actual inverse coefficient matrix is positive definite as well. -/
theorem nativeWeilPeterssonCoefficientMatrix_inverse_posDef
    (a : TeichmullerSpace.{0,0} R) (t : E) : (M a t)⁻¹.PosDef :=
  (nativeWeilPeterssonCoefficientMatrix_posDef R hp hg hgenus hΓ hfree hsmooth a t).inv

/-- Both inverse identities hold for the unchanged coefficient matrix. -/
theorem nativeWeilPeterssonCoefficientMatrix_inverse_identities
    (a : TeichmullerSpace.{0,0} R) (t : E) :
    (M a t)⁻¹ * M a t = 1 ∧ M a t * (M a t)⁻¹ = 1 := by
  have hdet : IsUnit (M a t).det := isUnit_iff_ne_zero.mpr
    (nativeWeilPeterssonCoefficientMatrix_det_ne_zero R hp hg hgenus hΓ hfree hsmooth a t)
  exact ⟨Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet⟩

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
