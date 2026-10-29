module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCoefficientMatrix
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Ring

/-!
# Finite coordinate expressions from the actual Weil–Petersson coefficients

All coefficients come from the original WP form in the actual Bers chart.
Raised Hermitian indices use the transpose of the ordinary inverse matrix;
the contraction identities below make this convention explicit.

The derivative-based formulas are total coordinate expressions. They do not
construct a covariant derivative or identify any expression with the curvature
of a Levi-Civita connection. Their geometric interpretation also requires
regularity, the Kahler identity and compatibility with the original real metric.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix
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
local notation "coeff" => nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree hsmooth
local notation "M" => nativeWeilPeterssonCoefficientMatrix R hp hg hgenus hΓ hfree hsmooth

/-- The holomorphic coordinate slot, defined from the real Frechet derivative.
This is a total function; genuine differentiability is a separate assertion. -/
def nativeWeilPeterssonCoordinateDz (f : E → ℂ) (l : I) (t : E) : ℂ :=
  (fderiv ℝ f t (Pi.single l 1) -
    Complex.I * fderiv ℝ f t (Pi.single l Complex.I)) / 2

/-- The antiholomorphic coordinate slot of the same real derivative. -/
def nativeWeilPeterssonCoordinateDbar (f : E → ℂ) (l : I) (t : E) : ℂ :=
  (fderiv ℝ f t (Pi.single l 1) +
    Complex.I * fderiv ℝ f t (Pi.single l Complex.I)) / 2

local notation "Dz" => nativeWeilPeterssonCoordinateDz (g := g)
local notation "Dbar" => nativeWeilPeterssonCoordinateDbar (g := g)

private theorem coordinateDbar_conj (f : E → ℂ) (l : I) (t : E) :
    Dbar (fun s => conj (f s)) l t = conj (Dz f l t) := by
  have hconj (v : E) :
      fderiv ℝ (fun s => conj (f s)) t v = conj (fderiv ℝ f t v) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply] using
      congrArg (fun L : E →L[ℝ] ℂ => L v)
        (Complex.conjCLE.comp_fderiv (f := f) (x := t))
  unfold nativeWeilPeterssonCoordinateDbar nativeWeilPeterssonCoordinateDz
  rw [hconj, hconj]
  simp only [map_div₀, map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring

/-- Differentiation of the actual Hermitian coefficient symmetry exchanges
the holomorphic and antiholomorphic coordinate slots. -/
theorem nativeWeilPeterssonCoefficientDz_conj
    (a : TeichmullerSpace.{0,0} R) (j k l : I) (t : E) :
    conj (Dz (coeff a j k) l t) = Dbar (coeff a k j) l t := by
  have hfun : (fun s => conj (coeff a j k s)) = coeff a k j :=
    funext (nativeWeilPeterssonLocalCoefficient_conj
      R hp hg hgenus hΓ hfree hsmooth a j k)
  rw [← hfun]
  exact (coordinateDbar_conj (coeff a j k) l t).symm

/-- A raised Hermitian index pair. Its ordinary matrix entry is explicitly
`(M a t)⁻¹ m j`, with the two array indices exchanged. -/
def nativeWeilPeterssonRaisedInverseCoefficient
    (a : TeichmullerSpace.{0,0} R) (j m : I) (t : E) : ℂ :=
  (M a t)⁻¹ m j

local notation "raised" =>
  nativeWeilPeterssonRaisedInverseCoefficient R hp hg hgenus hΓ hfree hsmooth

/-- The explicit conversion between raised tensor indices and array indices. -/
@[simp] theorem nativeWeilPeterssonRaisedInverseCoefficient_eq
    (a : TeichmullerSpace.{0,0} R) (j m : I) (t : E) :
    raised a j m t = (M a t)⁻¹ m j := rfl

/-- The actual raised coefficients retain Hermitian conjugate symmetry. -/
theorem nativeWeilPeterssonRaisedInverseCoefficient_conj
    (a : TeichmullerSpace.{0,0} R) (j m : I) (t : E) :
    conj (raised a j m t) = raised a m j t := by
  have h := (nativeWeilPeterssonCoefficientMatrix_inverse_posDef
    R hp hg hgenus hΓ hfree hsmooth a t).isHermitian.apply j m
  simpa only [nativeWeilPeterssonRaisedInverseCoefficient, RCLike.star_def] using h

/-- This contraction fixes the raised-index convention against the unchanged
first-linear coefficient matrix. Invertibility follows from its positivity. -/
theorem nativeWeilPeterssonRaisedInverseCoefficient_contract
    (a : TeichmullerSpace.{0,0} R) (m k : I) (t : E) :
    (∑ j, raised a j m t * coeff a j k t) = (1 : Matrix I I ℂ) m k := by
  change ((M a t)⁻¹ * M a t) m k = _
  rw [(nativeWeilPeterssonCoefficientMatrix_inverse_identities
    R hp hg hgenus hΓ hfree hsmooth a t).1]

/-- The other contraction follows from the genuine two-sided inverse. -/
theorem nativeWeilPeterssonRaisedInverseCoefficient_contract_right
    (a : TeichmullerSpace.{0,0} R) (j k : I) (t : E) :
    (∑ m, coeff a j m t * raised a k m t) = (1 : Matrix I I ℂ) j k := by
  change (M a t * (M a t)⁻¹) j k = _
  rw [(nativeWeilPeterssonCoefficientMatrix_inverse_identities
    R hp hg hgenus hΓ hfree hsmooth a t).2]

/-- The Hermitian coordinate Christoffel expression with a raised tensor
index. Identifying it with a connection requires the geometric bridge. -/
def nativeWeilPeterssonChristoffelExpression
    (a : TeichmullerSpace.{0,0} R) (j k l : I) (t : E) : ℂ :=
  ∑ m, raised a j m t * Dz (coeff a k m) l t

local notation "G" =>
  nativeWeilPeterssonChristoffelExpression R hp hg hgenus hΓ hfree hsmooth

/-- The raised-index expression solves the actual first-linear coefficient
equation; the ordinary inverse is contracted on its correct side. -/
theorem nativeWeilPeterssonChristoffelExpression_contract
    (a : TeichmullerSpace.{0,0} R) (k l r : I) (t : E) :
    (∑ j, G a j k l t * coeff a j r t) = Dz (coeff a k r) l t := by
  let d : I → ℂ := fun m => Dz (coeff a k m) l t
  have hG : (fun j => G a j k l t) = d ᵥ* (M a t)⁻¹ := by
    funext j
    change (∑ m, (M a t)⁻¹ m j * d m) = ∑ m, d m * (M a t)⁻¹ m j
    simp only [mul_comm]
  change ((fun j => G a j k l t) ᵥ* M a t) r = d r
  rw [hG, Matrix.vecMul_vecMul,
    (nativeWeilPeterssonCoefficientMatrix_inverse_identities
      R hp hg hgenus hΓ hfree hsmooth a t).1, Matrix.vecMul_one]

/-- The mixed coordinate expression with its final antiholomorphic slot.
This definition alone does not assert that it is geometric WP curvature. -/
def nativeWeilPeterssonMixedCurvatureExpression
    (a : TeichmullerSpace.{0,0} R) (j k l m : I) (t : E) : ℂ :=
  -Dbar (G a j k l) m t

local notation "U" =>
  nativeWeilPeterssonMixedCurvatureExpression R hp hg hgenus hΓ hfree hsmooth

/-- The fully lowered coordinate expression. Conjugation applies to the entire
mixed coefficient, whose last two lower slots have been interchanged. -/
def nativeWeilPeterssonLoweredCurvatureExpression
    (a : TeichmullerSpace.{0,0} R) (j k l m : I) (t : E) : ℂ :=
  -∑ n, coeff a j n t * conj (U a n k m l t)

local notation "L" =>
  nativeWeilPeterssonLoweredCurvatureExpression R hp hg hgenus hΓ hfree hsmooth

/-- Raising the lowered expression recovers exactly the negative conjugate
mixed coefficient, including the interchange of its last two slots. -/
theorem nativeWeilPeterssonLoweredCurvatureExpression_raise
    (a : TeichmullerSpace.{0,0} R) (r k l m : I) (t : E) :
    (∑ j, raised a j r t * L a j k l m t) = -conj (U a r k m l t) := by
  let v : I → ℂ := fun n => conj (U a n k m l t)
  have hL : (fun j => L a j k l m t) = -(M a t *ᵥ v) := by
    funext j
    rfl
  change ((M a t)⁻¹ *ᵥ (fun j => L a j k l m t)) r = -(v r)
  simp only [hL, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
    (nativeWeilPeterssonCoefficientMatrix_inverse_identities
      R hp hg hgenus hΓ hfree hsmooth a t).1, Matrix.one_mulVec, Pi.neg_apply]

/-- The coordinate Ricci contraction of the mixed expression. -/
def nativeWeilPeterssonRicciExpression
    (a : TeichmullerSpace.{0,0} R) (j k : I) (t : E) : ℂ :=
  ∑ l, U a l j l k t

local notation "Ric" =>
  nativeWeilPeterssonRicciExpression R hp hg hgenus hΓ hfree hsmooth

/-- The two coordinate Ricci contractions agree by actual inverse-matrix
cancellation. This does not use or presume any curvature negativity. -/
theorem nativeWeilPeterssonRicciExpression_eq_lowered_contraction
    (a : TeichmullerSpace.{0,0} R) (j k : I) (t : E) :
    Ric a j k t = -∑ l, ∑ r, raised a l r t * conj (L a r j k l t) := by
  change (∑ l, U a l j l k t) = _
  calc
    (∑ l, U a l j l k t) =
        ∑ l, -conj (∑ r, raised a r l t * L a r j k l t) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [nativeWeilPeterssonLoweredCurvatureExpression_raise]
      simp only [map_neg, Complex.conj_conj, neg_neg]
    _ = -∑ l, ∑ r, raised a l r t * conj (L a r j k l t) := by
      simp only [map_sum, map_mul, nativeWeilPeterssonRaisedInverseCoefficient_conj]
      exact Finset.sum_neg_distrib _

/-- The Ricci quadratic expression on a coordinate vector. A geometric Ricci
curvature additionally requires a unit vector and the connection bridge. -/
def nativeWeilPeterssonDirectionalRicciExpression
    (a : TeichmullerSpace.{0,0} R) (v t : E) : ℂ :=
  ∑ j, ∑ k, Ric a j k t * v j * conj (v k)

/-- The holomorphic sectional quartic expression, with the leading minus
sign and both conjugated vector slots retained. Its codomain stays complex
until the missing curvature symmetries establish reality. -/
def nativeWeilPeterssonHolomorphicSectionalExpression
    (a : TeichmullerSpace.{0,0} R) (v t : E) : ℂ :=
  -∑ j, ∑ k, ∑ l, ∑ m, L a j k l m t * v j * conj (v k) * v l * conj (v m)

/-- The displayed diagonal Ricci trace. Its identification with an invariant
scalar curvature requires orthonormal coordinates at the evaluation point. -/
def nativeWeilPeterssonRicciDiagonalTraceExpression
    (a : TeichmullerSpace.{0,0} R) (t : E) : ℂ :=
  ∑ j, Ric a j j t

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
