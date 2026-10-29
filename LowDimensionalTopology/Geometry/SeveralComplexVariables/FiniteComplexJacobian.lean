module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Determinant

/-!
# The actual complex Jacobian in standard finite coordinates

The entries are the original complex derivative evaluated on the original
standard basis. Analyticity follows from the finite determinant formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped BigOperators

namespace LowDimensionalTopology.Geometry.SeveralComplexVariables

/-- The determinant of the original complex derivative in standard coordinates. -/
def finiteComplexJacobian {n : ℕ}
    (F : (Fin n → ℂ) → (Fin n → ℂ)) (z : Fin n → ℂ) : ℂ :=
  Matrix.det (fun i j => (fderiv ℂ F z) (Pi.single j 1) i)

/-- The standard-coordinate formula is the determinant of the actual derivative. -/
theorem finiteComplexJacobian_eq_det_fderiv {n : ℕ}
    (F : (Fin n → ℂ) → (Fin n → ℂ)) (z : Fin n → ℂ) :
    finiteComplexJacobian F z = LinearMap.det (fderiv ℂ F z).toLinearMap :=
  LinearMap.det_toMatrix' (fderiv ℂ F z).toLinearMap

/-- Nonsingularity of the original Jacobian is equivalent to injectivity of
its actual derivative, without an analytic or rank assumption. -/
theorem finiteComplexJacobian_ne_zero_iff {n : ℕ}
    (F : (Fin n → ℂ) → (Fin n → ℂ)) (z : Fin n → ℂ) :
    finiteComplexJacobian F z ≠ 0 ↔ Function.Injective (fderiv ℂ F z) := by
  rw [finiteComplexJacobian_eq_det_fderiv, ne_eq,
    LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot,
    ContinuousLinearMap.coe_coe]

/-- The original Jacobian is analytic wherever the original vector map is analytic. -/
theorem analyticOnNhd_finiteComplexJacobian {n : ℕ}
    {D : Set (Fin n → ℂ)} {F : (Fin n → ℂ) → (Fin n → ℂ)}
    (hF : AnalyticOnNhd ℂ F D) : AnalyticOnNhd ℂ (finiteComplexJacobian F) D := by
  intro z hz
  have hentry (i j : Fin n) :
      AnalyticAt ℂ (fun q => (fderiv ℂ F q) (Pi.single j 1) i) z := by
    let ev : ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.apply ℂ (Fin n → ℂ) (Pi.single j 1))
    exact (ev.analyticAt (fderiv ℂ F z)).comp (hF z hz).fderiv
  have hJac : finiteComplexJacobian F =
      (fun q => ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∏ j : Fin n, (fderiv ℂ F q) (Pi.single j 1) (σ j)) := by
    funext q
    exact Matrix.det_apply' (fun i j => (fderiv ℂ F q) (Pi.single j 1) i)
  rw [hJac]
  apply Finset.analyticAt_fun_sum
  intro σ _hσ
  have hprod := Finset.univ.analyticAt_fun_prod
    (fun j (_hj : j ∈ (Finset.univ : Finset (Fin n))) => hentry (σ j) j)
  simpa only [Pi.mul_def] using analyticAt_const.mul hprod

end LowDimensionalTopology.Geometry.SeveralComplexVariables
