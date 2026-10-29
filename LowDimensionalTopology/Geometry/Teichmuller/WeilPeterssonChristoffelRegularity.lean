module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCoordinateExpressions
public import LowDimensionalTopology.Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Regularity of the original WP Christoffel coefficients on their actual chart target.
Only the original coefficient smoothness input is used; no connection comparison is assumed. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff
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
local notation "H" => nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree hsmooth
local notation "M" => nativeWeilPeterssonCoefficientMatrix R hp hg hgenus hΓ hfree hsmooth
local notation "raised" => nativeWeilPeterssonRaisedInverseCoefficient R hp hg hgenus hΓ hfree hsmooth
local notation "G" => nativeWeilPeterssonChristoffelExpression R hp hg hgenus hΓ hfree hsmooth
local notation "Dz" => nativeWeilPeterssonCoordinateDz (g := g)
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth

/-- The unchanged transposed inverse entry is smooth, using its finite adjugate formula. -/
theorem contDiffOn_nativeWeilPeterssonRaisedInverseCoefficient_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (a : TeichmullerSpace.{0,0} R) (j m : I) :
    ContDiffOn ℝ ∞ (raised a j m) (chart a).target := by
  classical
  have hdet : ContDiffOn ℝ ∞ (fun t : E => (M a t).det) (chart a).target := by
    simp_rw [Matrix.det_apply']
    exact ContDiffOn.sum fun σ _ =>
      contDiffOn_const.mul (contDiffOn_prod fun i _ => hWP a (σ i) i)
  have hadj : ContDiffOn ℝ ∞
      (fun t : E => (M a t).adjugate m j) (chart a).target := by
    simp_rw [Matrix.adjugate_apply, Matrix.det_apply']
    apply ContDiffOn.sum
    intro σ _
    apply contDiffOn_const.mul
    apply contDiffOn_prod
    intro i _
    by_cases hi : σ i = j
    · simp only [Matrix.updateRow_apply, hi]
      exact contDiffOn_const
    · simp only [Matrix.updateRow_apply, ite_eq_right hi,
        nativeWeilPeterssonCoefficientMatrix]
      exact hWP a (σ i) i
  have hinv : ContDiffOn ℝ ∞ (fun t : E => (M a t).det⁻¹) (chart a).target :=
    hdet.inv fun t _ => nativeWeilPeterssonCoefficientMatrix_det_ne_zero
      R hp hg hgenus hΓ hfree hsmooth a t
  apply (hinv.mul hadj).congr
  intro t _
  simp only [nativeWeilPeterssonRaisedInverseCoefficient, Matrix.inv_def,
    Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]

/-- The actual Christoffel coefficients are real smooth on the genuine open Bers target. -/
theorem contDiffOn_nativeWeilPeterssonChristoffelExpression_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (a : TeichmullerSpace.{0,0} R) (j k l : I) :
    ContDiffOn ℝ ∞ (G a j k l) (chart a).target := by
  classical
  change ContDiffOn ℝ ∞
    (fun t : E => ∑ m, raised a j m t * Dz (H a k m) l t) (chart a).target
  apply ContDiffOn.sum
  intro m _
  apply (contDiffOn_nativeWeilPeterssonRaisedInverseCoefficient_of_localSmoothness
    R hp hg hgenus hΓ hfree hsmooth hWP a j m).mul
  have hD := ((contDiffOn_infty_iff_fderiv_of_isOpen (chart a).open_target).mp
    (hWP a k m)).2
  have h₁ : ContDiffOn ℝ ∞
      (fun t : E => fderiv ℝ (H a k m) t (Pi.single l 1)) (chart a).target :=
    hD.clm_apply contDiffOn_const
  have hI : ContDiffOn ℝ ∞
      (fun t : E => fderiv ℝ (H a k m) t (Pi.single l Complex.I)) (chart a).target :=
    hD.clm_apply contDiffOn_const
  apply ((h₁.sub ((contDiffOn_const (c := Complex.I)).mul hI)).div_const (2 : ℂ)).congr
  intro t _
  simp only [nativeWeilPeterssonCoordinateDz]

/-- In particular the actual coefficient expression has genuine pointwise derivatives in its target. -/
theorem differentiableAt_nativeWeilPeterssonChristoffelExpression_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (a : TeichmullerSpace.{0,0} R) (j k l : I) (t : E) (ht : t ∈ (chart a).target) :
    DifferentiableAt ℝ (G a j k l) t := by
  exact ((contDiffOn_nativeWeilPeterssonChristoffelExpression_of_localSmoothness
    R hp hg hgenus hΓ hfree hsmooth hWP a j k l).contDiffAt
      ((chart a).open_target.mem_nhds ht)).differentiableAt (by simp)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
