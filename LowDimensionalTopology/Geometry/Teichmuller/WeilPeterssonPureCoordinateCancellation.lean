module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCoordinateExpressions
public import LowDimensionalTopology.Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! The pure holomorphic coordinate cancellation for the original WP coefficients.
The intermediate premise concerns differentiability of the actual expression;
the native regularity consumer supplies it from original coefficient smoothness. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Matrix
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
local notation "Dz" => nativeWeilPeterssonCoordinateDz (g := g)
local notation "H" => nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree hsmooth
local notation "G" => nativeWeilPeterssonChristoffelExpression R hp hg hgenus hΓ hfree hsmooth
local notation "M" => nativeWeilPeterssonCoefficientMatrix R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth

private theorem coordinateDz_mul (f₁ f₂ : E → ℂ) (r : I) (t : E)
    (h₁ : DifferentiableAt ℝ f₁ t) (h₂ : DifferentiableAt ℝ f₂ t) :
    Dz (fun s => f₁ s * f₂ s) r t = Dz f₁ r t * f₂ t + f₁ t * Dz f₂ r t := by
  simp only [nativeWeilPeterssonCoordinateDz, fderiv_fun_mul h₁ h₂,
    _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

private theorem coordinateDz_sum (f : I → E → ℂ) (r : I) (t : E)
    (hf : ∀ j, DifferentiableAt ℝ (f j) t) :
    Dz (fun s => ∑ j, f j s) r t = ∑ j, Dz (f j) r t := by
  classical
  unfold nativeWeilPeterssonCoordinateDz
  simp only [fderiv_fun_sum (fun j _ => hf j), _root_.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

private theorem coordinateDz_comm (f : E → ℂ) (t : E)
    (hf : ContDiffAt ℝ 2 f t) (r l : I) :
    Dz (fun s => Dz f l s) r t = Dz (fun s => Dz f r s) l t := by
  let DD := fderiv ℝ (fderiv ℝ f) t
  have hsym : ∀ u v : E, DD u v = DD v u :=
    hf.isSymmSndFDerivAt (by simp)
  have hL : DifferentiableAt ℝ (fderiv ℝ f) t :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heval (b : E) : HasFDerivAt (fun s => fderiv ℝ f s b) (DD.flip b) t := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      hL.hasFDerivAt.clm_apply (hasFDerivAt_const b t)
  have hDz (b : I) (u : E) :
      fderiv ℝ (fun s => Dz f b s) t u =
        (DD u (Pi.single b 1) - Complex.I * DD u (Pi.single b Complex.I)) / 2 := by
    have hh := ((heval (Pi.single b 1)).sub
      ((heval (Pi.single b Complex.I)).const_mul Complex.I)).mul_const (2 : ℂ)⁻¹
    simpa only [nativeWeilPeterssonCoordinateDz, div_eq_mul_inv,
      _root_.smul_apply, _root_.sub_apply, Pi.sub_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul, mul_comm] using
      congrArg (fun L : E →L[ℝ] ℂ => L u) hh.fderiv
  change (fderiv ℝ (fun s => Dz f l s) t (Pi.single r 1) -
      Complex.I * fderiv ℝ (fun s => Dz f l s) t (Pi.single r Complex.I)) / 2 =
    (fderiv ℝ (fun s => Dz f r s) t (Pi.single l 1) -
      Complex.I * fderiv ℝ (fun s => Dz f r s) t (Pi.single l Complex.I)) / 2
  rw [hDz l (Pi.single r 1), hDz l (Pi.single r Complex.I),
    hDz r (Pi.single l 1), hDz r (Pi.single l Complex.I)]
  rw [hsym (Pi.single r 1) (Pi.single l 1),
    hsym (Pi.single r 1) (Pi.single l Complex.I),
    hsym (Pi.single r Complex.I) (Pi.single l 1),
    hsym (Pi.single r Complex.I) (Pi.single l Complex.I)]
  ring

/-- Differentiating the actual first-linear metric equation and cancelling its
actual positive coefficient matrix gives the pure holomorphic cancellation. -/
theorem nativeWeilPeterssonChristoffelExpression_pureHolomorphic_of_differentiable
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (a : TeichmullerSpace.{0,0} R) (t : E) (ht : t ∈ (chart a).target)
    (hG : ∀ j k l, DifferentiableAt ℝ (G a j k l) t) (j k l r : I) :
    Dz (G a j k l) r t - Dz (G a j k r) l t +
      (∑ n, G a j n r t * G a n k l t) -
      (∑ n, G a j n l t * G a n k r t) = 0 := by
  classical
  have hH (b c : I) : ContDiffAt ℝ 2 (H a b c) t :=
    ((hWP a b c).contDiffAt ((chart a).open_target.mem_nhds ht)).of_le (by simp)
  have hdH (b c : I) : DifferentiableAt ℝ (H a b c) t :=
    (hH b c).differentiableAt (by simp)
  have hder (b c q : I) :
      (∑ n, (Dz (G a n k c) b t * H a n q t +
        G a n k c t * Dz (H a n q) b t)) =
      Dz (fun s => Dz (H a k q) c s) b t := by
    have hfun : (fun s => ∑ n, G a n k c s * H a n q s) =
        (fun s => Dz (H a k q) c s) :=
      funext (nativeWeilPeterssonChristoffelExpression_contract
        R hp hg hgenus hΓ hfree hsmooth a k c q)
    calc
      _ = Dz (fun s => ∑ n, G a n k c s * H a n q s) b t := by
        rw [coordinateDz_sum (fun n s => G a n k c s * H a n q s) b t
          (fun n => (hG n k c).mul (hdH n q))]
        apply Finset.sum_congr rfl
        intro n _
        exact (coordinateDz_mul _ _ b t (hG n k c) (hdH n q)).symm
      _ = _ := congrArg (fun f : E → ℂ => Dz f b t) hfun
  let C : I → ℂ := fun i =>
    Dz (G a i k l) r t - Dz (G a i k r) l t +
      (∑ n, G a i n r t * G a n k l t) -
      (∑ n, G a i n l t * G a n k r t)
  have hzero (q : I) : (∑ i, C i * H a i q t) = 0 := by
    have hquad (b c : I) :
        (∑ i, (∑ n, G a i n b t * G a n k c t) * H a i q t) =
        ∑ n, G a n k c t * Dz (H a n q) b t := by
      calc
        _ = ∑ n, G a n k c t * (∑ i, G a i n b t * H a i q t) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro n _
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by simp_rw [nativeWeilPeterssonChristoffelExpression_contract]
    calc
      _ = (∑ i, (Dz (G a i k l) r t * H a i q t +
            G a i k l t * Dz (H a i q) r t)) -
          (∑ i, (Dz (G a i k r) l t * H a i q t +
            G a i k r t * Dz (H a i q) l t)) := by
        dsimp only [C]
        simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [hquad r l, hquad l r]
        ring
      _ = Dz (fun s => Dz (H a k q) l s) r t -
          Dz (fun s => Dz (H a k q) r s) l t := by rw [hder r l q, hder l r q]
      _ = 0 := sub_eq_zero.mpr (coordinateDz_comm _ t (hH k q) r l)
  have hz : C ᵥ* M a t = 0 := by
    funext q
    exact hzero q
  have hC : C = 0 := by
    calc
      C = (C ᵥ* M a t) ᵥ* (M a t)⁻¹ := by
        rw [Matrix.vecMul_vecMul,
          (nativeWeilPeterssonCoefficientMatrix_inverse_identities
            R hp hg hgenus hΓ hfree hsmooth a t).2, Matrix.vecMul_one]
      _ = 0 := by rw [hz]; simp
  exact congrArg (fun f : I → ℂ => f j) hC

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
