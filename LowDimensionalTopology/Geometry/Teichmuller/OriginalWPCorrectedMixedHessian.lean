module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonChristoffelRegularity
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSourceKernels
public import Mathlib.Tactic.Ring

/-!
# The corrected mixed Hessian of the actual WP coefficients

Differentiating the actual first-linear Christoffel contraction and taking
its whole conjugate eliminates the connection derivative. The remaining
inverse correction is retained on every genuine original coordinate target.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Matrix
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "Dz" => nativeWeilPeterssonCoordinateDz (g := g)
local notation "Dbar" => nativeWeilPeterssonCoordinateDbar (g := g)
local notation "H" => nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree hsmooth
local notation "M" => nativeWeilPeterssonCoefficientMatrix R hp hg hgenus hΓ hfree hsmooth
local notation "G" => nativeWeilPeterssonChristoffelExpression R hp hg hgenus hΓ hfree hsmooth
local notation "L" => nativeWeilPeterssonLoweredCurvatureExpression
  R hp hg hgenus hΓ hfree hsmooth
local notation "C4" => nativeWeilPeterssonLoweredContraction R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth

private theorem coordinateDbar_mul (f₁ f₂ : E → ℂ) (r : I) (t : E)
    (h₁ : DifferentiableAt ℝ f₁ t) (h₂ : DifferentiableAt ℝ f₂ t) :
    Dbar (fun s => f₁ s * f₂ s) r t =
      Dbar f₁ r t * f₂ t + f₁ t * Dbar f₂ r t := by
  simp only [nativeWeilPeterssonCoordinateDbar, fderiv_fun_mul h₁ h₂,
    _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

private theorem coordinateDbar_sum (f : I → E → ℂ) (r : I) (t : E)
    (hf : ∀ j, DifferentiableAt ℝ (f j) t) :
    Dbar (fun s => ∑ j, f j s) r t = ∑ j, Dbar (f j) r t := by
  classical
  unfold nativeWeilPeterssonCoordinateDbar
  simp only [fderiv_fun_sum (fun j _ => hf j), _root_.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]

private theorem coordinateDz_conj (f : E → ℂ) (r : I) (t : E) :
    Dz (fun s => conj (f s)) r t = conj (Dbar f r t) := by
  have hconj (v : E) :
      fderiv ℝ (fun s => conj (f s)) t v = conj (fderiv ℝ f t v) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using
      congrArg (fun A : E →L[ℝ] ℂ => A v)
        (Complex.conjCLE.comp_fderiv (f := f) (x := t))
  unfold nativeWeilPeterssonCoordinateDz nativeWeilPeterssonCoordinateDbar
  rw [hconj, hconj]
  simp only [map_div₀, map_add, map_mul, Complex.conj_I, map_ofNat]
  ring

/-- The unchanged fully lowered expression is the actual mixed Hessian
minus its original inverse-matrix correction on every genuine chart target. -/
theorem nativeWeilPeterssonLoweredCurvatureExpression_eq_corrected_mixed
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (a : TeichmullerSpace.{0,0} R) (t : E) (ht : t ∈ (chart a).target)
    (j k l m : I) :
    L a j k l m t = Dz (fun s => Dbar (H a j k) m s) l t -
      ∑ n, ∑ r, Dz (H a j n) l t * (M a t)⁻¹ n r * Dbar (H a r k) m t := by
  classical
  have hH (b c : I) : DifferentiableAt ℝ (H a b c) t :=
    ((hWP a b c).contDiffAt ((chart a).open_target.mem_nhds ht)).differentiableAt
      (by simp)
  have hG (b c d : I) : DifferentiableAt ℝ (G a b c d) t :=
    differentiableAt_nativeWeilPeterssonChristoffelExpression_of_localSmoothness
      R hp hg hgenus hΓ hfree hsmooth hWP a b c d t ht
  have hder :
      (∑ n, (Dbar (G a n k m) l t * H a n j t +
        G a n k m t * Dbar (H a n j) l t)) =
      Dbar (fun s => Dz (H a k j) m s) l t := by
    have hfun : (fun s => ∑ n, G a n k m s * H a n j s) =
        (fun s => Dz (H a k j) m s) :=
      funext (nativeWeilPeterssonChristoffelExpression_contract
        R hp hg hgenus hΓ hfree hsmooth a k m j)
    calc
      _ = Dbar (fun s => ∑ n, G a n k m s * H a n j s) l t := by
        rw [coordinateDbar_sum (fun n s => G a n k m s * H a n j s) l t
          (fun n => (hG n k m).mul (hH n j))]
        apply Finset.sum_congr rfl
        intro n _
        exact (coordinateDbar_mul _ _ l t (hG n k m) (hH n j)).symm
      _ = _ := congrArg (fun f : E → ℂ => Dbar f l t) hfun
  have hbar (b c r : I) : conj (Dbar (H a b c) r t) = Dz (H a c b) r t := by
    have hc := congrArg conj (nativeWeilPeterssonCoefficientDz_conj
      R hp hg hgenus hΓ hfree hsmooth a c b r t)
    simpa only [Complex.conj_conj] using hc.symm
  have hsecond : conj (Dbar (fun s => Dz (H a k j) m s) l t) =
      Dz (fun s => Dbar (H a j k) m s) l t := by
    have hfun : (fun s => conj (Dz (H a k j) m s)) =
        (fun s => Dbar (H a j k) m s) :=
      funext (nativeWeilPeterssonCoefficientDz_conj
        R hp hg hgenus hΓ hfree hsmooth a k j m)
    calc
      _ = Dz (fun s => conj (Dz (H a k j) m s)) l t :=
        (coordinateDz_conj (fun s => Dz (H a k j) m s) l t).symm
      _ = _ := congrArg (fun f : E → ℂ => Dz f l t) hfun
  have hc :
      (∑ n, (conj (Dbar (G a n k m) l t) * H a j n t +
        conj (G a n k m t) * Dz (H a j n) l t)) =
      Dz (fun s => Dbar (H a j k) m s) l t := by
    simpa only [map_sum, map_add, map_mul,
      nativeWeilPeterssonLocalCoefficient_conj, hbar, hsecond] using congrArg conj hder
  have hCG (n : I) : conj (G a n k m t) =
      ∑ r, (M a t)⁻¹ n r * Dbar (H a r k) m t := by
    simp only [nativeWeilPeterssonChristoffelExpression, map_sum, map_mul,
      nativeWeilPeterssonRaisedInverseCoefficient_conj, nativeWeilPeterssonCoefficientDz_conj]
    simp only [nativeWeilPeterssonRaisedInverseCoefficient]
  have hcorrection :
      (∑ n, ∑ r, Dz (H a j n) l t * (M a t)⁻¹ n r * Dbar (H a r k) m t) =
      ∑ n, Dz (H a j n) l t * conj (G a n k m t) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [hCG n, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hL : L a j k l m t =
      ∑ n, H a j n t * conj (Dbar (G a n k m) l t) := by
    simp only [nativeWeilPeterssonLoweredCurvatureExpression,
      nativeWeilPeterssonMixedCurvatureExpression, map_neg, mul_neg,
      Finset.sum_neg_distrib, neg_neg]
  apply (eq_sub_iff_add_eq).mpr
  rw [hcorrection, hL]
  calc
    _ = ∑ n, (conj (Dbar (G a n k m) l t) * H a j n t +
        conj (G a n k m t) * Dz (H a j n) l t) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := hc

/-- The same four-direction contraction retains every inverse correction
when expanded in the original mixed parameter derivatives. -/
theorem nativeWeilPeterssonLoweredContraction_eq_corrected_mixed
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (a : TeichmullerSpace.{0,0} R) (t : E) (ht : t ∈ (chart a).target)
    (u v w s : E) :
    C4 a u v w s t = ∑ j, ∑ k, ∑ l, ∑ m,
      (Dz (fun x => Dbar (H a j k) m x) l t -
        ∑ n, ∑ r, Dz (H a j n) l t * (M a t)⁻¹ n r * Dbar (H a r k) m t) *
        u j * conj (v k) * w l * conj (s m) := by
  unfold nativeWeilPeterssonLoweredContraction
  simp_rw [nativeWeilPeterssonLoweredCurvatureExpression_eq_corrected_mixed
    R hp hg hgenus hΓ hfree hsmooth hWP a t ht]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
