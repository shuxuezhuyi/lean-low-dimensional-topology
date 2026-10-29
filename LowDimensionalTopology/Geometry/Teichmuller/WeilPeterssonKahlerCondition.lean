module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonChristoffelTorsion
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Closedness and coefficient symmetry for the actual WP form

The coordinate form, coefficients and open chart target are the existing
native ones. The equivalence uses only their named smoothness input and
finite real coordinate calculations.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3*g-3)
local notation "E" => I → ℂ
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "H" => nativeWeilPeterssonLocalCoefficient
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "Dz" => nativeWeilPeterssonCoordinateDz (g := g)

/-- On the genuine native chart target, the actual fundamental form is
closed exactly when its holomorphic coefficient slots are symmetric. -/
theorem nativeWeilPeterssonCoordinateForm_closed_iff_coefficientDz_symm
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (t : E) (ht : t ∈ (chart (basePoint R)).target) :
    extDerivWithin Ω (chart (basePoint R)).target t = 0 ↔
      ∀ j k l : I, Dz (H j k) l t = Dz (H l k) j t := by
  constructor
  · intro hc j k l
    exact nativeWeilPeterssonCoefficientDz_symm_of_closed
      R hp hg hgenus hΓ hfree hsmooth hWP t ht hc j l k
  · intro hsym
    have hd : DifferentiableAt ℝ Ω t :=
      ((contDiffOn_nativeWeilPeterssonFundamentalRealCoordinateForm_of_localSmoothness
        R hp hg hgenus hΓ hfree hsmooth hWP (basePoint R)).contDiffAt
          ((chart (basePoint R)).open_target.mem_nhds ht)).differentiableAt (by simp)
    have hh (j k : I) : DifferentiableAt ℝ (H j k) t :=
      ((hWP (basePoint R) j k).contDiffAt
        ((chart (basePoint R)).open_target.mem_nhds ht)).differentiableAt (by simp)
    let D := fderiv ℝ Ω t
    let A (j k l : I) := fderiv ℝ (H j k) t (Pi.single l 1)
    let B (j k l : I) := fderiv ℝ (H j k) t (Pi.single l Complex.I)
    have hform (j k : I) (c d : ℂ) (x : E) :
        Ω x ![Pi.single j c, Pi.single k d] =
          2 * (Complex.I * c * conj d * H j k x).re := by
      rw [nativeWeilPeterssonCoordinateForm_eq_finiteRealPairing]
      classical
      apply congrArg (fun z : ℂ => 2 * z.re)
      rw [Finset.sum_eq_single j]
      · rw [Finset.sum_eq_single k]
        · simp
        · intro s _ hs
          simp [hs]
        · simp
      · intro r _ hr
        simp [Pi.smul_apply, Pi.single_apply, hr]
      · simp
    have hderiv (j k : I) (c d : ℂ) (v : E) :
        D v ![Pi.single j c, Pi.single k d] =
          2 * (Complex.I * c * conj d * fderiv ℝ (H j k) t v).re := by
      have he := hd.hasFDerivAt.continuousAlternatingMap_apply_const
        ![Pi.single j c, Pi.single k d]
      have hf := (Complex.reCLM.hasFDerivAt.comp t
        ((hh j k).hasFDerivAt.const_mul (Complex.I * c * conj d))).const_mul 2
      have hf' := hf.congr_of_eventuallyEq
        (Eventually.of_forall (hform j k c d))
      have h := congrArg (fun L : E →L[ℝ] ℝ => L v) (he.unique hf')
      simpa only [D, ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
        ContinuousLinearMap.flipAlternating_apply_apply, smul_apply, smul_eq_mul] using h
    have hconj (j k : I) (v : E) :
        fderiv ℝ (H k j) t v = conj (fderiv ℝ (H j k) t v) := by
      have hfun : H k j = fun x => conj (H j k x) :=
        funext fun x => (nativeWeilPeterssonLocalCoefficient_conj
          R hp hg hgenus hΓ hfree hsmooth (basePoint R) j k x).symm
      rw [hfun]
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using
        congrArg (fun L : E →L[ℝ] ℂ => L v)
          (Complex.conjCLE.comp_fderiv (f := H j k) (x := t))
    have hsR (j k l : I) :
        (A j k l).re + (B j k l).im = (A l k j).re + (B l k j).im := by
      have h := congrArg Complex.re (hsym j k l)
      dsimp only [A, B]
      norm_num [nativeWeilPeterssonCoordinateDz, Complex.mul_re,
        Complex.mul_im, Complex.div_re, Complex.div_im] at h
      linarith
    have hsI (j k l : I) :
        (A j k l).im - (B j k l).re = (A l k j).im - (B l k j).re := by
      have h := congrArg Complex.im (hsym j k l)
      dsimp only [A, B]
      norm_num [nativeWeilPeterssonCoordinateDz, Complex.mul_re,
        Complex.mul_im, Complex.div_re, Complex.div_im] at h
      linarith
    have hAR (j k l : I) : (A k j l).re = (A j k l).re := by
      simpa only [A, Complex.conj_re] using
        congrArg Complex.re (hconj j k (Pi.single l 1))
    have hAI (j k l : I) : (A k j l).im = -(A j k l).im := by
      simpa only [A, Complex.conj_im] using
        congrArg Complex.im (hconj j k (Pi.single l 1))
    have hBR (j k l : I) : (B k j l).re = (B j k l).re := by
      simpa only [B, Complex.conj_re] using
        congrArg Complex.re (hconj j k (Pi.single l Complex.I))
    have hBI (j k l : I) : (B k j l).im = -(B j k l).im := by
      simpa only [B, Complex.conj_im] using
        congrArg Complex.im (hconj j k (Pi.single l Complex.I))
    have hcyclic (u v w : E) :
        extDeriv Ω t ![u,v,w] = D u ![v,w] - D v ![u,w] + D w ![u,v] := by
      have h0 : (0 : Fin 3).removeNth ![u,v,w] = ![v,w] := by
        ext i
        fin_cases i <;> rfl
      have h1 : (1 : Fin 3).removeNth ![u,v,w] = ![u,w] := by
        ext i
        fin_cases i <;> rfl
      have h2 : (2 : Fin 3).removeNth ![u,v,w] = ![u,v] := by
        ext i
        fin_cases i <;> rfl
      rw [extDeriv_apply hd]
      simp [Fin.sum_univ_three, h0, h1, h2, D,
        fderiv_continuousAlternatingMap_apply_const_apply hd, sub_eq_add_neg]
    have hext : extDeriv Ω t = 0 := by
      let b : Module.Basis (Σ _ : I, Fin 2) ℝ E := Pi.basis fun _ => Complex.basisOneI
      apply ContinuousAlternatingMap.toAlternatingMap_injective
      apply b.ext_alternating
      intro v _hv
      let a : I := (v 0).1
      let b' : I := (v 1).1
      let c : I := (v 2).1
      let α : Fin 2 := (v 0).2
      let β : Fin 2 := (v 1).2
      let γ : Fin 2 := (v 2).2
      have hvec : (fun i => b (v i)) =
          ![Pi.single a (Complex.basisOneI α), Pi.single b' (Complex.basisOneI β),
            Pi.single c (Complex.basisOneI γ)] := by
        funext i
        simp only [b, Pi.basis_apply]
        fin_cases i <;> rfl
      change extDeriv Ω t (fun i => b (v i)) = 0
      rw [hvec, hcyclic, hderiv, hderiv, hderiv]
      have h1R := hsR a b' c
      have h1I := hsI a b' c
      have h2R := hsR a c b'
      have h2I := hsI a c b'
      have h3R := hsR b' a c
      have h3I := hsI b' a c
      have h4R := hsR b' c a
      have h4I := hsI b' c a
      have h5R := hsR c a b'
      have h5I := hsI c a b'
      have h6R := hsR c b' a
      have h6I := hsI c b' a
      have haR := hAR a b' c
      have haI := hAI a b' c
      have hbR := hAR a c b'
      have hbI := hAI a c b'
      have hcR := hAR b' c a
      have hcI := hAI b' c a
      have kaR := hBR a b' c
      have kaI := hBI a b' c
      have kbR := hBR a c b'
      have kbI := hBI a c b'
      have kcR := hBR b' c a
      have kcI := hBI b' c a
      dsimp only [A, B] at h1R h1I h2R h2I h3R h3I h4R h4I h5R h5I h6R h6I
      dsimp only [A, B] at haR haI hbR hbI hcR hcI kaR kaI kbR kbI kcR kcI
      generalize α = iα
      generalize β = iβ
      generalize γ = iγ
      fin_cases iα <;> fin_cases iβ <;> fin_cases iγ <;>
        norm_num only [Complex.coe_basisOneI, Matrix.cons_val_zero', Matrix.cons_val_succ',
          map_one, Complex.conj_I, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
          Complex.neg_re, Complex.neg_im, zero_mul, mul_zero, one_mul, mul_one,
          zero_add, add_zero, sub_zero, zero_sub, neg_neg] <;>
        linarith only [h1R, h1I, h2R, h2I, h3R, h3I, h4R, h4I, h5R, h5I, h6R, h6I,
          haR, haI, hbR, hbI, hcR, hcI, kaR, kaI, kbR, kbI, kcR, kcI]
    simpa only [extDerivWithin,
      fderivWithin_of_isOpen (chart (basePoint R)).open_target ht, extDeriv] using hext

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
