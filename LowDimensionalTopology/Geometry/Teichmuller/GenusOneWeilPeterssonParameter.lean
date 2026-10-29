module

public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.NormalizedTorusFlatArea
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.PoincareLineElement
public import LowDimensionalTopology.External.LiZhongQC.Ch01.S06_C1Quasiconformal
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FieldSimp

/-!
# The WP integral in the actual normalized torus family

The deformation respects the original period basis and the pairing is integrated
over the existing actual torus with its normalized fundamental-domain measure.
The real tensor is defined on the upper-half-plane parameter directions
using the source normalization and the same literal torus integral.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane ComplexConjugate InnerProductSpace Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces Hyperbolic

def periodGap (τ : ℍ) : ℂ := (τ : ℂ) - conj (τ : ℂ)

theorem periodGap_ne_zero (τ : ℍ) : periodGap τ ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [periodGap, Complex.sub_im, Complex.conj_im, UpperHalfPlane.coe_im,
    Complex.zero_im] at hi
  linarith [τ.im_pos]

theorem periodGap_eq (τ : ℍ) : periodGap τ = 2 * Complex.I * (τ.im : ℂ) := by
  apply Complex.ext <;> simp [periodGap, Complex.mul_re, Complex.mul_im, two_mul]
  ring

/-- The original real-affine lift sending the marked periods to 1 and tau+t. -/
def affineLift (τ : ℍ) (t z : ℂ) : ℂ :=
  (1 + t / periodGap τ) * z + (-t / periodGap τ) * conj z

/-- The literal deck-period law, for every original integer period and every point. -/
theorem affineLift_period (τ : ℍ) (t z : ℂ) (m n : ℤ) :
    affineLift τ t (z + (m : ℂ) + (n : ℂ) * (τ : ℂ)) =
      affineLift τ t z + (m : ℂ) + (n : ℂ) * ((τ : ℂ) + t) := by
  unfold affineLift
  simp only [map_add, map_mul, map_intCast]
  field_simp [periodGap_ne_zero τ]
  unfold periodGap
  ring

/-- The Beltrami ratio of the two constant spatial coefficients in affineLift. -/
def affineBeltrami (τ : ℍ) (t : ℂ) : ℂ :=
  (-t / periodGap τ) / (1 + t / periodGap τ)

theorem affineBeltrami_eq (τ : ℍ) (t : ℂ) :
    affineBeltrami τ t = -t / (periodGap τ + t) := by
  have hd := periodGap_ne_zero τ
  have ha : 1 + t / periodGap τ = (periodGap τ + t) / periodGap τ := by
    field_simp [hd]
  unfold affineBeltrami
  rw [ha]
  by_cases h : periodGap τ + t = 0
  · simp [h]
  · field_simp [hd, h]

/-- On its explicit orientation-preserving range, this is the actual QC dilatation. -/
theorem affineLift_quasiconformal (τ : ℍ) (t : ℂ)
    (h : ‖-t / periodGap τ‖ < ‖1 + t / periodGap τ‖) :
    LiZhongQC.IsC1Quasiconformal (affineLift τ t) univ
        ((‖1 + t / periodGap τ‖ + ‖-t / periodGap τ‖) /
          (‖1 + t / periodGap τ‖ - ‖-t / periodGap τ‖)) ∧
      ∀ z, LiZhongQC.complexDilatation (affineLift τ t) z = affineBeltrami τ t := by
  obtain ⟨hqc, hμ⟩ := LiZhongQC.affine_isC1Quasiconformal
    (A := 1 + t / periodGap τ) (B := -t / periodGap τ) (C := 0) h
  have hF : (fun z : ℂ =>
      (1 + t / periodGap τ) * z + (-t / periodGap τ) * conj z + 0) = affineLift τ t := by
    funext z
    simp only [affineLift, add_zero]
  rw [hF] at hqc hμ
  exact ⟨hqc, fun z => (hμ z).1⟩

/-- The source's constant infinitesimal Beltrami coefficient. -/
def tangentBeltrami (τ : ℍ) : ℂ := -1 / periodGap τ

theorem hasDerivAt_affineBeltrami_zero (τ : ℍ) :
    HasDerivAt (affineBeltrami τ) (tangentBeltrami τ) 0 := by
  have hfun : affineBeltrami τ = fun t => -t / (periodGap τ + t) :=
    funext (affineBeltrami_eq τ)
  rw [hfun]
  have h := ((hasDerivAt_id (0 : ℂ)).neg).div
    ((hasDerivAt_const (0 : ℂ) (periodGap τ)).add (hasDerivAt_id (0 : ℂ)))
    (by simpa using periodGap_ne_zero τ)
  convert h using 1
  · rfl
  · unfold tangentBeltrami
    change -1 / periodGap τ =
      (-1 * (periodGap τ + 0) - (-0) * (0 + 1)) / (periodGap τ + 0) ^ 2
    field_simp [periodGap_ne_zero τ]
    ring

theorem tangentBeltrami_eq (τ : ℍ) :
    tangentBeltrami τ = Complex.I / (2 * (τ.im : ℂ)) := by
  rw [tangentBeltrami, periodGap_eq]
  simp only [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  ring

theorem tangentBeltrami_mul_conj (τ : ℍ) :
    tangentBeltrami τ * conj (tangentBeltrami τ) =
      ((1 / (4 * τ.im ^ 2) : ℝ) : ℂ) := by
  rw [tangentBeltrami_eq]
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_one]
  rw [div_mul_div_comm]
  simp only [mul_neg, Complex.I_mul_I, neg_neg]
  congr 1
  ring

/-- The original first-linear constant-Beltrami integral on the actual torus. -/
def pairing (τ : ℍ) (u v : ℂ) : ℂ :=
  ∫ _ : ComplexTorusCarrier, (u * tangentBeltrami τ) * conj (v * tangentBeltrami τ)
    ∂normalizedTorusUnitAreaMeasure τ

/-- The Hermitian coefficient is derived from unit area and the actual affine variation. -/
theorem pairing_eq (τ : ℍ) (u v : ℂ) :
    pairing τ u v = ((1 / (4 * τ.im ^ 2) : ℝ) : ℂ) * u * conj v := by
  rw [pairing, integral_const, measureReal_def, normalizedTorusUnitAreaMeasure_univ,
    ENNReal.toReal_one, one_smul]
  rw [map_mul]
  calc
    _ = (tangentBeltrami τ * conj (tangentBeltrami τ)) * u * conj v := by ring
    _ = _ := by rw [tangentBeltrami_mul_conj]

theorem pairing_one (τ : ℍ) : pairing τ 1 1 = ((1 / (4 * τ.im ^ 2) : ℝ) : ℂ) := by
  simp only [pairing_eq, map_one, mul_one]

/-- The English-normalized parameter tensor, compared with the existing Poincare tensor. -/
def parameterTensor (τ : ℍ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • halfPlanePoincareTensor τ

/-- The tensor is exactly twice the real part of the actual normalized-torus integral. -/
theorem parameterTensor_apply (τ : ℍ) (u v : ℂ) :
    parameterTensor τ u v = 2 * (pairing τ u v).re := by
  have hi : inner ℝ u v = u.re * v.re + u.im * v.im := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
    change (conj u * v).re = _
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  change (1 / 2 : ℝ) * halfPlanePoincareTensor τ u v = _
  rw [halfPlanePoincareTensor_apply, hi, pairing_eq]
  simp only [hyperbolicDensity, one_div, mul_inv_rev, inv_pow,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- This is half of the existing curvature-minus-one Poincare line element. -/
theorem parameterTensor_self (τ : ℍ) (v : ℂ) :
    parameterTensor τ v v = ‖v‖ ^ 2 / (2 * τ.im ^ 2) := by
  change (1 / 2 : ℝ) * halfPlanePoincareTensor τ v v = _
  rw [halfPlanePoincareTensor_self]
  field_simp [τ.im_ne_zero]

theorem parameterTensor_pos (τ : ℍ) {v : ℂ} (hv : v ≠ 0) :
    0 < parameterTensor τ v v :=
  mul_pos (by norm_num) (halfPlanePoincareTensor_pos τ hv)

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
