module

public import LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeriesSeed
public import LowDimensionalTopology.Geometry.Teichmuller.GammaLpOperators
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalRegions
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# The actual geodesic endpoint seed in a prescribed real Möbius chart

The full endpoint pair, including infinity, determines the squared logarithmic
derivative of the same normalizing matrix. The final theorem uses the actual
axis and only projective equality with a positive logarithmic dilation.
No equality of special-linear matrices is inferred from their actions.

The actual Möbius derivative API reuses Wu Xiaobin's Li-Zhong-QC
formalization, Apache-2.0, pinned commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped OnePoint UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries

open Hyperbolic
open GammaMeasurableBeltrami

private theorem boundary_finite (Q : Deck) (x : ℂ) :
    (realSLMobius Q).val (x : OnePoint ℂ) =
      if (Q 1 0 : ℂ) * x + Q 1 1 = 0 then ∞
      else (((Q 0 0 : ℂ) * x + Q 0 1) / ((Q 1 0 : ℂ) * x + Q 1 1) : ℂ) := by
  rw [realSLMobius, MonoidHom.comp_apply,
    Mobius.invariantDisc_specialLinear_action, Mobius.fractionalLinear_coe]
  rfl

private theorem boundary_infty (Q : Deck) :
    (realSLMobius Q).val ∞ =
      if (Q 1 0 : ℂ) = 0 then ∞ else ((Q 0 0 : ℂ) / Q 1 0 : ℂ) := by
  rw [realSLMobius, MonoidHom.comp_apply,
    Mobius.invariantDisc_specialLinear_action, Mobius.fractionalLinear_infty]
  rfl

private theorem finite_zero (Q : Deck) (x : ℂ)
    (h : (realSLMobius Q).val (x : OnePoint ℂ) = (0 : ℂ)) :
    (Q 1 0 : ℂ) * x + Q 1 1 ≠ 0 ∧ (Q 0 0 : ℂ) * x + Q 0 1 = 0 := by
  rw [boundary_finite] at h
  by_cases hd : (Q 1 0 : ℂ) * x + Q 1 1 = 0
  · rw [ite_eq_left hd] at h
    exact False.elim (OnePoint.infty_ne_coe (0 : ℂ) h)
  · rw [ite_eq_right hd] at h
    refine ⟨hd, ?_⟩
    have hq := OnePoint.coe_injective h
    simpa only [zero_mul] using (div_eq_iff hd).mp hq

private theorem finite_pole (Q : Deck) (x : ℂ)
    (h : (realSLMobius Q).val (x : OnePoint ℂ) = ∞) :
    (Q 1 0 : ℂ) * x + Q 1 1 = 0 := by
  rw [boundary_finite] at h
  by_contra hd
  rw [ite_eq_right hd] at h
  exact OnePoint.coe_ne_infty _ h

private theorem infty_zero (Q : Deck)
    (h : (realSLMobius Q).val ∞ = (0 : ℂ)) : (Q 0 0 : ℂ) = 0 := by
  rw [boundary_infty] at h
  by_cases hc : (Q 1 0 : ℂ) = 0
  · rw [ite_eq_left hc] at h
    exact False.elim (OnePoint.infty_ne_coe (0 : ℂ) h)
  · rw [ite_eq_right hc] at h
    have hq := OnePoint.coe_injective h
    simpa only [zero_mul] using (div_eq_iff hc).mp hq

private theorem infty_pole (Q : Deck)
    (h : (realSLMobius Q).val ∞ = ∞) : (Q 1 0 : ℂ) = 0 := by
  rw [boundary_infty] at h
  by_contra hc
  rw [ite_eq_right hc] at h
  exact OnePoint.coe_ne_infty _ h

/-- The full actual endpoint pair sent to zero and infinity gives the literal
squared logarithmic derivative, including either endpoint at infinity. -/
theorem endpointSeed_eq_squaredLogDerivative (Q : Deck) (a b : OnePoint ℂ)
    (ha : (realSLMobius Q).val a = (0 : ℂ))
    (hb : (realSLMobius Q).val b = ∞) {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    endpointSeed a b z =
      (deriv (LiZhongQC.h36p_m Q) z / LiZhongQC.h36p_m Q z) ^ 2 := by
  let ca : ℂ := Q 0 0
  let cb : ℂ := Q 0 1
  let cc : ℂ := Q 1 0
  let cd : ℂ := Q 1 1
  have hdet : ca * cd - cb * cc = 1 := by
    have hQ : Q 0 0 * Q 1 1 - Q 0 1 * Q 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using Q.det_coe
    dsimp only [ca, cb, cc, cd]
    exact_mod_cast hQ
  have hden : cc * z + cd ≠ 0 := denominator_ne_zero Q ⟨z, hz⟩
  have hm : LiZhongQC.h36p_m Q z ≠ 0 := by
    intro he
    have him := LiZhongQC.h36p_m_mem Q hz
    change 0 < (LiZhongQC.h36p_m Q z).im at him
    rw [he, Complex.zero_im] at him
    exact (lt_irrefl (0 : ℝ)) him
  have hnum : ca * z + cb ≠ 0 := by
    intro he
    apply hm
    change (ca * z + cb) / (cc * z + cd) = 0
    rw [he, zero_div]
  have hlog : deriv (LiZhongQC.h36p_m Q) z / LiZhongQC.h36p_m Q z =
      1 / ((cc * z + cd) * (ca * z + cb)) := by
    rw [(LiZhongQC.h36p_m_hasDerivAt Q hz).deriv]
    change 1 / (cc * z + cd) ^ 2 / ((ca * z + cb) / (cc * z + cd)) = _
    field_simp [hden, hnum]
  rw [hlog]
  cases a using OnePoint.rec with
  | infty =>
    cases b using OnePoint.rec with
    | infty =>
      exact False.elim (OnePoint.infty_ne_coe (0 : ℂ) (hb.symm.trans ha))
    | coe y =>
      have hca : ca = 0 := infty_zero Q ha
      have hy : cc * y + cd = 0 := finite_pole Q y hb
      have hbc : cb * cc = -1 := by
        have hneg : -(cb * cc) = 1 := by
          simpa only [hca, zero_mul, zero_sub] using hdet
        linear_combination -hneg
      have hN : ca * z + cb = cb := by rw [hca, zero_mul, zero_add]
      have hD : cc * z + cd = cc * (z - y) := by linear_combination hy
      have hzy : z - y ≠ 0 := by
        intro he
        apply hden
        rw [sub_eq_zero.mp he]
        exact hy
      have hcross : (-1 : ℂ) * ((cc * z + cd) * (ca * z + cb)) = z - y := by
        calc
          _ = -(cb * cc) * (z - y) := by rw [hN, hD]; ring
          _ = z - y := by rw [hbc]; ring
      have hrecip : 1 / ((cc * z + cd) * (ca * z + cb)) = -1 / (z - y) := by
        apply (div_eq_div_iff (mul_ne_zero hden hnum) hzy).mpr
        simpa only [one_mul] using hcross.symm
      rw [hrecip]
      simp only [endpointSeed, div_pow, neg_one_sq]
  | coe x =>
    have hx : ca * x + cb = 0 := (finite_zero Q x ha).2
    have hN : ca * z + cb = ca * (z - x) := by linear_combination hx
    have hzx : z - x ≠ 0 := by
      intro he
      apply hnum
      rw [sub_eq_zero.mp he]
      exact hx
    cases b using OnePoint.rec with
    | infty =>
      have hcc : cc = 0 := infty_pole Q hb
      have had : ca * cd = 1 := by
        simpa only [hcc, mul_zero, sub_zero] using hdet
      have hD : cc * z + cd = cd := by rw [hcc, zero_mul, zero_add]
      have hcross : (1 : ℂ) * ((cc * z + cd) * (ca * z + cb)) = z - x := by
        calc
          _ = (ca * cd) * (z - x) := by rw [hN, hD]; ring
          _ = z - x := by rw [had, one_mul]
      have hrecip : 1 / ((cc * z + cd) * (ca * z + cb)) = 1 / (z - x) := by
        apply (div_eq_div_iff (mul_ne_zero hden hnum) hzx).mpr
        simpa only [one_mul] using hcross.symm
      rw [hrecip]
      simp only [endpointSeed, div_pow, one_pow]
    | coe y =>
      have hy : cc * y + cd = 0 := finite_pole Q y hb
      have hD : cc * z + cd = cc * (z - y) := by linear_combination hy
      have hzy : z - y ≠ 0 := by
        intro he
        apply hden
        rw [sub_eq_zero.mp he]
        exact hy
      have hac : ca * cc * (x - y) = 1 := by
        linear_combination hdet + cc * hx - ca * hy
      have hcross : (x - y) * ((cc * z + cd) * (ca * z + cb)) =
          (z - x) * (z - y) := by
        calc
          _ = (ca * cc * (x - y)) * ((z - x) * (z - y)) := by rw [hN, hD]; ring
          _ = (z - x) * (z - y) := by rw [hac, one_mul]
      have hrecip : 1 / ((cc * z + cd) * (ca * z + cb)) =
          (x - y) / ((z - x) * (z - y)) := by
        apply (div_eq_div_iff (mul_ne_zero hden hnum) (mul_ne_zero hzx hzy)).mpr
        simpa only [one_mul] using hcross.symm
      rw [hrecip]
      simp only [endpointSeed, div_pow, mul_pow]

/-- The seed of the same actual hyperbolic axis has the squared logarithmic
derivative of every prescribed positive logarithmic normalizer. -/
theorem hyperbolicSeed_eq_squaredLogDerivative (A : Deck)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    (Q : Deck) (s : ℝ) (hs : 0 < s)
    (hQA : realSLMobius (Q * A * Q⁻¹) = realSLMobius (Fuchsian.hLogDilationSL s))
    {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    seed (hHyperbolicAxis A hA ht) z =
      (deriv (LiZhongQC.h36p_m Q) z / LiZhongQC.h36p_m Q z) ^ 2 := by
  have hscale_ne_one : (Real.exp (2 * s) : ℂ) ≠ 1 := by
    exact_mod_cast (ne_of_gt (Real.one_lt_exp_iff.mpr (mul_pos zero_lt_two hs)))
  have hn : realSLMobius (Q * A * Q⁻¹) =
      Mobius.mobiusScaling (Units.mk0 (Real.exp (2 * s) : ℂ)
        (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))) :=
    hQA.trans ((Fuchsian.realSLMobius_logDilation s).trans
      (Fuchsian.realSLMobius_verticalDilation (Real.exp (2 * s)) (Real.exp_pos _)))
  let a : OnePoint ℂ := (realSLMobius Q).val.symm (0 : ℂ)
  let b : OnePoint ℂ := (realSLMobius Q).val.symm ∞
  have ha : (realSLMobius Q).val a = (0 : ℂ) := (realSLMobius Q).val.apply_symm_apply _
  have hb : (realSLMobius Q).val b = ∞ := (realSLMobius Q).val.apply_symm_apply _
  have hfix (w : OnePoint ℂ) : (realSLMobius A).val w = w ↔
      (realSLMobius Q).val w = (0 : ℂ) ∨ (realSLMobius Q).val w = ∞ := by
    rw [← realSLMobius_conjugate_fixed_iff A Q w, hn,
      DiscreteGroups.mobiusScaling_eq_standard _ hscale_ne_one,
      Mobius.mobiusStandardElement_boundary_fixed_iff _ hscale_ne_one]
  have hends : (hHyperbolicAxis A hA ht).idealEndpoints = {a, b} := by
    rw [hHyperbolicAxis_idealEndpoints]
    ext w
    change (realSLMobius A).val w = w ↔ w = a ∨ w = b
    rw [hfix]
    constructor
    · rintro (hw | hw)
      · exact Or.inl ((realSLMobius Q).val.injective (hw.trans ha.symm))
      · exact Or.inr ((realSLMobius Q).val.injective (hw.trans hb.symm))
    · rintro (rfl | rfl)
      · exact Or.inl ha
      · exact Or.inr hb
  rw [seed_eq_endpointSeed hends]
  exact endpointSeed_eq_squaredLogDerivative Q a b ha hb hz

end LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries
