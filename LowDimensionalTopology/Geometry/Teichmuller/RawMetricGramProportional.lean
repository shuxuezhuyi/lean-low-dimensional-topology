module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricGram
public import Mathlib.Tactic.FieldSimp

/-!
# Equal literal metric Beltrami coefficients determine a positive ray

The normalized real Gram entries are recovered from the same literal complex
coefficient. Equality of coefficients consequently forces two arbitrary raw
metrics to differ by a positive scalar at each point, on all tangent vectors.
No isothermal chart or metric realization hypothesis is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u

/-- Recover the three normalized Gram entries from the literal coefficient.
This is the uniqueness assertion behind the metric expression. -/
theorem metricBeltramiFromGram_normalized_entries {E F G : ℝ}
    (hE : 0 < E) (hG : 0 < G) (hdet : 0 < E * G - F ^ 2) :
    let d := E + G + 2 * Real.sqrt (E * G - F ^ 2)
    let μ := metricBeltramiFromGram E F G
    E / d = (1 + ‖μ‖ ^ 2 + 2 * μ.re) / 4 ∧
      F / d = μ.im / 2 ∧ G / d = (1 + ‖μ‖ ^ 2 - 2 * μ.re) / 4 := by
  let d := E + G + 2 * Real.sqrt (E * G - F ^ 2)
  let μ := metricBeltramiFromGram E F G
  have hd : 0 < d := add_pos (add_pos hE hG)
    (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sqrt_pos.mpr hdet))
  have hre : μ.re = (E - G) / d := by
    change ((((E - G : ℝ) : ℂ) + 2 * Complex.I * (F : ℂ)) / (d : ℂ)).re = (E - G) / d
    rw [Complex.div_ofReal_re]
    simp
  have him : μ.im = (2 * F) / d := by
    change ((((E - G : ℝ) : ℂ) + 2 * Complex.I * (F : ℂ)) / (d : ℂ)).im = (2 * F) / d
    rw [Complex.div_ofReal_im]
    simp
  have hn : ‖μ‖ ^ 2 = ((E - G) / d) ^ 2 + ((2 * F) / d) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hs := Real.sq_sqrt hdet.le
  change E / d = (1 + ‖μ‖ ^ 2 + 2 * μ.re) / 4 ∧
    F / d = μ.im / 2 ∧ G / d = (1 + ‖μ‖ ^ 2 - 2 * μ.re) / 4
  refine ⟨?_, ?_, ?_⟩ <;> simp only [hn, hre, him] <;>
    field_simp [hd.ne'] <;> dsimp only [d] <;> nlinarith [hs]

/-- Two positive symmetric real forms on complex coordinates with the same
literal coefficient are positive scalar multiples on every pair of vectors. -/
theorem complexGram_proportional_of_metricBeltrami_eq
    (B C : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (hBs : ∀ a b, B a b = B b a) (hCs : ∀ a b, C a b = C b a)
    (hBp : ∀ a : ℂ, a ≠ 0 → 0 < B a a)
    (hCp : ∀ a : ℂ, a ≠ 0 → 0 < C a a)
    (hμ : metricBeltramiFromGram (B 1 1) (B 1 Complex.I) (B Complex.I Complex.I) =
      metricBeltramiFromGram (C 1 1) (C 1 Complex.I) (C Complex.I Complex.I)) :
    ∃ c : ℝ, 0 < c ∧ ∀ a b : ℂ, C a b = c * B a b := by
  have hBE := hBp 1 one_ne_zero
  have hBG := hBp Complex.I Complex.I_ne_zero
  have hCE := hCp 1 one_ne_zero
  have hCG := hCp Complex.I Complex.I_ne_zero
  let dB := B 1 1 + B Complex.I Complex.I +
    2 * Real.sqrt (B 1 1 * B Complex.I Complex.I - (B 1 Complex.I) ^ 2)
  let dC := C 1 1 + C Complex.I Complex.I +
    2 * Real.sqrt (C 1 1 * C Complex.I Complex.I - (C 1 Complex.I) ^ 2)
  have hdB : 0 < dB := add_pos (add_pos hBE hBG)
    (mul_pos (by norm_num : (0 : ℝ) < 2)
      (Real.sqrt_pos.mpr (complexGram_det_pos B hBs hBp)))
  have hdC : 0 < dC := add_pos (add_pos hCE hCG)
    (mul_pos (by norm_num : (0 : ℝ) < 2)
      (Real.sqrt_pos.mpr (complexGram_det_pos C hCs hCp)))
  obtain ⟨hBe, hBf, hBg⟩ := metricBeltramiFromGram_normalized_entries hBE hBG
    (complexGram_det_pos B hBs hBp)
  obtain ⟨hCe, hCf, hCg⟩ := metricBeltramiFromGram_normalized_entries hCE hCG
    (complexGram_det_pos C hCs hCp)
  have hE : C 1 1 / dC = B 1 1 / dB := by rw [hCe, hBe, hμ]
  have hF : C 1 Complex.I / dC = B 1 Complex.I / dB := by rw [hCf, hBf, hμ]
  have hG : C Complex.I Complex.I / dC = B Complex.I Complex.I / dB := by
    rw [hCg, hBg, hμ]
  have unnormalize {x y : ℝ} (h : x / dC = y / dB) : x = dC / dB * y := by
    calc
      x = (x / dC) * dC := (div_mul_cancel₀ x hdC.ne').symm
      _ = (y / dB) * dC := congrArg (fun t : ℝ => t * dC) h
      _ = dC / dB * y := by ring
  have he := unnormalize hE
  have hf := unnormalize hF
  have hg := unnormalize hG
  refine ⟨dC / dB, div_pos hdC hdB, ?_⟩
  intro a b
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im a).symm
  have hb : b = b.re • (1 : ℂ) + b.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im b).symm
  rw [ha, hb]
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul, hBs Complex.I 1, hCs Complex.I 1,
    he, hf, hg]
  ring

/-- Equality of the literal coefficient in one valid original chart forces
pointwise proportionality of the SAME two raw metrics on the whole original
real tangent space. -/
theorem rawMetric_pointwise_proportional_of_beltrami_eq
    {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}
    (g h : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (x : X) (hx : x ∈ e.val.source)
    (hμ : metricBeltramiInOriginalChart g e x hx =
      metricBeltramiInOriginalChart h e x hx) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∃ c : ℝ, 0 < c ∧ ∀ v w : RealSurfaceTangent R x,
      h.inner x v w = c * g.inner x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  have gp (a : ℂ) (ha : a ≠ 0) : 0 < metricGramForm g e x hx a a := by
    change 0 < g.inner x (D.symm a) (D.symm a)
    exact g.pos x _ (D.symm.toLinearEquiv.map_ne_zero_iff.mpr ha)
  have hp (a : ℂ) (ha : a ≠ 0) : 0 < metricGramForm h e x hx a a := by
    change 0 < h.inner x (D.symm a) (D.symm a)
    exact h.pos x _ (D.symm.toLinearEquiv.map_ne_zero_iff.mpr ha)
  rw [metricBeltramiInOriginalChart_eq_gram,
    metricBeltramiInOriginalChart_eq_gram] at hμ
  obtain ⟨c, hc, hform⟩ := complexGram_proportional_of_metricBeltrami_eq
    (metricGramForm g e x hx) (metricGramForm h e x hx)
    (fun a b => g.symm x (D.symm a) (D.symm b))
    (fun a b => h.symm x (D.symm a) (D.symm b)) gp hp hμ
  refine ⟨c, hc, ?_⟩
  intro v w
  have hvw := hform (D v) (D w)
  change h.inner x (D.symm (D v)) (D.symm (D w)) =
    c * g.inner x (D.symm (D v)) (D.symm (D w)) at hvw
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hvw

end LowDimensionalTopology.Geometry.Teichmuller
