module

public import LowDimensionalTopology.Geometry.Teichmuller.MetricBeltramiPullback
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Positive Gram matrices of every original smooth surface metric

The real entries are evaluated on the inverse differential of the actual
original chart. The strict unit-disk estimate applies to every raw smooth
metric, including metrics incompatible with the reference complex structure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u

/-- A positive symmetric real form has a strictly positive real Gram determinant
on the complex coordinate basis `1, I`. -/
theorem complexGram_det_pos (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (hs : ∀ a b, B a b = B b a) (hp : ∀ a : ℂ, a ≠ 0 → 0 < B a a) :
    0 < B 1 1 * B Complex.I Complex.I - (B 1 Complex.I) ^ 2 := by
  have hE : 0 < B 1 1 := hp 1 one_ne_zero
  let v : ℂ := (B 1 1) • Complex.I - (B 1 Complex.I) • (1 : ℂ)
  have hv : v ≠ 0 := by
    intro hz
    have him := congrArg Complex.im hz
    simp only [v, Complex.sub_im, Complex.smul_im, Complex.I_im, Complex.one_im,
      smul_eq_mul, mul_one, mul_zero, sub_zero, Complex.zero_im] at him
    exact hE.ne' him
  have hpos := hp v hv
  have hval : B v v = B 1 1 *
      (B 1 1 * B Complex.I Complex.I - (B 1 Complex.I) ^ 2) := by
    simp only [v, map_sub, map_smul, sub_apply,
      smul_apply, smul_eq_mul, hs Complex.I 1]
    ring
  rw [hval] at hpos
  by_contra hn
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hE.le (le_of_not_gt hn))) hpos

/-- The literal positive-square-root formula of the book lies strictly in the
unit disk for every positive definite real Gram matrix. -/
theorem metricBeltramiFromGram_norm_lt_one {E F G : ℝ}
    (hE : 0 < E) (hG : 0 < G) (hdet : 0 < E * G - F ^ 2) :
    ‖metricBeltramiFromGram E F G‖ < 1 := by
  let d : ℝ := E + G + 2 * Real.sqrt (E * G - F ^ 2)
  let n : ℂ := (((E - G : ℝ) : ℂ) + 2 * Complex.I * (F : ℂ))
  have hs : 0 < Real.sqrt (E * G - F ^ 2) := Real.sqrt_pos.mpr hdet
  have hs2 := Real.sq_sqrt hdet.le
  have hd : 0 < d := add_pos (add_pos hE hG)
    (mul_pos (by norm_num : (0 : ℝ) < 2) hs)
  have hn : ‖n‖ ^ 2 = (E - G) ^ 2 + 4 * F ^ 2 := by
    simp only [n, Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hsq : ‖n‖ ^ 2 < d ^ 2 := by
    rw [hn]
    dsimp only [d]
    nlinarith [mul_pos (add_pos hE hG) hs]
  have hnorm : ‖n‖ < d := by nlinarith [norm_nonneg n]
  change ‖n / (d : ℂ)‖ < 1
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd, div_lt_one hd]
  exact hnorm

/-- The real coordinate form of the actual original metric, using the inverse
of the actual original chart differential. -/
def metricGramForm {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (x : X) (hx : x ∈ e.val.source) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  letI : IsNormableSpace ℝ (RealSurfaceTangent R x) := D.isNormableSpace
  exact (g.inner x).bilinearComp D.symm.toContinuousLinearMap D.symm.toContinuousLinearMap

/-- The literal coefficient of `dx²` in an original complex chart. -/
def metricGramE {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (x : X) (hx : x ∈ e.val.source) : ℝ := metricGramForm g e x hx 1 1

/-- The literal mixed Gram entry; the metric coefficient of `dx dy` is `2F`. -/
def metricGramF {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (x : X) (hx : x ∈ e.val.source) : ℝ := metricGramForm g e x hx 1 Complex.I

/-- The literal coefficient of `dy²` in an original complex chart. -/
def metricGramG {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (x : X) (hx : x ∈ e.val.source) : ℝ := metricGramForm g e x hx Complex.I Complex.I

/-- All original chart Gram matrices of an arbitrary raw metric are positive
definite; no isothermal or original-atlas compatibility assumption is used. -/
theorem metricGram_positive {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (x : X) (hx : x ∈ e.val.source) :
    0 < metricGramE g e x hx ∧ 0 < metricGramG g e x hx ∧
      0 < metricGramE g e x hx * metricGramG g e x hx - (metricGramF g e x hx) ^ 2 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  have hp (a : ℂ) (ha : a ≠ 0) : 0 < metricGramForm g e x hx a a := by
    change 0 < g.inner x (D.symm a) (D.symm a)
    apply g.pos x
    exact D.symm.toLinearEquiv.map_ne_zero_iff.mpr ha
  refine ⟨hp 1 one_ne_zero, hp Complex.I Complex.I_ne_zero, ?_⟩
  exact complexGram_det_pos (metricGramForm g e x hx)
    (fun a b => g.symm x (D.symm a) (D.symm b)) hp

/-- The all-original-chart coefficient in the marking construction is exactly
the literal E,F,G formula for this same raw metric. -/
theorem metricBeltramiInOriginalChart_eq_gram
    {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (x : X) (hx : x ∈ e.val.source) :
    metricBeltramiInOriginalChart g e x hx = metricBeltramiFromGram
      (metricGramE g e x hx) (metricGramF g e x hx) (metricGramG g e x hx) := rfl

/-- The actual raw-metric coefficient has modulus strictly less than one in
EVERY original complex chart. This applies to all smooth metrics, not only to
metrics obtained from a marking. -/
theorem metricBeltramiInOriginalChart_norm_lt_one
    {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (x : X) (hx : x ∈ e.val.source) :
    ‖metricBeltramiInOriginalChart g e x hx‖ < 1 := by
  obtain ⟨hE, hG, hd⟩ := metricGram_positive g e x hx
  rw [metricBeltramiInOriginalChart_eq_gram]
  exact metricBeltramiFromGram_norm_lt_one hE hG hd

end LowDimensionalTopology.Geometry.Teichmuller
