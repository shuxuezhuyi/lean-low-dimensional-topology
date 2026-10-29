module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricGramSmooth
public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricGramProportional

/-!
# A global smooth conformal factor from the same literal metric coefficient

The pointwise comparison is defined with an arbitrary nonzero chosen frame.
That frame need not be smooth: uniqueness identifies the ratio locally with
ratios of genuine smooth original-chart Gram entries. Both metric arguments
are arbitrary raw smooth metrics on the unchanged original tangent bundle.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}

/-- The actual pointwise metric ratio on one nonzero tangent vector, without
asserting that the pointwise chosen frame is a smooth global vector field. -/
def rawMetricRatio (g h : SmoothSurfaceMetric R) (x : X) : ℝ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact h.inner x (AtlasInducedMetric.chosenFrame R x) (AtlasInducedMetric.chosenFrame R x) /
    g.inner x (AtlasInducedMetric.chosenFrame R x) (AtlasInducedMetric.chosenFrame R x)

theorem rawMetricRatio_pos (g h : SmoothSurfaceMetric R) (x : X) :
    0 < rawMetricRatio g h x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact div_pos (h.pos x _ (AtlasInducedMetric.chosenFrame_ne_zero R x))
    (g.pos x _ (AtlasInducedMetric.chosenFrame_ne_zero R x))

/-- Same literal coefficients imply one scalar identity on all original
vectors, with a ratio independent of the chosen chart or the chosen frame. -/
theorem rawMetricRatio_inner (g h : SmoothSurfaceMetric R)
    (hμ : ∀ (e : OriginalComplexChart R) (x : X) (hx : x ∈ e.val.source),
      metricBeltramiInOriginalChart g e x hx = metricBeltramiInOriginalChart h e x hx)
    (x : X) (v w : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    h.inner x v w = rawMetricRatio g h x * g.inner x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change h.inner x v w = rawMetricRatio g h x * g.inner x v w
  obtain ⟨e, he, hx⟩ := R.cover x
  obtain ⟨c, hc, hform⟩ := rawMetric_pointwise_proportional_of_beltrami_eq
    g h ⟨e, he⟩ x hx (hμ ⟨e, he⟩ x hx)
  have hratio : rawMetricRatio g h x = c := by
    dsimp only [rawMetricRatio]
    rw [hform]
    exact mul_div_cancel_right₀ _
      (g.pos x _ (AtlasInducedMetric.chosenFrame_ne_zero R x)).ne'
  rw [hratio]
  exact hform v w

/-- The global comparison equals the quotient of the actual E entries in
every valid fixed original chart. -/
theorem rawMetricRatio_eq_gramE (g h : SmoothSurfaceMetric R)
    (hμ : ∀ (e : OriginalComplexChart R) (x : X) (hx : x ∈ e.val.source),
      metricBeltramiInOriginalChart g e x hx = metricBeltramiInOriginalChart h e x hx)
    (e : OriginalComplexChart R) (x : X) (hx : x ∈ e.val.source) :
    rawMetricRatio g h x = metricGramE h e x hx / metricGramE g e x hx := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  have hh := rawMetricRatio_inner g h hμ x (D.symm 1) (D.symm 1)
  change metricGramE h e x hx = rawMetricRatio g h x * metricGramE g e x hx at hh
  exact ((div_eq_iff (metricGram_positive g e x hx).1.ne').mpr hh).symm

/-- The pointwise ratio is globally smooth because its expression in every
fixed original chart is a ratio of smooth actual Gram entries. -/
theorem rawMetricRatio_contMDiff (g h : SmoothSurfaceMetric R)
    (hμ : ∀ (e : OriginalComplexChart R) (x : X) (hx : x ∈ e.val.source),
      metricBeltramiInOriginalChart g e x hx = metricBeltramiInOriginalChart h e x hx) :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (rawMetricRatio g h) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (rawMetricRatio g h)
  intro x
  obtain ⟨e, he, hx⟩ := R.cover x
  let E : OriginalComplexChart R := ⟨e, he⟩
  have hg : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞
      (fun y => metricGramInChart g E y 1 1) e.source :=
    ((metricGramInChart_contMDiffOn g E).clm_apply
      contMDiffOn_const).clm_apply contMDiffOn_const
  have hh : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞
      (fun y => metricGramInChart h E y 1 1) e.source :=
    ((metricGramInChart_contMDiffOn h E).clm_apply
      contMDiffOn_const).clm_apply contMDiffOn_const
  have hne : metricGramInChart g E x 1 1 ≠ 0 := by
    rw [metricGramInChart_eq g E x hx]
    exact (metricGram_positive g E x hx).1.ne'
  have hs := (hh.contMDiffAt (e.open_source.mem_nhds hx)).div₀
    (hg.contMDiffAt (e.open_source.mem_nhds hx)) hne
  apply hs.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  simpa only [Pi.div_apply, metricGramInChart_eq h E y hy,
    metricGramInChart_eq g E y hy, metricGramE] using
    rawMetricRatio_eq_gramE g h hμ E y hy

/-- Positive rescaling leaves the literal Gram coefficient unchanged. This
also holds for arbitrary real triples; no extra positivity premise is hidden. -/
theorem metricBeltramiFromGram_pos_mul (c E F G : ℝ) (hc : 0 < c) :
    metricBeltramiFromGram (c * E) (c * F) (c * G) = metricBeltramiFromGram E F G := by
  have hdet : (c * E) * (c * G) - (c * F) ^ 2 = c ^ 2 * (E * G - F ^ 2) := by ring
  have hs : Real.sqrt ((c * E) * (c * G) - (c * F) ^ 2) =
      c * Real.sqrt (E * G - F ^ 2) := by
    rw [hdet, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  have hnum : ((((c * E - c * G : ℝ) : ℂ) + 2 * Complex.I * ((c * F : ℝ) : ℂ))) =
      (c : ℂ) * (((E - G : ℝ) : ℂ) + 2 * Complex.I * (F : ℂ)) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hden : ((c * E + c * G + 2 * (c * Real.sqrt (E * G - F ^ 2)) : ℝ) : ℂ) =
      (c : ℂ) * ((E + G + 2 * Real.sqrt (E * G - F ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    ring
  rw [metricBeltramiFromGram, hs, hnum, hden]
  exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hc.ne')

/-- Equal literal coefficients are equivalent to a globally C∞ real
exponential factor between the full original bilinear metrics. -/
theorem rawMetric_beltrami_eq_iff_smooth_scale (g h : SmoothSurfaceMetric R) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (∀ (e : OriginalComplexChart R) (x : X) (hx : x ∈ e.val.source),
      metricBeltramiInOriginalChart g e x hx = metricBeltramiInOriginalChart h e x hx) ↔
    ∃ φ : X → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ ∧
      ∀ (x : X) (v w : RealSurfaceTangent R x),
        h.inner x v w = Real.exp (φ x) * g.inner x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  constructor
  · intro hμ
    refine ⟨Real.log ∘ rawMetricRatio g h, ?_, ?_⟩
    · intro x
      exact (Real.contDiffAt_log.mpr (rawMetricRatio_pos g h x).ne').comp_contMDiffAt
        (rawMetricRatio_contMDiff g h hμ x)
    · intro x v w
      change h.inner x v w = Real.exp (Real.log (rawMetricRatio g h x)) * _
      rw [Real.exp_log (rawMetricRatio_pos g h x)]
      exact rawMetricRatio_inner g h hμ x v w
  · rintro ⟨φ, _hφ, hscale⟩ e x hx
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
    have hE : metricGramE h e x hx = Real.exp (φ x) * metricGramE g e x hx :=
      hscale x (D.symm 1) (D.symm 1)
    have hF : metricGramF h e x hx = Real.exp (φ x) * metricGramF g e x hx :=
      hscale x (D.symm 1) (D.symm Complex.I)
    have hG : metricGramG h e x hx = Real.exp (φ x) * metricGramG g e x hx :=
      hscale x (D.symm Complex.I) (D.symm Complex.I)
    rw [metricBeltramiInOriginalChart_eq_gram,
      metricBeltramiInOriginalChart_eq_gram, hE, hF, hG]
    exact (metricBeltramiFromGram_pos_mul _ _ _ _ (Real.exp_pos (φ x))).symm

end LowDimensionalTopology.Geometry.Teichmuller
