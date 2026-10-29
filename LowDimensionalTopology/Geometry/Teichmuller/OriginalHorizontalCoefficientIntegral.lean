module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHorizontalQuadraticTensors
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalTensorL2Integrability
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic.Linarith

/-!
# The actual horizontal coefficient integral for the same original metric area

Real and imaginary parts of the literal quadratic coefficient pairing are
actual native contractions. This proves continuity and integrability without
assuming that the chart selected at a varying point depends continuously on it.
The integral retains the book normalization and the metric's own area measure.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces AtlasMetricConstruction
universe u

/-- The canonical real action on the unchanged original symmetric-tensor submodule. -/
local instance canonicalHorizontalCoefficientTensorSMul
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) :
    SMul ℝ (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact Submodule.smul (symmetricTwoTensorSubmodule R)

private theorem horizontal_coefficient_contraction_parts
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (G : AtlasInducedMetric R.toRiemannSurface)
    (Q P : HolomorphicQuadraticDifferential R.toRiemannAtlas) (x : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    let e := chosenChart R.toRiemannSurface x
    let a := Q.val x (e.val x) * conj (P.val x (e.val x))
    let lambda := G.density e x
    metricTensorPointwisePairing R G.metric
        ((2 : ℝ) • quadraticDifferentialTensor R Q)
        ((2 : ℝ) • quadraticDifferentialTensor R P) x =
      8 * (a / ((lambda ^ 2 : ℝ) : ℂ)).re ∧
    metricTensorPointwisePairing R G.metric
        ((2 : ℝ) • quadraticDifferentialTensor R Q)
        ((2 : ℝ) • quadraticDifferentialTensor R (Complex.I • P)) x =
      8 * (a / ((lambda ^ 2 : ℝ) : ℂ)).im := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let e := chosenChart R.toRiemannSurface x
  let a := Q.val x (e.val x) * conj (P.val x (e.val x))
  let lambda := G.density e x
  have hx : x ∈ e.val.source := mem_chart_source ℂ x
  have hden : lambda ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (G.density_pos e x hx))
  have hn := metricTensorPointwisePairing_horizontal_normalization R G Q P x x hx
  have hni := metricTensorPointwisePairing_horizontal_normalization
    R G Q (Complex.I • P) x x hx
  have hphase (q p : ℂ) : (q * conj (Complex.I * p)).re = (q * conj p).im := by
    rw [map_mul, Complex.conj_I]
    have hm : q * (-Complex.I * conj p) = -Complex.I * (q * conj p) := by ring
    rw [hm, Complex.mul_re]
    simp
  change lambda ^ 2 * ((1 / 4 : ℝ) * metricTensorPointwisePairing R G.metric
    ((2 : ℝ) • quadraticDifferentialTensor R Q)
    ((2 : ℝ) • quadraticDifferentialTensor R P) x) = 2 * a.re at hn
  change lambda ^ 2 * ((1 / 4 : ℝ) * metricTensorPointwisePairing R G.metric
    ((2 : ℝ) • quadraticDifferentialTensor R Q)
    ((2 : ℝ) • quadraticDifferentialTensor R (Complex.I • P)) x) =
      2 * (Q.val x (e.val x) * conj (Complex.I * P.val x (e.val x))).re at hni
  rw [hphase] at hni
  change lambda ^ 2 * ((1 / 4 : ℝ) * metricTensorPointwisePairing R G.metric
    ((2 : ℝ) • quadraticDifferentialTensor R Q)
    ((2 : ℝ) • quadraticDifferentialTensor R (Complex.I • P)) x) = 2 * a.im at hni
  change _ = 8 * (a / ((lambda ^ 2 : ℝ) : ℂ)).re ∧
    _ = 8 * (a / ((lambda ^ 2 : ℝ) : ℂ)).im
  constructor
  · rw [Complex.div_ofReal_re, ← mul_div_assoc]
    apply (eq_div_iff hden).2
    nlinarith [hn]
  · rw [Complex.div_ofReal_im, ← mul_div_assoc]
    apply (eq_div_iff hden).2
    nlinarith [hni]

/-- The literal original quadratic coefficient is continuous and integrable
for the same prescribed metric area, and computes the actual horizontal integral. -/
theorem metricTensorBookL2Pairing_horizontal_coefficient_integral
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (G : AtlasInducedMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R G.metric)
    (Q P : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    letI : MeasurableSpace X := borel X
    let μ : Measure X := harea.exists.choose
    let f : X → ℂ := fun x =>
      let e := chosenChart R.toRiemannSurface x
      Q.val x (e.val x) * conj (P.val x (e.val x)) /
        ((G.density e x ^ 2 : ℝ) : ℂ)
    Continuous f ∧ Integrable f μ ∧
      metricTensorBookL2Pairing R G.metric harea
        ((2 : ℝ) • quadraticDifferentialTensor R Q)
        ((2 : ℝ) • quadraticDifferentialTensor R P) =
          2 * (∫ x, f x ∂μ).re := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let : MeasurableSpace X := borel X
  let μ : Measure X := harea.exists.choose
  let f : X → ℂ := fun x =>
    let e := chosenChart R.toRiemannSurface x
    Q.val x (e.val x) * conj (P.val x (e.val x)) /
      ((G.density e x ^ 2 : ℝ) : ℂ)
  let F (T : HolomorphicQuadraticDifferential R.toRiemannAtlas) : X → ℝ :=
    metricTensorPointwisePairing R G.metric
      ((2 : ℝ) • quadraticDifferentialTensor R Q)
      ((2 : ℝ) • quadraticDifferentialTensor R T)
  change Continuous f ∧ Integrable f μ ∧ _ = 2 * (∫ x, f x ∂μ).re
  have hparts (x : X) : F P x = 8 * (f x).re ∧
      F (Complex.I • P) x = 8 * (f x).im :=
    horizontal_coefficient_contraction_parts R G Q P x
  have hre (x : X) : (f x).re = F P x / 8 := by
    linarith [(hparts x).1]
  have him (x : X) : (f x).im = F (Complex.I • P) x / 8 := by
    linarith [(hparts x).2]
  have hrepr : f = fun x => ((F P x / 8 : ℝ) : ℂ) +
      ((F (Complex.I • P) x / 8 : ℝ) : ℂ) * Complex.I := by
    funext x
    calc
      f x = ((f x).re : ℂ) + ((f x).im : ℂ) * Complex.I :=
        (Complex.re_add_im (f x)).symm
      _ = _ := by rw [hre, him]
  have hcontinuous (T : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
      Continuous (F T) :=
    continuous_metricTensorPointwisePairing R G.metric _ _
  have hintegrable (T : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
      Integrable (F T) μ :=
    integrable_metricTensorPointwisePairing R G.metric harea _ _
  have hc : Continuous f := by
    rw [hrepr]
    exact (Complex.continuous_ofReal.comp ((hcontinuous P).div_const 8)).add
      ((Complex.continuous_ofReal.comp ((hcontinuous (Complex.I • P)).div_const 8)).mul
        continuous_const)
  have hr : Integrable (fun x => (f x).re) μ := by
    simpa only [hre] using (hintegrable P).div_const 8
  have hi : Integrable (fun x => (f x).im) μ := by
    simpa only [him] using (hintegrable (Complex.I • P)).div_const 8
  have hf : Integrable f μ := Integrable.re_im_iff.mp ⟨hr, hi⟩
  refine ⟨hc, hf, ?_⟩
  change (1 / 4 : ℝ) * (∫ x, F P x ∂μ) = 2 * (∫ x, f x ∂μ).re
  have hpoint (x : X) : (1 / 4 : ℝ) * F P x = 2 * (f x).re := by
    linarith [(hparts x).1]
  calc
    (1 / 4 : ℝ) * (∫ x, F P x ∂μ) = ∫ x, (1 / 4 : ℝ) * F P x ∂μ :=
      (integral_const_mul _ _).symm
    _ = ∫ x, 2 * (f x).re ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = 2 * ∫ x, (f x).re ∂μ := integral_const_mul _ _
    _ = 2 * (∫ x, f x ∂μ).re := by
      simpa only [Complex.reCLM_apply] using
        congrArg (fun t : ℝ => 2 * t) (Complex.reCLM.integral_comp_comm hf)

end LowDimensionalTopology.Geometry.Teichmuller
