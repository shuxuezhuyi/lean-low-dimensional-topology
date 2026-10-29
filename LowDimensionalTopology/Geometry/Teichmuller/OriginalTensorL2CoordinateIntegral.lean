module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalTensorL2Integrability
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Original tensor integration in a preferred original chart

The exact prescribed metric-area map law transports the original scalar
contraction. All measurability arguments stay on the actual chart target;
no continuity of an off-target totalization is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Manifold ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u

/-- The full original contraction has its true Gram-density coordinate integral,
with both the original chart source and its target explicitly restricted. -/
theorem metricTensorPointwisePairing_integral_preferred_chart
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R g)
    (h k : SmoothSymmetricTwoTensor R) (p : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    letI : MeasurableSpace X := borel X
    let μ : Measure X := harea.exists.choose
    let e : OriginalComplexChart R.toRiemannSurface :=
      ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
    let B : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
      fun z => metricGramInChart g e (e.val.symm z)
    let rho : ℂ → ℝ := fun z => Real.sqrt
      (B z 1 1 * B z Complex.I Complex.I - (B z 1 Complex.I) ^ 2)
    (∫ x in e.val.source, metricTensorPointwisePairing R g h k x ∂μ) =
      ∫ z in e.val.target,
        metricTensorPointwisePairing R g h k (e.val.symm z) * rho z
          ∂(volume : Measure ℂ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let μ : Measure X := harea.exists.choose
  let e : OriginalComplexChart R.toRiemannSurface :=
    ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
  let F : X → ℝ := metricTensorPointwisePairing R g h k
  let f : ℂ → ℝ := fun z => F (e.val.symm z)
  let B : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    fun z => metricGramInChart g e (e.val.symm z)
  let rho : ℂ → ℝ := fun z => Real.sqrt
    (B z 1 1 * B z Complex.I Complex.I - (B z 1 Complex.I) ^ 2)
  let ν : Measure ℂ :=
    (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (rho z))
  have hmap : Measure.map (e.val : X → ℂ) (μ.restrict e.val.source) =
      ν.restrict e.val.target := harea.exists.choose_spec.2 p
  have he : AEMeasurable (e.val : X → ℂ) (μ.restrict e.val.source) :=
    e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  have hF : Continuous F := continuous_metricTensorPointwisePairing R g h k
  have hf : ContinuousOn f e.val.target :=
    hF.comp_continuousOn' e.val.symm.continuousOn
  have hfmeas : AEStronglyMeasurable f
      (Measure.map (e.val : X → ℂ) (μ.restrict e.val.source)) := by
    rw [hmap]
    exact hf.aestronglyMeasurable e.val.open_target.measurableSet
  have hGram : ContinuousOn (metricGramInChart g e) e.val.source :=
    (metricGramInChart_contMDiffOn g e).continuousOn
  have hB : ContinuousOn B e.val.target :=
    hGram.comp e.val.symm.continuousOn (fun z hz => e.val.map_target hz)
  have hc (a b : ℂ) : ContinuousOn (fun z => B z a b) e.val.target :=
    (hB.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hrho : ContinuousOn rho e.val.target :=
    Real.continuous_sqrt.comp_continuousOn'
      (((hc 1 1).mul (hc Complex.I Complex.I)).sub ((hc 1 Complex.I).pow 2))
  have hmeasrho : AEMeasurable (fun z => ENNReal.ofReal (rho z))
      ((volume : Measure ℂ).restrict e.val.target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (hrho.aemeasurable e.val.open_target.measurableSet)
  have hfinite : ∀ᵐ z ∂(volume : Measure ℂ).restrict e.val.target,
      ENNReal.ofReal (rho z) < ∞ :=
    Filter.Eventually.of_forall (fun z => by simp)
  have hweight : (∫ z in e.val.target, f z ∂ν) =
      ∫ z in e.val.target, f z * rho z ∂(volume : Measure ℂ) := by
    change (∫ z, f z ∂((volume : Measure ℂ).withDensity
        (fun z => ENNReal.ofReal (rho z))).restrict e.val.target) = _
    rw [restrict_withDensity e.val.open_target.measurableSet,
      integral_withDensity_eq_integral_toReal_smul₀ hmeasrho hfinite]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      have hnonneg : 0 ≤ rho z := Real.sqrt_nonneg _
      change (ENNReal.ofReal (rho z)).toReal • f z = f z * rho z
      rw [ENNReal.toReal_ofReal hnonneg]
      change rho z * f z = f z * rho z
      exact mul_comm _ _)
  change (∫ x in e.val.source, F x ∂μ) =
    ∫ z in e.val.target, f z * rho z ∂(volume : Measure ℂ)
  calc
    (∫ x in e.val.source, F x ∂μ) =
        ∫ x in e.val.source, f (e.val x) ∂μ := by
      apply setIntegral_congr_fun e.val.open_source.measurableSet
      intro x hx
      change F x = F (e.val.symm (e.val x))
      rw [e.val.left_inv hx]
    _ = ∫ z, f z ∂Measure.map (e.val : X → ℂ) (μ.restrict e.val.source) :=
      (integral_map he hfmeas).symm
    _ = ∫ z in e.val.target, f z ∂ν := by rw [hmap]
    _ = ∫ z in e.val.target, f z * rho z ∂(volume : Measure ℂ) := hweight

open scoped InnerProductSpace ComplexConjugate in
/-- For the same inducing metric and arbitrary original tensors, the true
coordinate-area coefficient is lambda = G.density, which is rho_book squared. -/
theorem metricTensorPointwisePairing_integral_isothermal_preferred_chart
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (G : AtlasInducedMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R G.metric)
    (h k : SmoothSymmetricTwoTensor R) (p : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    letI : MeasurableSpace X := borel X
    let μ : Measure X := harea.exists.choose
    let e : OriginalComplexChart R.toRiemannSurface :=
      ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
    (∫ x in e.val.source, metricTensorPointwisePairing R G.metric h k x ∂μ) =
      ∫ z in e.val.target,
        metricTensorPointwisePairing R G.metric h k (e.val.symm z) *
          G.density e (e.val.symm z) ∂(volume : Measure ℂ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let : MeasurableSpace X := borel X
  let μ : Measure X := harea.exists.choose
  let e : OriginalComplexChart R.toRiemannSurface :=
    ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
  let B : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    fun z => metricGramInChart G.metric e (e.val.symm z)
  let rho : ℂ → ℝ := fun z => Real.sqrt
    (B z 1 1 * B z Complex.I Complex.I - (B z 1 Complex.I) ^ 2)
  have hraw : (∫ x in e.val.source, metricTensorPointwisePairing R G.metric h k x ∂μ) =
      ∫ z in e.val.target,
        metricTensorPointwisePairing R G.metric h k (e.val.symm z) * rho z
          ∂(volume : Measure ℂ) :=
    metricTensorPointwisePairing_integral_preferred_chart R G.metric harea h k p
  have hreal (a b : ℂ) : inner ℝ a b = a.re * b.re + a.im * b.im := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
    change (conj a * b).re = _
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hdensity (z : ℂ) (hz : z ∈ e.val.target) :
      rho z = G.density e (e.val.symm z) := by
    let y := e.val.symm z
    have hy : y ∈ e.val.source := e.val.map_target hz
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e y hy
    have hgram (a b : ℂ) : B z a b = G.density e y * inner ℝ a b := by
      change metricGramInChart G.metric e y a b = _
      rw [metricGramInChart_eq G.metric e y hy]
      change G.metric.inner y (D.symm a) (D.symm b) = _
      rw [G.inner_eq e y hy]
      change G.density e y * inner ℝ (D (D.symm a)) (D (D.symm b)) = _
      rw [D.apply_symm_apply, D.apply_symm_apply]
    have h00 : B z 1 1 = G.density e y := by
      rw [hgram]
      norm_num [hreal]
    have h11 : B z Complex.I Complex.I = G.density e y := by
      rw [hgram]
      norm_num [hreal]
    have h01 : B z 1 Complex.I = 0 := by
      rw [hgram]
      norm_num [hreal]
    change Real.sqrt (B z 1 1 * B z Complex.I Complex.I - (B z 1 Complex.I) ^ 2) =
      G.density e y
    rw [h00, h11, h01]
    simpa only [pow_two, mul_zero, sub_zero] using Real.sqrt_sq (G.density_pos e y hy).le
  change (∫ x in e.val.source, metricTensorPointwisePairing R G.metric h k x ∂μ) =
    ∫ z in e.val.target,
      metricTensorPointwisePairing R G.metric h k (e.val.symm z) *
        G.density e (e.val.symm z) ∂(volume : Measure ℂ)
  rw [hraw]
  apply setIntegral_congr_fun e.val.open_target.measurableSet
  intro z hz
  change metricTensorPointwisePairing R G.metric h k (e.val.symm z) * rho z =
    metricTensorPointwisePairing R G.metric h k (e.val.symm z) *
      G.density e (e.val.symm z)
  rw [hdensity z hz]

end LowDimensionalTopology.Geometry.Teichmuller
