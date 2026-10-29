module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricTensorPairing
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# The native tensor contraction and area density in an isothermal chart

Both tensor slots are original tangent vectors. The scalar density is the
coefficient of the metric itself, and the full symmetric trace component is
retained. The area formula uses the same measure already selected by the
original area input. No integral convergence or normalization is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u

private theorem isothermal_pairing_real_inner (a b : ℂ) :
    inner ℝ a b = a.re * b.re + a.im * b.im := by
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
  change (conj a * b).re = _
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The full native symmetric contraction, including its trace component,
has the stated coefficient before and after multiplication by metric density. -/
theorem metricTensorPointwisePairing_isothermal_coefficients
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (G : AtlasInducedMetric R.toRiemannSurface)
    (h k : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface)
    (x : X) (hx : x ∈ e.val.source) (A C : ℝ) (q r : ℂ) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
    let rho : ℝ := G.density e x
    (∀ v w : RealSurfaceTangent R.toRiemannSurface x,
      h.val.toFun x v w = A * inner ℝ (D v) (D w) + (q * D v * D w).re) →
    (∀ v w : RealSurfaceTangent R.toRiemannSurface x,
      k.val.toFun x v w = C * inner ℝ (D v) (D w) + (r * D v * D w).re) →
    rho ^ 2 * metricTensorPointwisePairing R G.metric h k x =
        2 * (A * C + (q * conj r).re) ∧
      rho * metricTensorPointwisePairing R G.metric h k x =
        (2 * (A * C + (q * conj r).re)) / rho := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  let rho : ℝ := G.density e x
  let Lh : ℂ →ₗ[ℝ] ℂ := D.toLinearEquiv.conj (metricRaisedTensor R G.metric h x)
  let Lk : ℂ →ₗ[ℝ] ℂ := D.toLinearEquiv.conj (metricRaisedTensor R G.metric k x)
  dsimp only
  intro hh hk
  have hrho : rho ≠ 0 := ne_of_gt (G.density_pos e x hx)
  have htr : metricTensorPointwisePairing R G.metric h k x =
      (Lh (Lk 1)).re + (Lh (Lk Complex.I)).im := by
    calc
      metricTensorPointwisePairing R G.metric h k x =
          LinearMap.trace ℝ ℂ (Lh.comp Lk) := by
        simpa only [metricTensorPointwisePairing, Lh, Lk, LinearEquiv.conj_comp] using
          (LinearMap.trace_conj'
            ((metricRaisedTensor R G.metric h x).comp (metricRaisedTensor R G.metric k x))
            D.toLinearEquiv).symm
      _ = (Lh (Lk 1)).re + (Lh (Lk Complex.I)).im := by
        rw [LinearMap.trace_eq_matrix_trace ℝ Complex.basisOneI, Matrix.trace_fin_two]
        simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI,
          Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one,
          LinearMap.comp_apply]
  have hcoord (t : SmoothSymmetricTwoTensor R) (s : ℝ) (c a : ℂ)
      (ht : ∀ v w : RealSurfaceTangent R.toRiemannSurface x,
        t.val.toFun x v w = s * inner ℝ (D v) (D w) + (c * D v * D w).re) :
      let L : ℂ →ₗ[ℝ] ℂ := D.toLinearEquiv.conj (metricRaisedTensor R G.metric t x)
      rho * (L a).re = s * a.re + (c * a).re ∧
        rho * (L a).im = s * a.im - (c * a).im := by
    let L : ℂ →ₗ[ℝ] ℂ := D.toLinearEquiv.conj (metricRaisedTensor R G.metric t x)
    have hs (b : ℂ) : rho * inner ℝ (L a) b =
        s * inner ℝ a b + (c * a * b).re := by
      have hu := metricRaisedTensor_spec R G.metric t x (D.symm a) (D.symm b)
      rw [G.inner_eq e x hx, ht] at hu
      change rho * inner ℝ (L a) (D (D.symm b)) =
        s * inner ℝ (D (D.symm a)) (D (D.symm b)) +
          (c * D (D.symm a) * D (D.symm b)).re at hu
      simpa only [D.apply_symm_apply] using hu
    constructor
    · simpa only [isothermal_pairing_real_inner, Complex.one_re, Complex.one_im,
        mul_one, mul_zero, add_zero] using hs 1
    · simpa only [isothermal_pairing_real_inner, Complex.I_re, Complex.I_im,
        Complex.mul_re, mul_zero, mul_one, zero_add, sub_eq_add_neg] using hs Complex.I
  have hH (a : ℂ) : rho * (Lh a).re = A * a.re + (q * a).re ∧
      rho * (Lh a).im = A * a.im - (q * a).im := hcoord h A q a hh
  have hK (a : ℂ) : rho * (Lk a).re = C * a.re + (r * a).re ∧
      rho * (Lk a).im = C * a.im - (r * a).im := hcoord k C r a hk
  have hk00 : rho * (Lk 1).re = C + r.re := by
    simpa using (hK 1).1
  have hk10 : rho * (Lk 1).im = -r.im := by
    simpa using (hK 1).2
  have hk01 : rho * (Lk Complex.I).re = -r.im := by
    simpa using (hK Complex.I).1
  have hk11 : rho * (Lk Complex.I).im = C - r.re := by
    simpa using (hK Complex.I).2
  have hre : rho ^ 2 * (Lh (Lk 1)).re =
      (A + q.re) * (C + r.re) + q.im * r.im := by
    calc
      rho ^ 2 * (Lh (Lk 1)).re = rho * (rho * (Lh (Lk 1)).re) := by ring
      _ = rho * (A * (Lk 1).re + (q * Lk 1).re) := by rw [(hH (Lk 1)).1]
      _ = (A + q.re) * (rho * (Lk 1).re) - q.im * (rho * (Lk 1).im) := by
        simp only [Complex.mul_re]
        ring
      _ = (A + q.re) * (C + r.re) + q.im * r.im := by
        rw [hk00, hk10]
        ring
  have him : rho ^ 2 * (Lh (Lk Complex.I)).im =
      (A - q.re) * (C - r.re) + q.im * r.im := by
    calc
      rho ^ 2 * (Lh (Lk Complex.I)).im =
          rho * (rho * (Lh (Lk Complex.I)).im) := by ring
      _ = rho * (A * (Lk Complex.I).im - (q * Lk Complex.I).im) := by
        rw [(hH (Lk Complex.I)).2]
      _ = (A - q.re) * (rho * (Lk Complex.I).im) -
          q.im * (rho * (Lk Complex.I).re) := by
        simp only [Complex.mul_im]
        ring
      _ = (A - q.re) * (C - r.re) + q.im * r.im := by
        rw [hk11, hk01]
        ring
  have hnum : rho ^ 2 * metricTensorPointwisePairing R G.metric h k x =
      2 * (A * C + (q * conj r).re) := by
    rw [htr, mul_add, hre, him]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  refine ⟨hnum, (eq_div_iff hrho).2 ?_⟩
  calc
    (rho * metricTensorPointwisePairing R G.metric h k x) * rho =
        rho ^ 2 * metricTensorPointwisePairing R G.metric h k x := by ring
    _ = 2 * (A * C + (q * conj r).re) := hnum

/-- The already selected original area has precisely the actual isothermal
metric density in each preferred original chart, with both restrictions retained. -/
theorem originalMetricArea_isothermal_preferred_chart
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (G : AtlasInducedMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R G.metric)
    (p : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    letI : MeasurableSpace X := borel X
    let mu : Measure X := harea.exists.choose
    let e : OriginalComplexChart R.toRiemannSurface :=
      ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
    Measure.map (e.val : X → ℂ) (mu.restrict e.val.source) =
      ((volume : Measure ℂ).withDensity (fun z =>
        ENNReal.ofReal (G.density e (e.val.symm z)))).restrict e.val.target := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let : MeasurableSpace X := borel X
  let mu : Measure X := harea.exists.choose
  let e : OriginalComplexChart R.toRiemannSurface :=
    ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
  let B : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    fun z => metricGramInChart G.metric e (e.val.symm z)
  have hmu : Measure.map (e.val : X → ℂ) (mu.restrict e.val.source) =
      ((volume : Measure ℂ).withDensity (fun z =>
        ENNReal.ofReal (Real.sqrt
          (B z 1 1 * B z Complex.I Complex.I - (B z 1 Complex.I) ^ 2)))).restrict
            e.val.target := (harea.exists.choose_spec).2 p
  have hdensity (z : ℂ) (hz : z ∈ e.val.target) :
      Real.sqrt (B z 1 1 * B z Complex.I Complex.I - (B z 1 Complex.I) ^ 2) =
        G.density e (e.val.symm z) := by
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
      norm_num [isothermal_pairing_real_inner]
    have h11 : B z Complex.I Complex.I = G.density e y := by
      rw [hgram]
      norm_num [isothermal_pairing_real_inner]
    have h01 : B z 1 Complex.I = 0 := by
      rw [hgram]
      norm_num [isothermal_pairing_real_inner]
    rw [h00, h11, h01]
    simpa only [pow_two, mul_zero, sub_zero] using Real.sqrt_sq (G.density_pos e y hy).le
  change Measure.map (e.val : X → ℂ) (mu.restrict e.val.source) =
    ((volume : Measure ℂ).withDensity (fun z =>
      ENNReal.ofReal (G.density e (e.val.symm z)))).restrict e.val.target
  rw [hmu]
  simp only [MeasureTheory.restrict_withDensity e.val.open_target.measurableSet]
  apply MeasureTheory.withDensity_congr_ae
  filter_upwards [ae_restrict_mem e.val.open_target.measurableSet] with z hz
  exact congrArg ENNReal.ofReal (hdensity z hz)

end LowDimensionalTopology.Geometry.Teichmuller
