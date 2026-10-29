module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalMetricGaussianCurvatureCovariance
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricGaussianCurvature
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricScaleTwoPointwise

/-!
# Gaussian curvature of twice the same original metric

Use the already constructed isothermal realization of the original metric,
double its actual target metric and density, and prove the full pullback
identity. Covariance then reads the doubled metric in these same coordinates.
The logarithms differ by a constant, so the two second-derivative sums agree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u

private theorem scaleTwo_log_density_second_partials
    (rho : ℂ → ℝ) (s : Set ℂ) (hs : IsOpen s)
    (hpos : ∀ z ∈ s, 0 < rho z) (z : ℂ) (hz : z ∈ s) :
    (fderiv ℝ (fun a => fderiv ℝ (fun b => Real.log (2 * rho b)) a 1) z 1 +
      fderiv ℝ (fun a => fderiv ℝ (fun b => Real.log (2 * rho b)) a Complex.I)
        z Complex.I) =
    (fderiv ℝ (fun a => fderiv ℝ (fun b => Real.log (rho b)) a 1) z 1 +
      fderiv ℝ (fun a => fderiv ℝ (fun b => Real.log (rho b)) a Complex.I)
        z Complex.I) := by
  have hlog : (fun b => Real.log (2 * rho b)) =ᶠ[𝓝 z]
      (fun b => Real.log 2 + Real.log (rho b)) := by
    filter_upwards [hs.mem_nhds hz] with b hb
    exact Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (hpos b hb).ne'
  have hfirst : (fun a => fderiv ℝ (fun b => Real.log (2 * rho b)) a) =ᶠ[𝓝 z]
      (fun a => fderiv ℝ (fun b => Real.log (rho b)) a) := by
    filter_upwards [hlog.fderiv (𝕜 := ℝ)] with a ha
    simpa only [fderiv_const_add] using ha
  have hsecond (v : ℂ) :
      fderiv ℝ (fun a => fderiv ℝ (fun b => Real.log (2 * rho b)) a v) z =
        fderiv ℝ (fun a => fderiv ℝ (fun b => Real.log (rho b)) a v) z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hfirst] with a ha
    exact congrArg (fun L : ℂ →L[ℝ] ℝ => L v) ha
  rw [hsecond 1, hsecond Complex.I]

/-- Doubling the actual original metric halves its Gaussian curvature at
every original point, under the explicit classical realization covariance. -/
theorem metricGaussianCurvature_scaleTwo
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (hreg : Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (hcurv : Unproved.Teichmuller.OriginalSmoothMetricGaussianCurvature.{u})
    (hcov : Unproved.Teichmuller.OriginalMetricGaussianCurvatureCovariance.{u})
    (g : SmoothSurfaceMetric R.toRiemannSurface) (x : X) :
    metricGaussianCurvature R hreg hcurv (scaleTwoOriginalMetric R g) x =
      (1 / 2 : ℝ) * metricGaussianCurvature R hreg hcurv g x := by
  let Sclosed := rawMetricIsothermalClosedSurface R hreg g
  let S : RiemannSurface (ULift.{0} X) :=
    rawMetricIsothermalSurface R.toRiemannSurface hreg g
  let f : SmoothSurfaceEquiv R.toRiemannSurface S :=
    rawMetricIsothermalMarking R.toRiemannSurface hreg g
  let G : AtlasInducedMetric S :=
    rawMetricIsothermalTargetMetric R.toRiemannSurface hreg g
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.isRealManifold
  let G₂ : AtlasInducedMetric S := by
    refine
      { metric := scaleTwoOriginalMetric Sclosed G.metric
        density := fun e y => 2 * G.density e y
        density_smooth := ?_
        density_pos := ?_
        inner_eq := ?_ }
    · intro e
      exact contMDiffOn_const.mul (G.density_smooth e)
    · intro e y hy
      exact mul_pos (by norm_num) (G.density_pos e y hy)
    · intro e y hy v w
      change 2 * G.metric.inner y v w = (2 * G.density e y) *
        inner ℝ (originalChartDifferential S e y v) (originalChartDifferential S e y w)
      rw [G.inner_eq e y hy]
      ring
  have hrealization (p : X) (v w : RealSurfaceTangent R.toRiemannSurface p) :
      G₂.metric.inner (f.toHomeomorph p)
          (surfaceDifferential R.toRiemannSurface S f p v)
          (surfaceDifferential R.toRiemannSurface S f p w) =
        (scaleTwoOriginalMetric R g).inner p v w := by
    change 2 * (SmoothSurfaceMetric.pullback f G.metric).inner p v w =
      2 * g.inner p v w
    exact congrArg (fun a : ℝ => 2 * a)
      (rawMetricIsothermalTargetMetric_pullback_inner R.toRiemannSurface hreg g p v w)
  let K : X → ℝ := metricGaussianCurvature R hreg hcurv g
  let K₂ : X → ℝ := metricGaussianCurvature R hreg hcurv (scaleTwoOriginalMetric R g)
  have hK := (metricGaussianCurvature_spec R hreg hcurv g).2
  have hK₂ := (metricGaussianCurvature_spec R hreg hcurv (scaleTwoOriginalMetric R g)).2
  have hcov₂ := hcov X R hreg (scaleTwoOriginalMetric R g) K₂ hK₂ S f G₂ hrealization
  let y := f.toHomeomorph x
  let e : OriginalComplexChart S := ⟨chartAt ℂ y, chart_mem_atlas ℂ y⟩
  have hy : y ∈ e.val.source := mem_chart_source ℂ y
  have hz : e.val y ∈ e.val.target := e.val.map_source hy
  have hx : (SmoothSurfaceEquiv.symm f).toHomeomorph (e.val.symm (e.val y)) = x := by
    rw [e.val.left_inv hy]
    exact f.toHomeomorph.symm_apply_apply x
  let rho : ℂ → ℝ := fun a => G.density e (e.val.symm a)
  let ell : ℂ → ℝ := fun a => Real.log (rho a)
  let ell₂ : ℂ → ℝ := fun a => Real.log (2 * rho a)
  let lap : ℝ := fderiv ℝ (fun a => fderiv ℝ ell a 1) (e.val y) 1 +
    fderiv ℝ (fun a => fderiv ℝ ell a Complex.I) (e.val y) Complex.I
  let lap₂ : ℝ := fderiv ℝ (fun a => fderiv ℝ ell₂ a 1) (e.val y) 1 +
    fderiv ℝ (fun a => fderiv ℝ ell₂ a Complex.I) (e.val y) Complex.I
  have hpos (a : ℂ) (ha : a ∈ e.val.target) : 0 < rho a :=
    G.density_pos e (e.val.symm a) (e.val.map_target ha)
  have hlap : lap₂ = lap :=
    scaleTwo_log_density_second_partials rho e.val.target e.val.open_target hpos (e.val y) hz
  have hc := hcov₂ e (e.val y) hz
  have hg := hK e (e.val y) hz
  change K₂ ((SmoothSurfaceEquiv.symm f).toHomeomorph (e.val.symm (e.val y))) =
    -lap₂ / (2 * (2 * rho (e.val y))) at hc
  change K ((SmoothSurfaceEquiv.symm f).toHomeomorph (e.val.symm (e.val y))) =
    -lap / (2 * rho (e.val y)) at hg
  rw [hx, hlap] at hc
  rw [hx] at hg
  change K₂ x = (1 / 2 : ℝ) * K x
  rw [hc, hg]
  field_simp [(hpos (e.val y) hz).ne']

end LowDimensionalTopology.Geometry.Teichmuller
