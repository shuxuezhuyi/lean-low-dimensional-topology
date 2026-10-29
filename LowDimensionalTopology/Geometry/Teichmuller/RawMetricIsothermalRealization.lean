module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricIsothermalMarking
public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricConformality

/-!
# The same original metric on the native isothermal marked target

The actual inverse marking pulls back the whole original smooth metric.
The original all-vector density identity proves that this transported metric
is compatible with the constructed target atlas. Pulling it back by the same
marking recovers every original metric entry, and the existing coefficient
calculation then applies in every valid original source chart.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Manifold ContDiff InnerProductSpace

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X]

def rawMetricIsothermalTargetPatch (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R)
    (e : OriginalComplexChart (rawMetricIsothermalSurface R hreg g)) :
    RawMetricIsothermalPatch g :=
  RawMetricIsothermalPatch.atPoint hreg g
    (((rawMetricIsothermalAtlas_mem_iff R hreg g e.val).mp e.property).choose)

theorem rawMetricIsothermalTargetPatch_chart (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R)
    (e : OriginalComplexChart (rawMetricIsothermalSurface R hreg g)) :
    (rawMetricIsothermalTargetPatch R hreg g e).liftedChart = e.val :=
  ((rawMetricIsothermalAtlas_mem_iff R hreg g e.val).mp e.property).choose_spec

/-- The full original metric, transported by the actual inverse marking, is
compatible with the genuinely constructed new atlas. Compatibility is proved
as an output, not assumed of the original metric. -/
def rawMetricIsothermalTargetMetric (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) : AtlasInducedMetric (rawMetricIsothermalSurface R hreg g) := by
  let S := rawMetricIsothermalSurface R hreg g
  let f := rawMetricIsothermalMarking R hreg g
  let j := SmoothSurfaceEquiv.symm f
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  refine
    { metric := SmoothSurfaceMetric.pullback j g
      density := fun e y => (rawMetricIsothermalTargetPatch R hreg g e).density y.down
      density_smooth := ?_
      density_pos := ?_
      inner_eq := ?_ }
  · intro e
    let P := rawMetricIsothermalTargetPatch R hreg g e
    have heq : P.liftedChart = e.val := rawMetricIsothermalTargetPatch_chart R hreg g e
    have hρ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ P.density P.chart.source := by
      rw [P.chart_source]
      exact P.density_native
    have hmap : MapsTo j.toHomeomorph e.val.source P.chart.source := by
      intro y hy
      rw [← heq] at hy
      exact hy
    exact hρ.comp j.contMDiff_toFun.contMDiffOn hmap
  · intro e y hy
    let P := rawMetricIsothermalTargetPatch R hreg g e
    have heq : P.liftedChart = e.val := rawMetricIsothermalTargetPatch_chart R hreg g e
    have hC : y.down ∈ P.chart.source := by
      rw [← heq] at hy
      exact hy
    exact P.chart_density_pos y.down hC
  · intro e y hy u v
    let P := rawMetricIsothermalTargetPatch R hreg g e
    have heq : P.liftedChart = e.val := rawMetricIsothermalTargetPatch_chart R hreg g e
    have hC : y.down ∈ P.chart.source := by
      rw [← heq] at hy
      exact hy
    have hOld := hC
    rw [P.chart_source] at hOld
    let A := surfaceDifferential S R j y
    have hCD : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (P.chart : X → ℂ) y.down := by
      change MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
        ((P.coordinate : ℂ → ℂ) ∘ (P.oldChart.val : X → ℂ)) y.down
      exact ((P.coordinate_contDiff.differentiable (by simp)
        (P.oldChart.val y.down)).mdifferentiableAt).comp y.down
          (mdifferentiableAt_atlas (I := 𝓘(ℝ, ℂ)) P.oldChart.property hOld.1)
    have hj : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) j.toHomeomorph y :=
      j.contMDiff_toFun.mdifferentiableAt (by simp)
    have hD (a : RealSurfaceTangent S y) :
        mvfderiv 𝓘(ℝ, ℂ)
            ((P.coordinate : ℂ → ℂ) ∘ (P.oldChart.val : X → ℂ)) y.down (A a) =
          originalChartDifferential S e y a := by
      have hh := congrArg (fun L : RealSurfaceTangent S y →L[ℝ] ℂ => L a)
        (mvfderiv_comp y hCD hj)
      change mvfderiv 𝓘(ℝ, ℂ) (P.chart : X → ℂ) y.down (A a) =
        mvfderiv 𝓘(ℝ, ℂ) (e.val : ULift.{0} X → ℂ) y a
      rw [← heq]
      exact hh.symm
    have hg := P.chart_inner_eq y.down hC (A u) (A v)
    rw [SmoothSurfaceMetric.pullback_inner]
    change g.inner y.down (A u) (A v) = P.density y.down *
      ⟪originalChartDifferential S e y u, originalChartDifferential S e y v⟫_ℝ
    rw [hg, hD u, hD v]

/-- Pulling back the transported target metric recovers the same original g
on every original point and every original tangent pair. -/
theorem rawMetricIsothermalTargetMetric_pullback_inner (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (x : X) (v t : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (SmoothSurfaceMetric.pullback (rawMetricIsothermalMarking R hreg g)
      (rawMetricIsothermalTargetMetric R hreg g).metric).inner x v t = g.inner x v t := by
  let S := rawMetricIsothermalSurface R hreg g
  let f := rawMetricIsothermalMarking R hreg g
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  have hf : SmoothSurfaceEquiv.trans f (SmoothSurfaceEquiv.symm f) =
      SmoothSurfaceEquiv.refl R := Diffeomorph.self_trans_symm f
  change (SmoothSurfaceMetric.pullback f
    (SmoothSurfaceMetric.pullback (SmoothSurfaceEquiv.symm f) g)).inner x v t = g.inner x v t
  rw [← SmoothSurfaceMetric.pullback_trans_inner, hf, SmoothSurfaceMetric.pullback_refl_inner]

/-- Every valid original chart reads the literal original metric coefficient
as the coefficient of the actual smooth positive marking. -/
theorem rawMetricIsothermalMarking_metricBeltrami (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R) (x : X)
    (hx : x ∈ e.val.source) :
    metricBeltramiInOriginalChart g e x hx =
      (rawMetricIsothermalMarking R hreg g).rawBeltramiCoefficient e (e.val x) := by
  let S := rawMetricIsothermalSurface R hreg g
  let f := rawMetricIsothermalMarking R hreg g
  let h := rawMetricIsothermalTargetMetric R hreg g
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  have hpull := pullback_metricBeltrami_eq_marking f
    (rawMetricIsothermalMarking_preservesComplexOrientation R hreg g) h e x hx
  have hcoeff : metricBeltramiInOriginalChart (SmoothSurfaceMetric.pullback f h.metric) e x hx =
      metricBeltramiInOriginalChart g e x hx := by
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
    change metricBeltramiFromGram
      ((SmoothSurfaceMetric.pullback f h.metric).inner x (D.symm 1) (D.symm 1))
      ((SmoothSurfaceMetric.pullback f h.metric).inner x (D.symm 1) (D.symm Complex.I))
      ((SmoothSurfaceMetric.pullback f h.metric).inner x
        (D.symm Complex.I) (D.symm Complex.I)) =
      metricBeltramiFromGram
        (g.inner x (D.symm 1) (D.symm 1))
        (g.inner x (D.symm 1) (D.symm Complex.I))
        (g.inner x (D.symm Complex.I) (D.symm Complex.I))
    rw [rawMetricIsothermalTargetMetric_pullback_inner,
      rawMetricIsothermalTargetMetric_pullback_inner,
      rawMetricIsothermalTargetMetric_pullback_inner]
  exact hcoeff.symm.trans hpull

/-- The already total raw formula is compared only at genuine original chart
points, where it has the proved geometric meaning. -/
theorem rawMetricIsothermalMarking_rawCoefficient (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R) (x : X)
    (hx : x ∈ e.val.source) :
    metricBeltramiInChart g e x =
      (rawMetricIsothermalMarking R hreg g).rawBeltramiCoefficient e (e.val x) := by
  rw [metricBeltramiInChart_eq g e x hx]
  exact rawMetricIsothermalMarking_metricBeltrami R hreg g e x hx

end LowDimensionalTopology.Geometry.Teichmuller
