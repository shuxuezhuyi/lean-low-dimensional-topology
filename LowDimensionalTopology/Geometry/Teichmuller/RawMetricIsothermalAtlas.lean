module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricIsothermalOverlap
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Closed
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The native complex atlas of an arbitrary original smooth metric

Every local patch below is constructed from the actual local density theorem.
Its full original metric identity and actual coordinate maps give the analytic
overlaps. The new atlas lives on the homeomorphic copy ULift.{0} X, leaving the
original topology and the original real tangent bundle unchanged. No complex
atlas or compatibility assumption is an input to the existence construction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Manifold ContDiff InnerProductSpace

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}

/-- Concrete local data already supplied by the actual density theorem.
There is no atlas, global marking, or global realization field. -/
structure RawMetricIsothermalPatch (g : SmoothSurfaceMetric R) where
  oldChart : OriginalComplexChart R
  domain : Set ℂ
  domain_open : IsOpen domain
  domain_subset : domain ⊆ oldChart.val.target
  coordinate : ℂ ≃ₜ ℂ
  coordinate_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (coordinate : ℂ → ℂ)
  inverse_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (coordinate.symm : ℂ → ℂ)
  beltrami_equation : ∀ z ∈ domain,
    LiZhongQC.dzbar (coordinate : ℂ → ℂ) z =
      metricBeltramiInChart g oldChart (oldChart.val.symm z) *
        LiZhongQC.dz (coordinate : ℂ → ℂ) z
  jacobian_pos : ∀ z, 0 < LiZhongQC.jacobian (coordinate : ℂ → ℂ) z
  density_contDiffOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (rawMetricIsothermalDensity g oldChart (coordinate : ℂ → ℂ)) domain
  density_pos : ∀ z ∈ domain,
    0 < rawMetricIsothermalDensity g oldChart (coordinate : ℂ → ℂ) z
  density_native :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞
      (fun x => rawMetricIsothermalDensity g oldChart (coordinate : ℂ → ℂ) (oldChart.val x))
      (oldChart.val.source ∩ oldChart.val ⁻¹' domain)
  inner_eq :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ x ∈ oldChart.val.source ∩ oldChart.val ⁻¹' domain,
      ∀ v t : RealSurfaceTangent R x,
        g.inner x v t =
          rawMetricIsothermalDensity g oldChart (coordinate : ℂ → ℂ) (oldChart.val x) *
            ⟪mvfderiv 𝓘(ℝ, ℂ) ((coordinate : ℂ → ℂ) ∘ (oldChart.val : X → ℂ)) x v,
              mvfderiv 𝓘(ℝ, ℂ) ((coordinate : ℂ → ℂ) ∘ (oldChart.val : X → ℂ)) x t⟫_ℝ

namespace RawMetricIsothermalPatch

variable {g : SmoothSurfaceMetric R}

/-- The actual coordinate, restricted to its genuine local domain. -/
def chart (P : RawMetricIsothermalPatch g) : OpenPartialHomeomorph X ℂ :=
  rawMetricIsothermalChart P.oldChart P.domain P.domain_open P.coordinate

/-- The density as a function on the unchanged original surface. -/
def density (P : RawMetricIsothermalPatch g) (x : X) : ℝ :=
  rawMetricIsothermalDensity g P.oldChart (P.coordinate : ℂ → ℂ) (P.oldChart.val x)

theorem chart_source (P : RawMetricIsothermalPatch g) :
    P.chart.source = P.oldChart.val.source ∩ P.oldChart.val ⁻¹' P.domain :=
  rawMetricIsothermalChart_source P.oldChart P.domain P.domain_open P.coordinate

theorem chart_target (P : RawMetricIsothermalPatch g) :
    P.chart.target = P.coordinate '' P.domain :=
  rawMetricIsothermalChart_target_of_subset P.oldChart P.domain P.domain_open
    P.coordinate P.domain_subset

@[simp]
theorem chart_apply (P : RawMetricIsothermalPatch g) (x : X) :
    P.chart x = P.coordinate (P.oldChart.val x) := rfl

@[simp]
theorem chart_symm_apply (P : RawMetricIsothermalPatch g) (z : ℂ) :
    P.chart.symm z = P.oldChart.val.symm (P.coordinate.symm z) := rfl

theorem chart_density_pos (P : RawMetricIsothermalPatch g) (x : X)
    (hx : x ∈ P.chart.source) : 0 < P.density x := by
  rw [P.chart_source] at hx
  exact P.density_pos (P.oldChart.val x) hx.2

theorem chart_inner_eq (P : RawMetricIsothermalPatch g) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ x ∈ P.chart.source, ∀ v t : RealSurfaceTangent R x,
      g.inner x v t = P.density x *
        ⟪mvfderiv 𝓘(ℝ, ℂ) ((P.coordinate : ℂ → ℂ) ∘ (P.oldChart.val : X → ℂ)) x v,
          mvfderiv 𝓘(ℝ, ℂ) ((P.coordinate : ℂ → ℂ) ∘ (P.oldChart.val : X → ℂ)) x t⟫_ℝ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro x hx v t
  rw [P.chart_source] at hx
  exact P.inner_eq x hx v t

theorem exists_at_point
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (x : X) :
    ∃ P : RawMetricIsothermalPatch g, x ∈ P.chart.source := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let e : OriginalComplexChart R := ⟨(R.cover x).choose, (R.cover x).choose_spec.1⟩
  have hx : x ∈ e.val.source := (R.cover x).choose_spec.2
  obtain ⟨V, w, hV, _hzV, hVU, hw, hwi, hPDE, hJ, hρ, hρpos, _hW, hxW,
      hρNative, hinner⟩ :=
    exists_rawMetric_local_isothermal_density_of_regularity hreg g e x hx
  let P : RawMetricIsothermalPatch g :=
    { oldChart := e
      domain := V
      domain_open := hV
      domain_subset := hVU
      coordinate := w
      coordinate_contDiff := hw
      inverse_contDiff := hwi
      beltrami_equation := hPDE
      jacobian_pos := hJ
      density_contDiffOn := hρ
      density_pos := hρpos
      density_native := hρNative
      inner_eq := hinner }
  refine ⟨P, ?_⟩
  rw [P.chart_source]
  exact hxW

/-- Choose the actual producer output at each original point. The only hard
input is the existing explicit regularity statement. -/
def atPoint
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (x : X) : RawMetricIsothermalPatch g :=
  (exists_at_point hreg g x).choose

theorem atPoint_mem_source
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (x : X) : x ∈ (atPoint hreg g x).chart.source :=
  (exists_at_point hreg g x).choose_spec

/-- Analytic compatibility is proved from the same actual metric on all of
its original tangent vectors, using the concrete overlap theorem. -/
theorem overlap_analytic (P Q : RawMetricIsothermalPatch g) :
    AnalyticOnNhd ℂ (P.chart.symm.trans Q.chart) (P.chart.symm.trans Q.chart).source := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact (rawMetricIsothermalOverlap_analytic_and_orientation g P.oldChart Q.oldChart
    P.domain Q.domain P.domain_open Q.domain_open P.coordinate Q.coordinate
    P.density Q.density P.coordinate_contDiff P.inverse_contDiff Q.coordinate_contDiff
    P.jacobian_pos Q.jacobian_pos P.chart_density_pos Q.chart_density_pos
    P.chart_inner_eq Q.chart_inner_eq).1

/-- The same actual chart transported to a homeomorphic copy of the original
space. The topology is the existing ULift topology. -/
def liftedChart (P : RawMetricIsothermalPatch g) : OpenPartialHomeomorph (ULift.{0} X) ℂ :=
  (Homeomorph.ulift : ULift.{0} X ≃ₜ X).transOpenPartialHomeomorph P.chart

@[simp]
theorem liftedChart_apply (P : RawMetricIsothermalPatch g) (y : ULift.{0} X) :
    P.liftedChart y = P.chart y.down := rfl

@[simp]
theorem liftedChart_symm_apply (P : RawMetricIsothermalPatch g) (z : ℂ) :
    P.liftedChart.symm z = ULift.up (P.chart.symm z) := rfl

theorem liftedChart_source (P : RawMetricIsothermalPatch g) :
    P.liftedChart.source = ULift.down ⁻¹' P.chart.source := rfl

theorem liftedChart_target (P : RawMetricIsothermalPatch g) :
    P.liftedChart.target = P.chart.target := rfl

/-- The original global homeomorphism cancels in the actual overlap map,
including its true source; no tangent-space identification is involved. -/
theorem lifted_overlap_analytic (P Q : RawMetricIsothermalPatch g) :
    AnalyticOnNhd ℂ (P.liftedChart.symm.trans Q.liftedChart)
      (P.liftedChart.symm.trans Q.liftedChart).source := by
  simpa only [liftedChart, Homeomorph.transOpenPartialHomeomorph_symm_trans] using
    P.overlap_analytic Q

end RawMetricIsothermalPatch

/-- One genuine new chart at each original point, on the homeomorphic copy. -/
def rawMetricIsothermalChartAt (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (x : X) : OpenPartialHomeomorph (ULift.{0} X) ℂ :=
  (RawMetricIsothermalPatch.atPoint hreg g x).liftedChart

/-- The full covering atlas constructed from the actual local solutions of
the same original arbitrary metric. No compatible-atlas hypothesis occurs. -/
def rawMetricIsothermalAtlas (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) : RiemannAtlas (ULift.{0} X) where
  charts := Set.range (rawMetricIsothermalChartAt R hreg g)
  cover y := by
    refine ⟨rawMetricIsothermalChartAt R hreg g y.down, ⟨y.down, rfl⟩, ?_⟩
    exact RawMetricIsothermalPatch.atPoint_mem_source hreg g y.down
  compatible e he f hf := by
    obtain ⟨x, rfl⟩ := he
    obtain ⟨y, rfl⟩ := hf
    exact (RawMetricIsothermalPatch.atPoint hreg g x).lifted_overlap_analytic
      (RawMetricIsothermalPatch.atPoint hreg g y)

theorem rawMetricIsothermalAtlas_chart_mem (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (x : X) :
    rawMetricIsothermalChartAt R hreg g x ∈ (rawMetricIsothermalAtlas R hreg g).charts :=
  ⟨x, rfl⟩

theorem rawMetricIsothermalAtlas_mem_iff (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (c : OpenPartialHomeomorph (ULift.{0} X) ℂ) :
    c ∈ (rawMetricIsothermalAtlas R hreg g).charts ↔
      ∃ x : X, rawMetricIsothermalChartAt R hreg g x = c := Iff.rfl

theorem rawMetricIsothermalChartAt_mem_source (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) (x : X) :
    ULift.up x ∈ (rawMetricIsothermalChartAt R hreg g x).source :=
  RawMetricIsothermalPatch.atPoint_mem_source hreg g x

/-- The genuinely new complex surface with the original topology transported
by the actual ULift homeomorphism. No compactness or genus is required. -/
def rawMetricIsothermalSurface (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) : RiemannSurface (ULift.{0} X) where
  toRiemannAtlas := rawMetricIsothermalAtlas R hreg g
  t2Space := by
    let := R.t2Space
    exact (Homeomorph.ulift : ULift.{0} X ≃ₜ X).isEmbedding.t2Space
  connectedSpace :=
    (Homeomorph.ulift : ULift.{0} X ≃ₜ X).connectedSpace_iff.mpr R.connectedSpace

/-- An originally closed reference gives a closed new surface by transporting
its given compactness, without adding any assumption to the raw metric. -/
def rawMetricIsothermalClosedSurface (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R.toRiemannSurface) : ClosedRiemannSurface (ULift.{0} X) where
  toRiemannSurface := rawMetricIsothermalSurface R.toRiemannSurface hreg g
  compactSpace := by
    let := R.compactSpace
    exact (Homeomorph.ulift : ULift.{0} X ≃ₜ X).symm.compactSpace

end LowDimensionalTopology.Geometry.Teichmuller
