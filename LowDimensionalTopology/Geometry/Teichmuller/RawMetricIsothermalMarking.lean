module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricIsothermalAtlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The actual smooth oriented marking of the native isothermal surface

The marking is the genuine ULift homeomorphism in the forward direction.
Both real smoothness statements follow from actual local chart compositions.
Every old source chart is checked for positive orientation using the original
analytic transition and the actual positive Jacobian of the plane solution.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}

private theorem patch_chart_contMDiffAt {g : SmoothSurfaceMetric R}
    (P : RawMetricIsothermalPatch g) {x : X} (hx : x ∈ P.chart.source) :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (P.chart : X → ℂ) x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  rw [P.chart_source] at hx
  have he : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (P.oldChart.val : X → ℂ) x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas P.oldChart.property) hx.1
  change ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
    ((P.coordinate : ℂ → ℂ) ∘ (P.oldChart.val : X → ℂ)) x
  exact P.coordinate_contDiff.comp_contMDiffAt he

private theorem patch_chart_symm_contMDiffAt {g : SmoothSurfaceMetric R}
    (P : RawMetricIsothermalPatch g) {z : ℂ} (hz : z ∈ P.chart.target) :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (P.chart.symm : ℂ → X) z := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have hzt : P.coordinate.symm z ∈ P.oldChart.val.target := by
    rw [P.chart_target] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    simpa only [P.coordinate.symm_apply_apply] using P.domain_subset ha
  have he : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (P.oldChart.val.symm : ℂ → X) (P.coordinate.symm z) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas P.oldChart.property) hzt
  change ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
    ((P.oldChart.val.symm : ℂ → X) ∘ (P.coordinate.symm : ℂ → ℂ)) z
  exact he.comp z P.inverse_contDiff.contMDiff.contMDiffAt

/-- The unchanged original point is sent to its actual homeomorphic copy by
a real smooth map for the original and new atlases. -/
theorem rawMetricIsothermalUp_contMDiff (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) :
    let := R.toRiemannAtlas.toChartedSpace
    let := (rawMetricIsothermalSurface R hreg g).toRiemannAtlas.toChartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (ULift.up : X → ULift.{0} X) := by
  let S := rawMetricIsothermalSurface R hreg g
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  dsimp only
  intro x
  let P := RawMetricIsothermalPatch.atPoint hreg g x
  let E := P.liftedChart
  have hx : x ∈ P.chart.source := RawMetricIsothermalPatch.atPoint_mem_source hreg g x
  have hmem : E ∈ S.charts := rawMetricIsothermalAtlas_chart_mem R hreg g x
  have ht : P.chart x ∈ E.target := P.chart.map_source hx
  have hInv : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (E.symm : ℂ → ULift.{0} X) (P.chart x) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hmem) ht
  apply (hInv.comp x (patch_chart_contMDiffAt P hx)).congr_of_eventuallyEq
  filter_upwards [P.chart.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply, E, RawMetricIsothermalPatch.liftedChart_symm_apply,
    P.chart.left_inv hy]

/-- The actual inverse homeomorphism is real smooth, using the same local
inverse coordinate maps, rather than an assumed atlas compatibility. -/
theorem rawMetricIsothermalDown_contMDiff (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) :
    let := R.toRiemannAtlas.toChartedSpace
    let := (rawMetricIsothermalSurface R hreg g).toRiemannAtlas.toChartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (ULift.down : ULift.{0} X → X) := by
  let S := rawMetricIsothermalSurface R hreg g
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  dsimp only
  intro y
  let P := RawMetricIsothermalPatch.atPoint hreg g y.down
  let E := P.liftedChart
  have hy : y ∈ E.source := RawMetricIsothermalPatch.atPoint_mem_source hreg g y.down
  have hmem : E ∈ S.charts := rawMetricIsothermalAtlas_chart_mem R hreg g y.down
  have ht : E y ∈ P.chart.target := E.map_source hy
  have hE : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (E : ULift.{0} X → ℂ) y :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hmem) hy
  apply ((patch_chart_symm_contMDiffAt P ht).comp y hE).congr_of_eventuallyEq
  filter_upwards [E.open_source.mem_nhds hy] with z hz
  have hzc : z.down ∈ P.chart.source := hz
  simp only [Function.comp_apply, E, RawMetricIsothermalPatch.liftedChart_apply,
    P.chart.left_inv hzc]

/-- The actual ULift homeomorphism, with its two real smoothness proofs. -/
def rawMetricIsothermalMarking (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) :
    SmoothSurfaceEquiv R (rawMetricIsothermalSurface R hreg g) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := (rawMetricIsothermalSurface R hreg g).toRiemannAtlas.toChartedSpace
  exact
    { toEquiv := (Homeomorph.ulift : ULift.{0} X ≃ₜ X).symm.toEquiv
      contMDiff_toFun := rawMetricIsothermalUp_contMDiff R hreg g
      contMDiff_invFun := rawMetricIsothermalDown_contMDiff R hreg g }

@[simp]
theorem rawMetricIsothermalMarking_toHomeomorph (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) :
    (rawMetricIsothermalMarking R hreg g).toHomeomorph =
      (Homeomorph.ulift : ULift.{0} X ≃ₜ X).symm := rfl

/-- Every old source chart and every actual new chart see a positive real
Jacobian. The sign is proved from the actual plane solution and the original
holomorphic transition, without supplying an orientation premise. -/
theorem rawMetricIsothermalMarking_preservesComplexOrientation (R : RiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R) :
    PreservesComplexOrientation R.toRiemannAtlas
      (rawMetricIsothermalSurface R hreg g).toRiemannAtlas
      (rawMetricIsothermalMarking R hreg g).toHomeomorph := by
  intro d hd c hc z hz
  obtain ⟨j, rfl⟩ := (rawMetricIsothermalAtlas_mem_iff R hreg g c).mp hc
  let P := RawMetricIsothermalPatch.atPoint hreg g j
  let T : OpenPartialHomeomorph ℂ ℂ := d.symm.trans P.oldChart.val
  have hC := hz.2
  change d.symm z ∈ P.chart.source at hC
  rw [P.chart_source] at hC
  have hzT : z ∈ T.source := by
    change z ∈ d.target ∩ d.symm ⁻¹' P.oldChart.val.source
    exact ⟨hz.1, hC.1⟩
  have hTC : DifferentiableAt ℂ (T : ℂ → ℂ) z :=
    (R.compatible d hd P.oldChart.val P.oldChart.property z hzT).differentiableAt
  have hTR : DifferentiableAt ℝ (T : ℂ → ℂ) z := hTC.restrictScalars ℝ
  have hTpos : 0 < realJacobian (T : ℂ → ℂ) z := by
    rw [realJacobian_eq_norm_deriv_sq hTC]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
      (R.toRiemannAtlas.transition_deriv_ne_zero d P.oldChart.val hd
        P.oldChart.property z hzT))
  have hw : DifferentiableAt ℝ (P.coordinate : ℂ → ℂ) (T z) :=
    P.coordinate_contDiff.differentiable (by simp) (T z)
  have hwpos : 0 < realJacobian (P.coordinate : ℂ → ℂ) (T z) := by
    unfold realJacobian
    rw [LiZhongQC.det_fderiv_eq_jacobian hw]
    exact P.jacobian_pos (T z)
  have hJac : realJacobian ((P.coordinate : ℂ → ℂ) ∘ T) z =
      realJacobian (P.coordinate : ℂ → ℂ) (T z) * realJacobian (T : ℂ → ℂ) z := by
    unfold realJacobian
    rw [fderiv_comp z hw hTR]
    exact LinearMap.det_comp _ _
  change 0 < realJacobian ((P.coordinate : ℂ → ℂ) ∘ T) z
  rw [hJac]
  exact mul_pos hwpos hTpos

/-- An original closed reference and every one of its raw smooth metrics
produce the actual positively oriented smooth marked target. -/
def rawMetricMarkedRiemannSurface (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R.toRiemannSurface) : MarkedRiemannSurface.{u, u} R where
  carrier := ULift.{0} X
  topology := inferInstance
  surface := rawMetricIsothermalClosedSurface R hreg g
  marking := rawMetricIsothermalMarking R.toRiemannSurface hreg g
  orientation_preserving :=
    rawMetricIsothermalMarking_preservesComplexOrientation R.toRiemannSurface hreg g

@[simp]
theorem rawMetricMarkedRiemannSurface_marking_apply (R : ClosedRiemannSurface X)
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    (g : SmoothSurfaceMetric R.toRiemannSurface) (x : X) :
    (rawMetricMarkedRiemannSurface R hreg g).marking.toHomeomorph x = ULift.up x := rfl

end LowDimensionalTopology.Geometry.Teichmuller
