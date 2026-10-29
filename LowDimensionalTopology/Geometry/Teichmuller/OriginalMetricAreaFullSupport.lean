module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Positive mass of original open sets for the prescribed metric area

The measure is exactly the one already selected by the area premise. In a
valid preferred original chart its actual positive Gram density bounds a
positive constant on a small complex ball. The original map law transfers
this mass back to the original open set.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology MeasureTheory Metric
open scoped Manifold ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u

/-- The same prescribed original metric area assigns positive mass to every
nonempty original open set. No additional support hypothesis is needed. -/
theorem originalMetricArea_isOpenPosMeasure
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R g) :
    letI : MeasurableSpace X := borel X
    let μ : Measure X := harea.exists.choose
    Measure.IsOpenPosMeasure μ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let μ : Measure X := harea.exists.choose
  change Measure.IsOpenPosMeasure μ
  constructor
  intro U hU hUne hμU
  obtain ⟨x, hxU⟩ := hUne
  let e : OriginalComplexChart R.toRiemannSurface := ⟨chartAt ℂ x, chart_mem_atlas ℂ x⟩
  have hx : x ∈ e.val.source := mem_chart_source ℂ x
  let z : ℂ := e.val x
  have hz : z ∈ e.val.target := e.val.map_source hx
  let W : Set ℂ := e.val '' (e.val.source ∩ U)
  have hW : IsOpen W := e.val.isOpen_image_source_inter hU
  have hzW : z ∈ W := ⟨x, ⟨hx, hxU⟩, rfl⟩
  have hWt : W ⊆ e.val.target := by
    rintro w ⟨y, hy, rfl⟩
    exact e.val.map_source hy.1
  let B : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    fun w => metricGramInChart g e (e.val.symm w)
  let rho : ℂ → ℝ := fun w => Real.sqrt
    (B w 1 1 * B w Complex.I Complex.I - (B w 1 Complex.I) ^ 2)
  let ν : Measure ℂ := (volume : Measure ℂ).withDensity (fun w => ENNReal.ofReal (rho w))
  have hmap : Measure.map (e.val : X → ℂ) (μ.restrict e.val.source) =
      ν.restrict e.val.target := harea.exists.choose_spec.2 x
  have hmeas : AEMeasurable (e.val : X → ℂ) (μ.restrict e.val.source) :=
    e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  have hpre : (e.val ⁻¹' W) ∩ e.val.source ⊆ U := by
    rintro y ⟨⟨y', hy', hyy'⟩, hy⟩
    have hsame : y' = y := e.val.injOn hy'.1 hy hyy'
    exact hsame ▸ hy'.2
  have hzeroMap : Measure.map (e.val : X → ℂ) (μ.restrict e.val.source) W = 0 := by
    rw [Measure.map_apply_of_aemeasurable hmeas hW.measurableSet,
      Measure.restrict_apply' e.val.open_source.measurableSet]
    exact measure_mono_null hpre hμU
  have hzeroν : ν W = 0 := by
    rw [hmap, Measure.restrict_apply' e.val.open_target.measurableSet] at hzeroMap
    simpa only [Set.inter_eq_left.mpr hWt] using hzeroMap
  have hg : ContinuousAt (metricGramInChart g e) x :=
    (metricGramInChart_contMDiffOn g e).continuousOn.continuousAt
      (e.val.open_source.mem_nhds hx)
  have hg' : ContinuousAt (metricGramInChart g e) (e.val.symm z) := by
    simpa only [z, e.val.left_inv hx] using hg
  have hinv : ContinuousAt (e.val.symm : ℂ → X) z :=
    e.val.symm.continuousOn.continuousAt (e.val.open_target.mem_nhds hz)
  have hB : ContinuousAt B z := hg'.comp hinv
  have hc (a b : ℂ) : ContinuousAt (fun w => B w a b) z :=
    (hB.clm_apply (continuousAt_const (y := a))).clm_apply (continuousAt_const (y := b))
  have hrho : ContinuousAt rho z :=
    Real.continuous_sqrt.continuousAt.comp
      (((hc 1 1).mul (hc Complex.I Complex.I)).sub ((hc 1 Complex.I).pow 2))
  have hBz : B z = metricGramForm g e x hx := by
    dsimp only [B, z]
    rw [e.val.left_inv hx, metricGramInChart_eq g e x hx]
  have hdet : 0 < B z 1 1 * B z Complex.I Complex.I - (B z 1 Complex.I) ^ 2 := by
    rw [hBz]
    exact (metricGram_positive g e x hx).2.2
  have hpos : 0 < rho z := Real.sqrt_pos.mpr hdet
  have hhalf : rho z / 2 < rho z := half_lt_self hpos
  have hlower : ∀ᶠ w in 𝓝 z, rho z / 2 < rho w :=
    hrho.eventually (isOpen_Ioi.mem_nhds hhalf)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hW.mem_nhds hzW) hlower)
  have hball0 : ν (ball z r) = 0 :=
    measure_mono_null (fun w hw => (hrsub hw).1) hzeroν
  have hv : (volume : Measure ℂ) (ball z r) ≠ 0 :=
    isOpen_ball.measure_ne_zero volume ⟨z, mem_ball_self hr⟩
  have hbound : ENNReal.ofReal (rho z / 2) * (volume : Measure ℂ) (ball z r) ≤
      ν (ball z r) := by
    change ENNReal.ofReal (rho z / 2) * (volume : Measure ℂ) (ball z r) ≤
      (volume : Measure ℂ).withDensity (fun w => ENNReal.ofReal (rho w)) (ball z r)
    rw [withDensity_apply _ measurableSet_ball, ← setLIntegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact ENNReal.ofReal_le_ofReal (le_of_lt (hrsub hw).2)
  have hnonzero : ENNReal.ofReal (rho z / 2) * (volume : Measure ℂ) (ball z r) ≠ 0 :=
    mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr (half_pos hpos))) hv
  apply hnonzero
  exact le_antisymm (by simpa only [hball0] using hbound) bot_le

end LowDimensionalTopology.Geometry.Teichmuller
