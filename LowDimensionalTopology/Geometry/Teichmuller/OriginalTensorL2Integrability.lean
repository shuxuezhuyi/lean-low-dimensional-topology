module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalTensorL2Pairing
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalSymmetricTensorGram
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrability of the original tensor contraction

The original metric-raised endomorphisms have their actual Gram matrices
in each original chart. The matrix formula proves continuity without changing
complex structure. Compactness and finiteness of the same prescribed area
measure then give integrability of the original contraction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

private theorem original_metric_matrix_det_ne_zero
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) (hx : x ∈ e.val.source) :
    let b : Fin 2 → ℂ := Complex.basisOneI
    let G : Matrix (Fin 2) (Fin 2) ℝ :=
      fun i j => metricGramInChart g e x (b i) (b j)
    G.det ≠ 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  let B := Complex.basisOneI.map D.symm.toLinearEquiv
  let G : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => metricGramInChart g e x (Complex.basisOneI i) (Complex.basisOneI j)
  have hG : LinearMap.BilinForm.toMatrix B (g.inner x).toLinearMap₁₂ = G := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    change g.inner x (D.symm (Complex.basisOneI i)) (D.symm (Complex.basisOneI j)) =
      metricGramInChart g e x (Complex.basisOneI i) (Complex.basisOneI j)
    simp only [metricGramInChart_eq g e x hx, metricGramForm,
      ContinuousLinearMap.bilinearComp_apply, D, ContinuousLinearEquiv.coe_coe]
  have hd := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero B).mp
    (metricForm_nondegenerate R g x)
  change G.det ≠ 0
  simpa only [hG] using hd

/-- The original metric contraction is the trace of the two actual raised
Gram matrices in the same valid original chart. -/
theorem metricTensorPointwisePairing_matrix_in_original_chart
    (g : SmoothSurfaceMetric R.toRiemannSurface) (h k : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) (hx : x ∈ e.val.source) :
    let b : Fin 2 → ℂ := Complex.basisOneI
    let G : Matrix (Fin 2) (Fin 2) ℝ :=
      fun i j => metricGramInChart g e x (b i) (b j)
    let H : Matrix (Fin 2) (Fin 2) ℝ :=
      fun i j => symmetricTensorGramInChart R h e x (b i) (b j)
    let K : Matrix (Fin 2) (Fin 2) ℝ :=
      fun i j => symmetricTensorGramInChart R k e x (b i) (b j)
    metricTensorPointwisePairing R g h k x = Matrix.trace ((G⁻¹ * H) * (G⁻¹ * K)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  let B := Complex.basisOneI.map D.symm.toLinearEquiv
  let G : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => metricGramInChart g e x (Complex.basisOneI i) (Complex.basisOneI j)
  let T (t : SmoothSymmetricTwoTensor R) : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => symmetricTensorGramInChart R t e x
      (Complex.basisOneI i) (Complex.basisOneI j)
  have hG : LinearMap.BilinForm.toMatrix B (g.inner x).toLinearMap₁₂ = G := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    change g.inner x (D.symm (Complex.basisOneI i)) (D.symm (Complex.basisOneI j)) =
      metricGramInChart g e x (Complex.basisOneI i) (Complex.basisOneI j)
    simp only [metricGramInChart_eq g e x hx, metricGramForm,
      ContinuousLinearMap.bilinearComp_apply, D, ContinuousLinearEquiv.coe_coe]
  have hT (t : SmoothSymmetricTwoTensor R) :
      LinearMap.BilinForm.toMatrix B (t.val.toFun x).toLinearMap₁₂ = T t := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    change t.val.toFun x (D.symm (Complex.basisOneI i)) (D.symm (Complex.basisOneI j)) =
      symmetricTensorGramInChart R t e x (Complex.basisOneI i) (Complex.basisOneI j)
    simp only [symmetricTensorGramInChart_eq R t e x hx, symmetricTensorGramForm,
      ContinuousLinearMap.bilinearComp_apply, D, ContinuousLinearEquiv.coe_coe]
  have hdet : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (original_metric_matrix_det_ne_zero R g e x hx)
  have hraised (t : SmoothSymmetricTwoTensor R) :
      LinearMap.toMatrix B B (metricRaisedTensor R g t x) = G⁻¹ * T t := by
    have hs := t.property
    change ∀ (y : X) (v w : RealSurfaceTangent R.toRiemannSurface y),
      t.val.toFun y v w = t.val.toFun y w v at hs
    have heq : LinearMap.BilinForm.compRight (g.inner x).toLinearMap₁₂
        (metricRaisedTensor R g t x) = (t.val.toFun x).toLinearMap₁₂ := by
      ext v w
      change g.inner x v (metricRaisedTensor R g t x w) = t.val.toFun x v w
      rw [g.symm x v (metricRaisedTensor R g t x w), metricRaisedTensor_spec]
      exact hs x w v
    have hm := congrArg (LinearMap.BilinForm.toMatrix B) heq
    rw [LinearMap.BilinForm.toMatrix_compRight, hG, hT t] at hm
    calc
      LinearMap.toMatrix B B (metricRaisedTensor R g t x) =
          G⁻¹ * (G * LinearMap.toMatrix B B (metricRaisedTensor R g t x)) :=
        (Matrix.nonsing_inv_mul_cancel_left G _ hdet).symm
      _ = G⁻¹ * T t := by rw [hm]
  change LinearMap.trace ℝ (RealSurfaceTangent R.toRiemannSurface x)
    ((metricRaisedTensor R g h x).comp (metricRaisedTensor R g k x)) =
      Matrix.trace ((G⁻¹ * T h) * (G⁻¹ * T k))
  rw [LinearMap.trace_eq_matrix_trace ℝ B, LinearMap.toMatrix_comp B B B,
    hraised h, hraised k]

/-- The full contraction of two original smooth symmetric tensors is continuous
for every original smooth positive metric. -/
theorem continuous_metricTensorPointwisePairing
    (g : SmoothSurfaceMetric R.toRiemannSurface) (h k : SmoothSymmetricTwoTensor R) :
    Continuous (metricTensorPointwisePairing R g h k) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  rw [continuous_iff_continuousAt]
  intro x
  let e : OriginalComplexChart R.toRiemannSurface := ⟨chartAt ℂ x, chart_mem_atlas ℂ x⟩
  have hx : x ∈ e.val.source := mem_chart_source ℂ x
  let b : Fin 2 → ℂ := Complex.basisOneI
  let G : X → Matrix (Fin 2) (Fin 2) ℝ :=
    fun y i j => metricGramInChart g e y (b i) (b j)
  let H : X → Matrix (Fin 2) (Fin 2) ℝ :=
    fun y i j => symmetricTensorGramInChart R h e y (b i) (b j)
  let K : X → Matrix (Fin 2) (Fin 2) ℝ :=
    fun y i j => symmetricTensorGramInChart R k e y (b i) (b j)
  have hg : ContinuousAt (metricGramInChart g e) x :=
    (metricGramInChart_contMDiffOn g e).continuousOn.continuousAt
      (e.val.open_source.mem_nhds hx)
  have hG : ContinuousAt G x := by
    apply continuousAt_pi.2
    intro i
    apply continuousAt_pi.2
    intro j
    exact (hg.clm_apply (continuousAt_const (y := b i))).clm_apply
      (continuousAt_const (y := b j))
  have ht (t : SmoothSymmetricTwoTensor R) : ContinuousAt
      (fun y i j => symmetricTensorGramInChart R t e y (b i) (b j)) x := by
    have hh : ContinuousAt (symmetricTensorGramInChart R t e) x :=
      (symmetricTensorGramInChart_contMDiffOn R t e).continuousOn.continuousAt
        (e.val.open_source.mem_nhds hx)
    apply continuousAt_pi.2
    intro i
    apply continuousAt_pi.2
    intro j
    exact (hh.clm_apply (continuousAt_const (y := b i))).clm_apply
      (continuousAt_const (y := b j))
  have hH : ContinuousAt H x := ht h
  have hK : ContinuousAt K x := ht k
  have hd : (G x).det ≠ 0 := original_metric_matrix_det_ne_zero R g e x hx
  have hinv : ContinuousAt (Ring.inverse : ℝ → ℝ) (G x).det := by
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hd)
  have hI : ContinuousAt (fun y => (G y)⁻¹) x :=
    (continuousAt_matrix_inv (G x) hinv).comp hG
  have htrace : Continuous (Matrix.trace : Matrix (Fin 2) (Fin 2) ℝ → ℝ) :=
    continuous_id.matrix_trace
  have hf : ContinuousAt (fun y => Matrix.trace (((G y)⁻¹ * H y) * ((G y)⁻¹ * K y))) x :=
    htrace.continuousAt.comp ((hI.mul hH).mul (hI.mul hK))
  apply hf.congr_of_eventuallyEq
  filter_upwards [e.val.open_source.mem_nhds hx] with y hy
  exact metricTensorPointwisePairing_matrix_in_original_chart R g h k e y hy

/-- Compactness makes the original contraction integrable for the same finite
metric-area measure chosen by the explicit area existence input. -/
theorem integrable_metricTensorPointwisePairing
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R g)
    (h k : SmoothSymmetricTwoTensor R) :
    letI : MeasurableSpace X := borel X
    let μ : Measure X := harea.exists.choose
    Integrable (metricTensorPointwisePairing R g h k) μ := by
  let : MeasurableSpace X := borel X
  let : OpensMeasurableSpace X := ⟨le_rfl⟩
  let μ : Measure X := harea.exists.choose
  let : CompactSpace X := R.compactSpace
  let : IsFiniteMeasure μ := harea.exists.choose_spec.1
  change Integrable (metricTensorPointwisePairing R g h k) μ
  have hc := continuous_metricTensorPointwisePairing R g h k
  have hi : IntegrableOn (metricTensorPointwisePairing R g h k) Set.univ μ :=
    ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ hc.continuousOn
  simpa only [IntegrableOn, Measure.restrict_univ] using hi

end LowDimensionalTopology.Geometry.Teichmuller
