module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalTensorL2Integrability
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricAreaFullSupport
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Original conformal directions are orthogonal exactly to trace-free tensors

Every test is an actual smooth scalar times the same original metric. The
native trace is proved smooth by its finite original-chart Gram expression,
so testing by that trace uses an actual member of the original test space.
The chosen metric-area measure is unchanged throughout.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- Contracting against the actual conformal direction ψg is ψ times the
ordinary trace of the original tensor raised by the same metric. -/
theorem metricTensorPointwisePairing_conformalScale
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (h : SmoothSymmetricTwoTensor R) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ (ψ : C^∞⟮𝓘(ℝ, ℂ), X; ℝ⟯) (x : X),
      metricTensorPointwisePairing R g h
          (conformalScaleLinear (R := R) g ψ) x =
        ψ x * metricTensorTrace R g h x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ∀ (ψ : C^∞⟮𝓘(ℝ, ℂ), X; ℝ⟯) (x : X),
    metricTensorPointwisePairing R g h (conformalScaleLinear (R := R) g ψ) x =
      ψ x * metricTensorTrace R g h x
  intro ψ x
  let V := TangentSpace 𝓘(ℝ, ℂ) x
  have hr : metricRaisedTensor R g (conformalScaleLinear (R := R) g ψ) x =
      ψ x • (LinearMap.id : V →ₗ[ℝ] V) := by
    apply LinearMap.ext
    intro v
    apply sub_eq_zero.mp
    apply (metricForm_nondegenerate R g x).1
    intro w
    change g.inner x
      (metricRaisedTensor R g (conformalScaleLinear (R := R) g ψ) x v - ψ x • v) w = 0
    rw [map_sub, sub_apply, map_smul, smul_apply]
    have hs := metricRaisedTensor_spec R g (conformalScaleLinear (R := R) g ψ) x v w
    change g.inner x
      (metricRaisedTensor R g (conformalScaleLinear (R := R) g ψ) x v) w =
        ψ x * g.inner x v w at hs
    change g.inner x
      (metricRaisedTensor R g (conformalScaleLinear (R := R) g ψ) x v) w -
        ψ x * g.inner x v w = 0
    exact sub_eq_zero.mpr hs
  change LinearMap.trace ℝ V
      ((metricRaisedTensor R g h x).comp
        (metricRaisedTensor R g (conformalScaleLinear (R := R) g ψ) x)) =
    ψ x * LinearMap.trace ℝ V (metricRaisedTensor R g h x)
  rw [hr, LinearMap.comp_smul, LinearMap.comp_id]
  simpa only [smul_eq_mul] using
    (map_smul (LinearMap.trace ℝ V) (ψ x) (metricRaisedTensor R g h x))

private theorem original_metric_gram_det_ne_zero
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

private theorem metricTensorTrace_in_original_chart
    (g : SmoothSurfaceMetric R.toRiemannSurface) (h : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) (hx : x ∈ e.val.source) :
    let b : Fin 2 → ℂ := Complex.basisOneI
    let G : Matrix (Fin 2) (Fin 2) ℝ :=
      fun i j => metricGramInChart g e x (b i) (b j)
    let H : Matrix (Fin 2) (Fin 2) ℝ :=
      fun i j => symmetricTensorGramInChart R h e x (b i) (b j)
    metricTensorTrace R g h x =
      (G 0 0 * G 1 1 - G 0 1 * G 1 0)⁻¹ *
        (G 1 1 * H 0 0 - G 0 1 * H 1 0 - G 1 0 * H 0 1 + G 0 0 * H 1 1) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let b : Fin 2 → ℂ := Complex.basisOneI
  let G : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => metricGramInChart g e x (b i) (b j)
  let H : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => symmetricTensorGramInChart R h e x (b i) (b j)
  let ψ : C^∞⟮𝓘(ℝ, ℂ), X; ℝ⟯ := ⟨fun _ => 1, contMDiff_const⟩
  let k : SmoothSymmetricTwoTensor R := conformalScaleLinear (R := R) g ψ
  let K : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => symmetricTensorGramInChart R k e x (b i) (b j)
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  have hK : K = G := by
    ext i j
    change symmetricTensorGramInChart R k e x (b i) (b j) =
      metricGramInChart g e x (b i) (b j)
    rw [symmetricTensorGramInChart_eq R k e x hx, metricGramInChart_eq g e x hx]
    change (1 : ℝ) * g.inner x (D.symm (b i)) (D.symm (b j)) =
      g.inner x (D.symm (b i)) (D.symm (b j))
    exact one_mul _
  have hp := metricTensorPointwisePairing_conformalScale R g h ψ x
  change metricTensorPointwisePairing R g h k x = 1 * metricTensorTrace R g h x at hp
  rw [one_mul] at hp
  have hm := metricTensorPointwisePairing_matrix_in_original_chart R g h k e x hx
  change metricTensorPointwisePairing R g h k x =
    Matrix.trace ((G⁻¹ * H) * (G⁻¹ * K)) at hm
  have hd : IsUnit G.det :=
    isUnit_iff_ne_zero.mpr (original_metric_gram_det_ne_zero R g e x hx)
  rw [hp, hK, Matrix.nonsing_inv_mul G hd, Matrix.mul_one] at hm
  change metricTensorTrace R g h x =
    (G 0 0 * G 1 1 - G 0 1 * G 1 0)⁻¹ *
      (G 1 1 * H 0 0 - G 0 1 * H 1 0 - G 1 0 * H 0 1 + G 0 0 * H 1 1)
  rw [hm, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two,
    Matrix.det_fin_two]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The ordinary trace raised by any original smooth positive metric is an
actual infinitely smooth scalar on the same original surface. -/
theorem contMDiff_metricTensorTrace
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (h : SmoothSymmetricTwoTensor R) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (metricTensorTrace R g h) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (metricTensorTrace R g h)
  intro x
  let e : OriginalComplexChart R.toRiemannSurface := ⟨chartAt ℂ x, chart_mem_atlas ℂ x⟩
  have hx : x ∈ e.val.source := mem_chart_source ℂ x
  let b : Fin 2 → ℂ := Complex.basisOneI
  let G : X → Matrix (Fin 2) (Fin 2) ℝ :=
    fun y i j => metricGramInChart g e y (b i) (b j)
  let H : X → Matrix (Fin 2) (Fin 2) ℝ :=
    fun y i j => symmetricTensorGramInChart R h e y (b i) (b j)
  have hG (i j : Fin 2) : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞
      (fun y => G y i j) x := by
    have hc := ((metricGramInChart_contMDiffOn g e).clm_apply
      (contMDiffOn_const (c := b i))).clm_apply (contMDiffOn_const (c := b j))
    exact (hc x hx).contMDiffAt (e.val.open_source.mem_nhds hx)
  have hH (i j : Fin 2) : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞
      (fun y => H y i j) x := by
    have hc := ((symmetricTensorGramInChart_contMDiffOn R h e).clm_apply
      (contMDiffOn_const (c := b i))).clm_apply (contMDiffOn_const (c := b j))
    exact (hc x hx).contMDiffAt (e.val.open_source.mem_nhds hx)
  have hd := original_metric_gram_det_ne_zero R g e x hx
  change (G x).det ≠ 0 at hd
  rw [Matrix.det_fin_two] at hd
  have hden := ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have hnum := ((((hG 1 1).mul (hH 0 0)).sub
    ((hG 0 1).mul (hH 1 0))).sub ((hG 1 0).mul (hH 0 1))).add
      ((hG 0 0).mul (hH 1 1))
  have hf := (hden.inv₀ hd).mul hnum
  apply hf.congr_of_eventuallyEq
  filter_upwards [e.val.open_source.mem_nhds hx] with y hy
  exact metricTensorTrace_in_original_chart R g h e y hy

/-- Orthogonality to every actual original smooth conformal direction is
equivalent to vanishing of the entire original metric trace. -/
theorem metricTensorL2Pairing_conformalScale_eq_zero_iff
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R g)
    (h : SmoothSymmetricTwoTensor R) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (∀ ψ : C^∞⟮𝓘(ℝ, ℂ), X; ℝ⟯,
      metricTensorL2Pairing R g harea h (conformalScaleLinear (R := R) g ψ) = 0) ↔
      ∀ x : X, metricTensorTrace R g h x = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let μ : Measure X := harea.exists.choose
  let : Measure.IsOpenPosMeasure μ := originalMetricArea_isOpenPosMeasure R g harea
  change (∀ ψ : C^∞⟮𝓘(ℝ, ℂ), X; ℝ⟯,
    metricTensorL2Pairing R g harea h (conformalScaleLinear (R := R) g ψ) = 0) ↔
      ∀ x : X, metricTensorTrace R g h x = 0
  constructor
  · intro hall
    have ht := contMDiff_metricTensorTrace R g h
    let ψ : C^∞⟮𝓘(ℝ, ℂ), X; ℝ⟯ := ⟨metricTensorTrace R g h, ht⟩
    have heq (x : X) : metricTensorPointwisePairing R g h
        (conformalScaleLinear (R := R) g ψ) x = (metricTensorTrace R g h x) ^ 2 := by
      rw [metricTensorPointwisePairing_conformalScale R g h ψ x]
      change metricTensorTrace R g h x * metricTensorTrace R g h x =
        (metricTensorTrace R g h x) ^ 2
      exact (pow_two _).symm
    have hF : metricTensorPointwisePairing R g h
        (conformalScaleLinear (R := R) g ψ) =
          (fun x => (metricTensorTrace R g h x) ^ 2) := funext heq
    have hi : Integrable (fun x => (metricTensorTrace R g h x) ^ 2) μ := by
      simpa only [hF] using integrable_metricTensorPointwisePairing R g harea h
        (conformalScaleLinear (R := R) g ψ)
    have hzero : (∫ x, (metricTensorTrace R g h x) ^ 2 ∂μ) = 0 := by
      have hz := hall ψ
      change (∫ x, metricTensorPointwisePairing R g h
        (conformalScaleLinear (R := R) g ψ) x ∂μ) = 0 at hz
      simpa only [hF] using hz
    have hae : (fun x => (metricTensorTrace R g h x) ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hi).mp hzero
    have hc : Continuous (fun x => (metricTensorTrace R g h x) ^ 2) := ht.continuous.pow 2
    have hpoint : (fun x => (metricTensorTrace R g h x) ^ 2) = 0 :=
      (hc.ae_eq_iff_eq μ continuous_zero).mp hae
    intro x
    have hz := congrFun hpoint x
    change (metricTensorTrace R g h x) ^ 2 = (0 : ℝ) at hz
    nlinarith
  · intro htrace ψ
    change (∫ x, metricTensorPointwisePairing R g h
      (conformalScaleLinear (R := R) g ψ) x ∂μ) = 0
    have heq : metricTensorPointwisePairing R g h
        (conformalScaleLinear (R := R) g ψ) = 0 := by
      funext x
      change metricTensorPointwisePairing R g h
        (conformalScaleLinear (R := R) g ψ) x = (0 : ℝ)
      rw [metricTensorPointwisePairing_conformalScale R g h ψ x, htrace x, mul_zero]
    rw [heq]
    exact integral_zero' X ℝ

end LowDimensionalTopology.Geometry.Teichmuller
