module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalLocalTensorHolomorphicCoefficient
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicQuadraticDifferential

/-!
# The native quadratic coefficient family of a trace-free divergence-free tensor

Coefficients are taken from the same original tensor in the preferred original
charts and are explicitly zero outside their targets. The transition law is
proved by comparing that tensor on two pairs of actual tangent vectors. The
result packages the existing holomorphic quadratic differential subtype.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Filter Set Topology
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

private def original_tensor_coefficient (h : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) : ℂ :=
  (symmetricTensorGramInChart R h e x 1 1 : ℂ) -
    Complex.I * (symmetricTensorGramInChart R h e x 1 Complex.I : ℂ)

private theorem original_tt_chart_reconstruct
    (G : AtlasInducedMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (h : SmoothSymmetricTwoTensor R)
    (htrace : ∀ x : X, metricTensorTrace R G.metric h x = 0)
    (hzero : letI := R.toRiemannAtlas.toChartedSpace
      letI := R.toRiemannAtlas.isRealManifold
      ∀ x : X, (metricTensorDivergence R G.metric hdiv h).toFun x = 0)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) (hx : x ∈ e.val.source) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
    ∀ (v w : RealSurfaceTangent R.toRiemannSurface x),
      h.val.toFun x v w = (original_tensor_coefficient R h e x * D v * D w).re := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  have ht : ∀ᶠ w in 𝓝 (e.val x),
      metricTensorTrace R G.metric h (e.val.symm w) = 0 :=
    Filter.Eventually.of_forall (fun w => htrace (e.val.symm w))
  have hs := (differentiableAt_native_tracefree_coefficient R G hdiv h e (e.val x)
    (e.val.map_source hx) ht (hzero (e.val.symm (e.val x)))).2
  let P (y : X) : Prop :=
    ∀ (v w : RealSurfaceTangent R.toRiemannSurface y),
      h.val.toFun y v w = (original_tensor_coefficient R h e y *
        originalChartDifferential R.toRiemannSurface e y v *
        originalChartDifferential R.toRiemannSurface e y w).re
  have hsP : P (e.val.symm (e.val x)) := by
    simpa only [P, original_tensor_coefficient,
      SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply] using hs
  have hxP : P x := (e.val.left_inv hx) ▸ hsP
  simpa only [P, SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply] using hxP

private theorem original_chart_deriv_intertwines
    (e f : OriginalComplexChart R.toRiemannSurface) (x : X)
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source)
    (v : RealSurfaceTangent R.toRiemannSurface x) :
    originalChartDifferential R.toRiemannSurface f x v =
      deriv (e.val.symm.trans f.val) (e.val x) *
        originalChartDifferential R.toRiemannSurface e x v := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let T : ℂ → ℂ := e.val.symm.trans f.val
  have hz : e.val x ∈ (e.val.symm.trans f.val).source := by
    refine ⟨e.val.map_source he, ?_⟩
    simpa only [Set.mem_preimage, OpenPartialHomeomorph.symm_symm,
      e.val.left_inv he] using hf
  have ht : DifferentiableAt ℂ T (e.val x) :=
    (R.toRiemannAtlas.compatible e.val e.property f.val f.property (e.val x) hz).differentiableAt
  have hh := (SmoothSurfaceEquiv.refl R.toRiemannSurface).chartDifferential_intertwines
    e f x he hf v
  change fderiv ℝ T (e.val x) (originalChartDifferential R.toRiemannSurface e x v) =
    originalChartDifferential R.toRiemannSurface f x
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (id : X → X) x v) at hh
  simp only [mfderiv_id, ContinuousLinearMap.id_apply] at hh
  rw [ht.fderiv_restrictScalars ℝ] at hh
  change fderiv ℂ T (e.val x) (originalChartDifferential R.toRiemannSurface e x v) =
    originalChartDifferential R.toRiemannSurface f x v at hh
  rw [fderiv_eq_deriv_mul] at hh
  exact hh.symm

private theorem original_tensor_coefficient_change
    (G : AtlasInducedMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (h : SmoothSymmetricTwoTensor R)
    (htrace : ∀ x : X, metricTensorTrace R G.metric h x = 0)
    (hzero : letI := R.toRiemannAtlas.toChartedSpace
      letI := R.toRiemannAtlas.isRealManifold
      ∀ x : X, (metricTensorDivergence R G.metric hdiv h).toFun x = 0)
    (e f : OriginalComplexChart R.toRiemannSurface) (x : X)
    (he : x ∈ e.val.source) (hf : x ∈ f.val.source) :
    original_tensor_coefficient R h e x =
      original_tensor_coefficient R h f x * deriv (e.val.symm.trans f.val) (e.val x) ^ 2 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x he
  let E := SmoothSurfaceEquiv.originalChartDifferentialEquiv f x hf
  let a := original_tensor_coefficient R h e x
  let b := original_tensor_coefficient R h f x
  let t := deriv (e.val.symm.trans f.val) (e.val x)
  have heq := original_tt_chart_reconstruct R G hdiv h htrace hzero e x he
  have hfq := original_tt_chart_reconstruct R G hdiv h htrace hzero f x hf
  change ∀ (v w : RealSurfaceTangent R.toRiemannSurface x),
    h.val.toFun x v w = (a * D v * D w).re at heq
  change ∀ (v w : RealSurfaceTangent R.toRiemannSurface x),
    h.val.toFun x v w = (b * E v * E w).re at hfq
  have hD (v : RealSurfaceTangent R.toRiemannSurface x) : E v = t * D v :=
    original_chart_deriv_intertwines R e f x he hf v
  have hr : a.re = (b * t * t).re := by
    calc
      a.re = h.val.toFun x (D.symm 1) (D.symm 1) := by
        simpa only [D.apply_symm_apply, mul_one] using (heq (D.symm 1) (D.symm 1)).symm
      _ = (b * t * t).re := by
        simpa only [hD, D.apply_symm_apply, mul_one] using hfq (D.symm 1) (D.symm 1)
  have hi : (a * Complex.I).re = (b * t * (t * Complex.I)).re := by
    calc
      (a * Complex.I).re = h.val.toFun x (D.symm 1) (D.symm Complex.I) := by
        simpa only [D.apply_symm_apply, mul_one] using
          (heq (D.symm 1) (D.symm Complex.I)).symm
      _ = (b * t * (t * Complex.I)).re := by
        simpa only [hD, D.apply_symm_apply, mul_one] using hfq (D.symm 1) (D.symm Complex.I)
  change a = b * t ^ 2
  apply Complex.ext
  · simpa only [pow_two, mul_assoc] using hr
  · have hs : (a * Complex.I).re = ((b * t ^ 2) * Complex.I).re := by
      simpa only [pow_two, mul_assoc] using hi
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub] at hs
    linarith [hs]

open scoped Classical in
/-- Native trace and divergence zero produce the actual global quadratic
family, including its overlap law and reconstruction on all native slots. -/
theorem native_tt_quadratic_coefficient_family
    (G : AtlasInducedMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (h : SmoothSymmetricTwoTensor R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    let coefficient : X → ℂ → ℂ := fun p z =>
      let e : OriginalComplexChart R.toRiemannSurface :=
        ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
      if z ∈ e.val.target then
        (symmetricTensorGramInChart R h e (e.val.symm z) 1 1 : ℂ) -
          Complex.I * (symmetricTensorGramInChart R h e (e.val.symm z) 1 Complex.I : ℂ)
      else 0
    (∀ x : X, metricTensorTrace R G.metric h x = 0) →
    (∀ x : X, (metricTensorDivergence R G.metric hdiv h).toFun x = 0) →
      (∀ p z, z ∉ (chartAt ℂ p).target → coefficient p z = 0) ∧
      (∀ p q : X, ∀ z ∈ (chartAt ℂ q).target,
        (chartAt ℂ q).symm z ∈ (chartAt ℂ p).source →
          coefficient q z =
            coefficient p (LiZhongQC.chartTransition p q z) *
              deriv (LiZhongQC.chartTransition p q) z ^ 2) ∧
      (∀ p : X, DifferentiableOn ℂ (coefficient p) (chartAt ℂ p).target) ∧
      (∃ Q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
        Q.val = coefficient ∧
        ∀ (p : X) (z : ℂ) (hz : z ∈ (chartAt ℂ p).target),
          let e : OriginalComplexChart R.toRiemannSurface :=
            ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
          let x := e.val.symm z
          let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x
            (e.val.map_target hz)
          ∀ (v w : RealSurfaceTangent R.toRiemannSurface x),
            h.val.toFun x v w = (Q.val p z * D v * D w).re) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let coefficient : X → ℂ → ℂ := fun p z =>
    let e : OriginalComplexChart R.toRiemannSurface :=
      ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
    if z ∈ e.val.target then original_tensor_coefficient R h e (e.val.symm z) else 0
  dsimp only
  intro htrace hzero
  change (∀ p z, z ∉ (chartAt ℂ p).target → coefficient p z = 0) ∧
    (∀ p q : X, ∀ z ∈ (chartAt ℂ q).target,
      (chartAt ℂ q).symm z ∈ (chartAt ℂ p).source →
        coefficient q z = coefficient p (LiZhongQC.chartTransition p q z) *
          deriv (LiZhongQC.chartTransition p q) z ^ 2) ∧
    (∀ p : X, DifferentiableOn ℂ (coefficient p) (chartAt ℂ p).target) ∧
    (∃ Q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
      Q.val = coefficient ∧
      ∀ (p : X) (z : ℂ) (hz : z ∈ (chartAt ℂ p).target),
        let e : OriginalComplexChart R.toRiemannSurface :=
          ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
        let x := e.val.symm z
        let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x
          (e.val.map_target hz)
        ∀ (v w : RealSurfaceTangent R.toRiemannSurface x),
          h.val.toFun x v w = (Q.val p z * D v * D w).re)
  have hoff : ∀ p z, z ∉ (chartAt ℂ p).target → coefficient p z = 0 := by
    intro p z hz
    simp only [coefficient, ite_eq_right hz]
  have hoverlap : ∀ p q : X, ∀ z ∈ (chartAt ℂ q).target,
      (chartAt ℂ q).symm z ∈ (chartAt ℂ p).source →
        coefficient q z = coefficient p (LiZhongQC.chartTransition p q z) *
          deriv (LiZhongQC.chartTransition p q) z ^ 2 := by
    intro p q z hz hs
    let e : OriginalComplexChart R.toRiemannSurface := ⟨chartAt ℂ q, chart_mem_atlas ℂ q⟩
    let f : OriginalComplexChart R.toRiemannSurface := ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
    let x := e.val.symm z
    have he : x ∈ e.val.source := e.val.map_target hz
    have hf : x ∈ f.val.source := hs
    have ht : LiZhongQC.chartTransition p q z = f.val x := rfl
    have htarget : LiZhongQC.chartTransition p q z ∈ f.val.target := by
      rw [ht]
      exact f.val.map_source hf
    have hx : f.val.symm (LiZhongQC.chartTransition p q z) = x := by
      rw [ht]
      exact f.val.left_inv hf
    have hez : e.val x = z := e.val.right_inv hz
    change (if z ∈ e.val.target then original_tensor_coefficient R h e (e.val.symm z) else 0) =
      (if LiZhongQC.chartTransition p q z ∈ f.val.target then
        original_tensor_coefficient R h f (f.val.symm (LiZhongQC.chartTransition p q z)) else 0) *
        deriv (LiZhongQC.chartTransition p q) z ^ 2
    rw [ite_eq_left hz, ite_eq_left htarget, hx]
    have hc := original_tensor_coefficient_change R G hdiv h htrace hzero e f x he hf
    change original_tensor_coefficient R h e x =
      original_tensor_coefficient R h f x * deriv (LiZhongQC.chartTransition p q) z ^ 2
    have htransition : (e.val.symm.trans f.val : ℂ → ℂ) =
        LiZhongQC.chartTransition p q := rfl
    rw [htransition, hez] at hc
    exact hc
  have hhol : ∀ p : X, DifferentiableOn ℂ (coefficient p) (chartAt ℂ p).target := by
    intro p z hz
    let e : OriginalComplexChart R.toRiemannSurface := ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
    have ht : ∀ᶠ w in 𝓝 z, metricTensorTrace R G.metric h (e.val.symm w) = 0 :=
      Filter.Eventually.of_forall (fun w => htrace (e.val.symm w))
    have hl := (differentiableAt_native_tracefree_coefficient R G hdiv h e z hz ht
      (hzero (e.val.symm z))).1
    have hnear : coefficient p =ᶠ[𝓝 z]
        (fun w => original_tensor_coefficient R h e (e.val.symm w)) := by
      filter_upwards [e.val.open_target.mem_nhds hz] with w hw
      change (if w ∈ e.val.target then original_tensor_coefficient R h e (e.val.symm w) else 0) = _
      exact ite_eq_left hw
    exact (hl.congr_of_eventuallyEq hnear).differentiableWithinAt
  have hrepr : ∀ (p : X) (z : ℂ) (hz : z ∈ (chartAt ℂ p).target),
      let e : OriginalComplexChart R.toRiemannSurface :=
        ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
      let x := e.val.symm z
      let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x (e.val.map_target hz)
      ∀ (v w : RealSurfaceTangent R.toRiemannSurface x),
        h.val.toFun x v w = (coefficient p z * D v * D w).re := by
    intro p z hz
    let e : OriginalComplexChart R.toRiemannSurface := ⟨chartAt ℂ p, chart_mem_atlas ℂ p⟩
    let x := e.val.symm z
    have hx : x ∈ e.val.source := e.val.map_target hz
    have hc : coefficient p z = original_tensor_coefficient R h e x := ite_eq_left hz
    simpa only [hc] using original_tt_chart_reconstruct R G hdiv h htrace hzero e x hx
  have hfamily : LiZhongQC.IsDiffFamily 2 0 coefficient := by
    refine ⟨hoff, ?_⟩
    intro p q z hz hs
    simpa only [zpow_ofNat, pow_zero, mul_one] using hoverlap p q z hz hs
  refine ⟨hoff, hoverlap, hhol, ?_⟩
  refine ⟨⟨coefficient, ?_⟩, rfl, hrepr⟩
  change LiZhongQC.IsDiffFamily 2 0 coefficient ∧
    ∀ p : X, DifferentiableOn ℂ (coefficient p) (chartAt ℂ p).target
  exact ⟨hfamily, hhol⟩

end LowDimensionalTopology.Geometry.Teichmuller
