module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricLieProducer
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalConformalTensorTrace
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalConformalTensorOrthogonality
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalQuadraticDifferentialTensor
public import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# The pure quadratic representative of an actual metric Lie variation

Subtracting half the actual native trace times the same metric removes its
conformal part. The resulting smooth tensor has the source quadratic
coefficient on every original conformal chart, with the exact factor two.
No holomorphicity of this generally smooth coefficient is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
open scoped Manifold ContDiff BigOperators InnerProductSpace ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
namespace SmoothSurfaceMetric

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The additive group inherited from the same native symmetric-tensor submodule. -/
local instance nativeMetricLieTensorAddCommGroup : AddCommGroup (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  letI : ∀ x : X, IsTopologicalAddGroup (TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ) :=
    fun x => ContinuousLinearMap.isTopologicalAddGroup
      (E := TangentSpace 𝓘(ℝ, ℂ) x) (F := ℝ) (σ := RingHom.id ℝ)
  letI : ∀ x : X, ContinuousAdd (TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ) :=
    fun x => (ContinuousLinearMap.isTopologicalAddGroup
      (E := TangentSpace 𝓘(ℝ, ℂ) x) (F := ℝ) (σ := RingHom.id ℝ)).toContinuousAdd
  let : ∀ x : X, AddCommGroup (TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ]
      TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ) := fun _ => ContinuousLinearMap.addCommGroup
  let : ∀ x : X, Module ℝ (TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ]
      TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ) := fun _ => ContinuousLinearMap.module
  let : AddCommGroup (SmoothSurfaceTwoTensor R) := ContMDiffSection.instAddCommGroup
  let : Module ℝ (SmoothSurfaceTwoTensor R) := ContMDiffSection.instModule
  exact Submodule.addCommGroup (symmetricTwoTensorSubmodule R)

/-- Subtraction is inherited from this same canonical native tensor group. -/
local instance nativeMetricLieTensorSub : Sub (SmoothSymmetricTwoTensor R) := by
  exact (nativeMetricLieTensorAddCommGroup R).toAddGroup.toSubNegMonoid.toSub

/-- The actual smooth conformal coefficient removed from the metric Lie tensor. -/
def nativeMetricLieConformalScalar
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X) → C^∞⟮𝓘(ℝ, ℂ), X; ℝ⟯ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro V
  exact ⟨fun x => (2 : ℝ)⁻¹ * metricTensorTrace R g (nativeMetricLie R hvar g V) x,
    contMDiff_const.mul (contMDiff_metricTensorTrace R g (nativeMetricLie R hvar g V))⟩

/-- The same native Lie tensor with its actual conformal trace part removed. -/
def nativeMetricLieQuadraticPart
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X) → SmoothSymmetricTwoTensor R := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact fun V => nativeMetricLie R hvar g V - conformalScaleLinear (R := R) g
    (nativeMetricLieConformalScalar R hvar g V)

/-- The removed part lies in the existing space of all smooth conformal directions. -/
theorem nativeMetricLie_sub_quadraticPart_mem_conformal
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
      nativeMetricLie R hvar g V - nativeMetricLieQuadraticPart R hvar g V ∈
        conformalVerticalTensors (R := R) g := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro V
  refine ⟨nativeMetricLieConformalScalar R hvar g V, ?_⟩
  change conformalScaleLinear (R := R) g (nativeMetricLieConformalScalar R hvar g V) =
    nativeMetricLie R hvar g V - (nativeMetricLie R hvar g V -
      conformalScaleLinear (R := R) g (nativeMetricLieConformalScalar R hvar g V))
  exact (sub_sub_cancel _ _).symm

private theorem quadratic_lie_real_inner (a b : ℂ) :
    inner ℝ a b = a.re * b.re + a.im * b.im := by
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
  change (conj a * b).re = _
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem quadratic_lie_inverse_chart_apply
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) (hx : x ∈ e.val.source) (a : ℂ) :
    originalChartDifferential R.toRiemannSurface e x
      ((SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx).symm a) = a := by
  exact (SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply e x hx
    ((SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx).symm a)).symm.trans
      ((SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx).apply_symm_apply a)

private theorem quadratic_lie_metric_inverse_chart
    (G : AtlasInducedMetric R.toRiemannSurface)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) (hx : x ∈ e.val.source)
    (a b : ℂ) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    G.metric.inner x
      ((SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx).symm a)
      ((SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx).symm b) =
        G.density e x * inner ℝ a b := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  rw [G.inner_eq e x hx, quadratic_lie_inverse_chart_apply R e x hx a,
    quadratic_lie_inverse_chart_apply R e x hx b]

/-- The actual conformal correction leaves zero whole native trace. -/
theorem nativeMetricLieQuadraticPart_trace_zero
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (G : AtlasInducedMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ (V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X)) (x : X),
      metricTensorTrace R G.metric (nativeMetricLieQuadraticPart R hvar G.metric V) x = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro V x
  let L := nativeMetricLie R hvar G.metric V
  let P := nativeMetricLieQuadraticPart R hvar G.metric V
  let psi := nativeMetricLieConformalScalar R hvar G.metric V
  let e : OriginalComplexChart R.toRiemannSurface :=
    ⟨chartAt ℂ x, chart_mem_atlas ℂ x⟩
  have hx : x ∈ e.val.source := mem_chart_source ℂ x
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  have hmetric (a b : ℂ) :
      G.metric.inner x (D.symm a) (D.symm b) = G.density e x * inner ℝ a b :=
    quadratic_lie_metric_inverse_chart R G e x hx a b
  have htr : G.density e x * metricTensorTrace R G.metric L x =
      L.val x (D.symm 1) (D.symm 1) + L.val x (D.symm Complex.I) (D.symm Complex.I) :=
    metricTensorTrace_conformal_frame R G L e x hx
  apply (metricTensorTrace_eq_zero_iff_conformal_frame R G P e x hx).mpr
  change L.val x (D.symm Complex.I) (D.symm Complex.I) -
      psi x * G.metric.inner x (D.symm Complex.I) (D.symm Complex.I) =
    -(L.val x (D.symm 1) (D.symm 1) -
      psi x * G.metric.inner x (D.symm 1) (D.symm 1))
  rw [hmetric Complex.I Complex.I, hmetric 1 1]
  norm_num [quadratic_lie_real_inner]
  have hpsi : psi x = (2 : ℝ)⁻¹ * metricTensorTrace R G.metric L x := rfl
  rw [hpsi]
  nlinarith only [htr]

private theorem quadratic_lie_model_apply (q v w : ℂ) :
    quadraticModel q v w = (q * v * w).re := by
  change q.re * (v * w).re - q.im * (v * w).im = (q * v * w).re
  simp only [Complex.mul_re, Complex.mul_im]
  ring

set_option maxHeartbeats 800000 in
open scoped Classical in
/-- The source pure quadratic coefficient, in every original conformal chart.
The metric density is the coefficient of the metric itself. -/
theorem nativeMetricLieQuadraticPart_inOriginalChart
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (G : AtlasInducedMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ (V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X))
        (e : OriginalComplexChart R.toRiemannSurface) (z : ℂ) (hz : z ∈ e.val.target),
      let x := e.val.symm z
      let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x (e.val.map_target hz)
      let C : ℂ → Fin 2 → ℝ := fun w k =>
        if hw : w ∈ e.val.target then
          Complex.basisOneI.repr
            (SmoothSurfaceEquiv.originalChartDifferentialEquiv e (e.val.symm w)
              (e.val.map_target hw) (V (e.val.symm w))) k
        else 0
      let B : ℂ := (G.density e x : ℂ) / 2 *
        (((fderiv ℝ (fun w => C w 0) z 1 -
            fderiv ℝ (fun w => C w 1) z Complex.I : ℝ) : ℂ) -
          Complex.I * ((fderiv ℝ (fun w => C w 1) z 1 +
            fderiv ℝ (fun w => C w 0) z Complex.I : ℝ) : ℂ))
      ∀ v w : ℂ,
        (nativeMetricLieQuadraticPart R hvar G.metric V).val x (D.symm v) (D.symm w) =
          2 * (B * v * w).re := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro V e z hz
  let x := e.val.symm z
  have hx : x ∈ e.val.source := e.val.map_target hz
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  let L := nativeMetricLie R hvar G.metric V
  let P := nativeMetricLieQuadraticPart R hvar G.metric V
  let psi := nativeMetricLieConformalScalar R hvar G.metric V
  let b : Fin 2 → ℂ := Complex.basisOneI
  let Gram : ℂ → Fin 2 → Fin 2 → ℝ := fun w i j =>
    metricGramInChart G.metric e (e.val.symm w) (b i) (b j)
  let C : ℂ → Fin 2 → ℝ := fun w k =>
    if hw : w ∈ e.val.target then
      Complex.basisOneI.repr
        (SmoothSurfaceEquiv.originalChartDifferentialEquiv e (e.val.symm w)
          (e.val.map_target hw) (V (e.val.symm w))) k
    else 0
  let rho := G.density e x
  have hmetric (a c : ℂ) :
      G.metric.inner x (D.symm a) (D.symm c) = rho * inner ℝ a c :=
    quadratic_lie_metric_inverse_chart R G e x hx a c
  let B : ℂ := (rho : ℂ) / 2 *
    (((fderiv ℝ (fun w => C w 0) z 1 -
        fderiv ℝ (fun w => C w 1) z Complex.I : ℝ) : ℂ) -
      Complex.I * ((fderiv ℝ (fun w => C w 1) z 1 +
        fderiv ℝ (fun w => C w 0) z Complex.I : ℝ) : ℂ))
  have hgram (w : ℂ) (hw : w ∈ e.val.target) (i j : Fin 2) :
      Gram w i j = if i = j then G.density e (e.val.symm w) else 0 := by
    let D' := SmoothSurfaceEquiv.originalChartDifferentialEquiv e (e.val.symm w)
      (e.val.map_target hw)
    change metricGramInChart G.metric e (e.val.symm w) (b i) (b j) = _
    rw [metricGramInChart_eq G.metric e (e.val.symm w) (e.val.map_target hw)]
    change G.metric.inner (e.val.symm w) (D'.symm (b i)) (D'.symm (b j)) = _
    have hm : G.metric.inner (e.val.symm w) (D'.symm (b i)) (D'.symm (b j)) =
        G.density e (e.val.symm w) * inner ℝ (b i) (b j) :=
      quadratic_lie_metric_inverse_chart R G e (e.val.symm w) (e.val.map_target hw) (b i) (b j)
    rw [hm]
    fin_cases i <;> fin_cases j <;>
      simp [b, Complex.coe_basisOneI]
  have hdiag : fderiv ℝ (fun w => Gram w 1 1) z =
      fderiv ℝ (fun w => Gram w 0 0) z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [e.val.open_target.mem_nhds hz] with w hw
    simp only [hgram w hw]
  have hoff : fderiv ℝ (fun w => Gram w 0 1) z = 0 := by
    have hnear : (fun w => Gram w 0 1) =ᶠ[𝓝 z] (fun _ : ℂ => (0 : ℝ)) := by
      filter_upwards [e.val.open_target.mem_nhds hz] with w hw
      simpa using hgram w hw 0 1
    rw [hnear.fderiv_eq]
    exact fderiv_const_apply (0 : ℝ)
  have hLie (i j : Fin 2) :
      L.val x (D.symm (b i)) (D.symm (b j)) =
        ∑ k : Fin 2,
          (C z k * fderiv ℝ (fun w => Gram w i j) z (b k) +
            Gram z i k * fderiv ℝ (fun w => C w k) z (b j) +
            Gram z j k * fderiv ℝ (fun w => C w k) z (b i)) :=
    nativeMetricLie_hasOriginalCoordinates R hvar G.metric V e z hz i j
  let T := C z 0 * fderiv ℝ (fun w => Gram w 0 0) z 1 +
    C z 1 * fderiv ℝ (fun w => Gram w 0 0) z Complex.I
  have h00 : L.val x (D.symm 1) (D.symm 1) =
      T + 2 * rho * fderiv ℝ (fun w => C w 0) z 1 := by
    have h := hLie 0 0
    simp [Fin.sum_univ_two, b, Complex.coe_basisOneI, hgram z hz] at h
    dsimp only [T, rho]
    nlinarith [h]
  have h11 : L.val x (D.symm Complex.I) (D.symm Complex.I) =
      T + 2 * rho * fderiv ℝ (fun w => C w 1) z Complex.I := by
    have h := hLie 1 1
    simp [Fin.sum_univ_two, b, Complex.coe_basisOneI, hgram z hz] at h
    rw [hdiag] at h
    dsimp only [T, rho]
    nlinarith [h]
  have h01 : L.val x (D.symm 1) (D.symm Complex.I) =
      rho * (fderiv ℝ (fun w => C w 0) z Complex.I +
        fderiv ℝ (fun w => C w 1) z 1) := by
    have h := hLie 0 1
    simp [Fin.sum_univ_two, b, Complex.coe_basisOneI, hgram z hz, hoff] at h
    dsimp only [rho]
    nlinarith [h]
  have htr : G.density e x * metricTensorTrace R G.metric L x =
      L.val x (D.symm 1) (D.symm 1) + L.val x (D.symm Complex.I) (D.symm Complex.I) :=
    metricTensorTrace_conformal_frame R G L e x hx
  have hpsi : psi x = (2 : ℝ)⁻¹ * metricTensorTrace R G.metric L x := rfl
  have hP00 : P.val x (D.symm 1) (D.symm 1) =
      rho * (fderiv ℝ (fun w => C w 0) z 1 -
        fderiv ℝ (fun w => C w 1) z Complex.I) := by
    change L.val x (D.symm 1) (D.symm 1) -
      psi x * G.metric.inner x (D.symm 1) (D.symm 1) = _
    rw [hmetric 1 1, quadratic_lie_real_inner, hpsi]
    simp only [Complex.one_re, Complex.one_im, mul_one, mul_zero, add_zero]
    dsimp only [rho] at h00 h11 ⊢
    nlinarith only [htr, h00, h11]
  have hP01 : P.val x (D.symm 1) (D.symm Complex.I) =
      rho * (fderiv ℝ (fun w => C w 0) z Complex.I +
        fderiv ℝ (fun w => C w 1) z 1) := by
    change L.val x (D.symm 1) (D.symm Complex.I) -
      psi x * G.metric.inner x (D.symm 1) (D.symm Complex.I) = _
    rw [hmetric 1 Complex.I, quadratic_lie_real_inner]
    simpa only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_add, sub_zero] using h01
  have hP11 : P.val x (D.symm Complex.I) (D.symm Complex.I) =
      -P.val x (D.symm 1) (D.symm 1) :=
    (metricTensorTrace_eq_zero_iff_conformal_frame R G P e x hx).mp
      (nativeMetricLieQuadraticPart_trace_zero R hvar G V x)
  have hsymm := P.property
  change ∀ (y : X) (a c : RealSurfaceTangent R.toRiemannSurface y),
    P.val y a c = P.val y c a at hsymm
  have hP10 : P.val x (D.symm Complex.I) (D.symm 1) =
      P.val x (D.symm 1) (D.symm Complex.I) := hsymm x _ _
  let : IsNormableSpace ℝ (RealSurfaceTangent R.toRiemannSurface x) := D.isNormableSpace
  let PC : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    (P.val x).bilinearComp D.symm.toContinuousLinearMap D.symm.toContinuousLinearMap
  have hPC (a c : ℂ) : PC a c = P.val x (D.symm a) (D.symm c) := rfl
  let Q : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := (2 : ℝ) • quadraticModel B
  have hQ (a c : ℂ) : Q a c = 2 * (B * a * c).re := by
    change 2 * quadraticModel B a c = _
    rw [quadratic_lie_model_apply]
  have hBre : 2 * B.re = rho *
      (fderiv ℝ (fun w => C w 0) z 1 - fderiv ℝ (fun w => C w 1) z Complex.I) := by
    simp only [B, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hBim : -(2 * B.im) = rho *
      (fderiv ℝ (fun w => C w 0) z Complex.I + fderiv ℝ (fun w => C w 1) z 1) := by
    simp only [B, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have heq : PC.toLinearMap₁₂ = Q.toLinearMap₁₂ := by
    apply LinearMap.ext_basis Complex.basisOneI Complex.basisOneI
    intro i j
    change PC (b i) (b j) = Q (b i) (b j)
    rw [hPC, hQ]
    fin_cases i <;> fin_cases j
    · simpa only [b, Complex.coe_basisOneI, Matrix.cons_val_zero', mul_one] using
        hP00.trans hBre.symm
    · simpa only [b, Complex.coe_basisOneI, Matrix.cons_val_zero', Matrix.cons_val_succ',
        mul_one, Complex.mul_I_re, mul_neg] using hP01.trans hBim.symm
    · simpa only [b, Complex.coe_basisOneI, Matrix.cons_val_zero', Matrix.cons_val_succ',
        mul_one, Complex.mul_I_re, mul_neg] using hP10.trans (hP01.trans hBim.symm)
    · simpa only [b, Complex.coe_basisOneI, Matrix.cons_val_succ',
        Matrix.cons_val_zero', mul_one, mul_assoc,
        Complex.I_mul_I, mul_neg_one, Complex.neg_re, mul_neg] using
        hP11.trans (congrArg (fun t : ℝ => -t) (hP00.trans hBre.symm))
  intro v w
  have h := congrArg (fun A : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ => A v w) heq
  simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
    hPC, hQ] using h

/-- Adding all conformal directions gives the same source vertical span
whether the full Lie tensors or their pure quadratic representatives are used. -/
theorem conformal_sup_span_nativeMetricLie_eq_quadraticPart
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    conformalVerticalTensors (R := R) g ⊔
        Submodule.span ℝ (Set.range (nativeMetricLie R hvar g)) =
      conformalVerticalTensors (R := R) g ⊔
        Submodule.span ℝ (Set.range (nativeMetricLieQuadraticPart R hvar g)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  let C := conformalVerticalTensors (R := R) g
  let A := Submodule.span ℝ (Set.range (nativeMetricLie R hvar g))
  let B := Submodule.span ℝ (Set.range (nativeMetricLieQuadraticPart R hvar g))
  change C ⊔ A = C ⊔ B
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    rintro L ⟨V, rfl⟩
    have hc : nativeMetricLie R hvar g V - nativeMetricLieQuadraticPart R hvar g V ∈ C :=
      nativeMetricLie_sub_quadraticPart_mem_conformal R hvar g V
    have hp : nativeMetricLieQuadraticPart R hvar g V ∈ B :=
      Submodule.subset_span ⟨V, rfl⟩
    have hsum : (nativeMetricLie R hvar g V - nativeMetricLieQuadraticPart R hvar g V) +
        nativeMetricLieQuadraticPart R hvar g V ∈ C ⊔ B :=
      (C ⊔ B).add_mem (Submodule.mem_sup_left hc) (Submodule.mem_sup_right hp)
    rw [sub_add_cancel] at hsum
    exact hsum
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    rintro P ⟨V, rfl⟩
    have hc : nativeMetricLie R hvar g V - nativeMetricLieQuadraticPart R hvar g V ∈ C :=
      nativeMetricLie_sub_quadraticPart_mem_conformal R hvar g V
    have hl : nativeMetricLie R hvar g V ∈ A := Submodule.subset_span ⟨V, rfl⟩
    have hsub : nativeMetricLie R hvar g V -
        (nativeMetricLie R hvar g V - nativeMetricLieQuadraticPart R hvar g V) ∈ C ⊔ A :=
      (C ⊔ A).sub_mem (Submodule.mem_sup_right hl) (Submodule.mem_sup_left hc)
    rw [sub_sub_cancel] at hsub
    exact hsub

end SmoothSurfaceMetric
end LowDimensionalTopology.Geometry.Teichmuller
