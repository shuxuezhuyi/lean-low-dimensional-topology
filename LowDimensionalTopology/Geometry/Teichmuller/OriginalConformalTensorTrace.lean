module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricTensorTrace
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The native trace calculation in an isothermal chart

This is the local trace step for an actual atlas-induced metric. For an
arbitrary original metric, the existing isothermal marked target supplies
this input; conformality of that original metric to its reference atlas is
not an assumption. Both tensor slots below remain actual tangent vectors.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff InnerProductSpace ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- In the actual inverse-chart frame, density times native trace is the
sum of the two diagonal entries of the original tensor. -/
theorem metricTensorTrace_conformal_frame
    (G : AtlasInducedMetric R.toRiemannSurface) (ξ : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) (hx : x ∈ e.val.source) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
    G.density e x * metricTensorTrace R G.metric ξ x =
      ξ.val.toFun x (D.symm 1) (D.symm 1) +
        ξ.val.toFun x (D.symm Complex.I) (D.symm Complex.I) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  let A := metricRaisedTensor R G.metric ξ x
  let B : ℂ →ₗ[ℝ] ℂ := D.toLinearEquiv.conj A
  have htr : metricTensorTrace R G.metric ξ x = (B 1).re + (B Complex.I).im := by
    calc
      metricTensorTrace R G.metric ξ x = LinearMap.trace ℝ ℂ B :=
        (LinearMap.trace_conj' A D.toLinearEquiv).symm
      _ = (B 1).re + (B Complex.I).im := by
        rw [LinearMap.trace_eq_matrix_trace ℝ Complex.basisOneI, Matrix.trace_fin_two]
        simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
          Matrix.cons_val_zero, Matrix.cons_val_one]
  have hi (a b : ℂ) : inner ℝ a b = a.re * b.re + a.im * b.im := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
    change (conj a * b).re = _
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hdiag (a : ℂ) : G.density e x * inner ℝ (B a) a =
      ξ.val.toFun x (D.symm a) (D.symm a) := by
    have hs := metricRaisedTensor_spec R G.metric ξ x (D.symm a) (D.symm a)
    rw [G.inner_eq e x hx] at hs
    change G.density e x * inner ℝ (B a) (D (D.symm a)) = _ at hs
    rw [D.apply_symm_apply] at hs
    exact hs
  have h0 : G.density e x * (B 1).re = ξ.val.toFun x (D.symm 1) (D.symm 1) := by
    have hs := hdiag 1
    rw [hi] at hs
    simpa only [Complex.one_re, Complex.one_im, mul_one, mul_zero, add_zero] using hs
  have h1 : G.density e x * (B Complex.I).im =
      ξ.val.toFun x (D.symm Complex.I) (D.symm Complex.I) := by
    have hs := hdiag Complex.I
    rw [hi] at hs
    simpa only [Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add] using hs
  rw [htr, mul_add]
  exact congrArg₂ (fun a b : ℝ => a + b) h0 h1

/-- Trace zero is exactly the opposite-diagonal condition in that same native frame. -/
theorem metricTensorTrace_eq_zero_iff_conformal_frame
    (G : AtlasInducedMetric R.toRiemannSurface) (ξ : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) (hx : x ∈ e.val.source) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
    metricTensorTrace R G.metric ξ x = 0 ↔
      ξ.val.toFun x (D.symm Complex.I) (D.symm Complex.I) =
        -ξ.val.toFun x (D.symm 1) (D.symm 1) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  have htr := metricTensorTrace_conformal_frame R G ξ e x hx
  constructor
  · intro ht
    rw [ht, mul_zero] at htr
    linarith
  · intro hd
    have hm : G.density e x * metricTensorTrace R G.metric ξ x = 0 := by
      rw [htr, hd, add_neg_cancel]
    exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt (G.density_pos e x hx))

end LowDimensionalTopology.Geometry.Teichmuller
