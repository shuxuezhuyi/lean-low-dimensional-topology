module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalTensorL2Pairing
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalTensorPairingIsothermal

/-!
# Tensor normalization for the half-sized coefficient matrix

The integral is one quarter of the ordinary real tensor contraction integral.
The coefficient formula keeps the full trace term and uses the actual
coefficient of twice the quadratic differential in both native tensors.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff InnerProductSpace ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u

/-- The tensor integral for the half-sized real coefficient matrix convention. -/
def metricTensorBookL2Pairing
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R g)
    (h k : SmoothSymmetricTwoTensor R) : ℝ :=
  (1 / 4 : ℝ) * metricTensorL2Pairing R g harea h k

/-- The rescaled contraction has the literal quadratic coefficient convention,
including the trace part, on the same original tangent slots. -/
theorem metricTensorPointwisePairing_book_coefficients
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (G : AtlasInducedMetric R.toRiemannSurface)
    (h k : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface)
    (x : X) (hx : x ∈ e.val.source) (A C : ℝ) (B D : ℂ) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    let F := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
    let rho : ℝ := G.density e x
    (∀ v w : RealSurfaceTangent R.toRiemannSurface x,
      h.val.toFun x v w = A * inner ℝ (F v) (F w) +
        ((2 : ℂ) * B * F v * F w).re) →
    (∀ v w : RealSurfaceTangent R.toRiemannSurface x,
      k.val.toFun x v w = C * inner ℝ (F v) (F w) +
        ((2 : ℂ) * D * F v * F w).re) →
    rho ^ 2 * ((1 / 4 : ℝ) * metricTensorPointwisePairing R G.metric h k x) =
      (A * C + 4 * (B * conj D).re) / 2 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let rho : ℝ := G.density e x
  dsimp only
  intro hh hk
  have hn := (metricTensorPointwisePairing_isothermal_coefficients R G h k e x hx
    A C ((2 : ℂ) * B) ((2 : ℂ) * D) hh hk).1
  have hscale : ((2 : ℂ) * B) * conj ((2 : ℂ) * D) =
      (4 : ℂ) * (B * conj D) := by
    rw [map_mul, Complex.conj_ofNat]
    ring
  have hcoeff : (((2 : ℂ) * B) * conj ((2 : ℂ) * D)).re =
      4 * (B * conj D).re := by
    rw [hscale, Complex.mul_re]
    norm_num
  rw [hcoeff] at hn
  calc
    rho ^ 2 * ((1 / 4 : ℝ) * metricTensorPointwisePairing R G.metric h k x) =
        (1 / 4 : ℝ) * (rho ^ 2 * metricTensorPointwisePairing R G.metric h k x) := by ring
    _ = (1 / 4 : ℝ) * (2 * (A * C + 4 * (B * conj D).re)) := by rw [hn]
    _ = (A * C + 4 * (B * conj D).re) / 2 := by ring

end LowDimensionalTopology.Geometry.Teichmuller
