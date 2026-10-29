module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalQuadraticDifferentialTensor
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalTensorBookNormalization

/-!
# The displayed horizontal image and its pointwise normalization

The literal image consists of twice the real tensor of an actual original
holomorphic quadratic differential. Its book-normalized contraction has the
source factor two. Orthogonality, Green's identity and the global geometric
identification remain separate assertions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces AtlasMetricConstruction
universe u

/-- The real scalar action already inherited from the same native symmetric-tensor submodule. -/
local instance canonicalHorizontalTensorSMul
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) :
    SMul ℝ (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact Submodule.smul (symmetricTwoTensorSubmodule R)

/-- The displayed original tensor image {Q + conjugate Q}, with Q holomorphic. -/
def horizontalQuadraticTensors
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) :
    Set (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact Set.range (fun Q : HolomorphicQuadraticDifferential R.toRiemannAtlas =>
    (2 : ℝ) • quadraticDifferentialTensor R Q)

/-- The same actual horizontal tensors retain the factor two in the
book-normalized pairing, with rho equal to the actual area density lambda. -/
theorem metricTensorPointwisePairing_horizontal_normalization
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (G : AtlasInducedMetric R.toRiemannSurface)
    (Q P : HolomorphicQuadraticDifferential R.toRiemannAtlas) (p x : X)
    (hx : x ∈ (chosenChart R.toRiemannSurface p).val.source) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    let e := chosenChart R.toRiemannSurface p
    let rho := G.density e x
    rho ^ 2 * ((1 / 4 : ℝ) * metricTensorPointwisePairing R G.metric
        ((2 : ℝ) • quadraticDifferentialTensor R Q)
        ((2 : ℝ) • quadraticDifferentialTensor R P) x) =
      2 * (Q.val p (e.val x) * conj (P.val p (e.val x))).re := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let e := chosenChart R.toRiemannSurface p
  let rho := G.density e x
  dsimp only
  have htwice (T : HolomorphicQuadraticDifferential R.toRiemannAtlas)
      (v w : RealSurfaceTangent R.toRiemannSurface x) :
      ((2 : ℝ) • quadraticDifferentialTensor R T).val.toFun x v w =
        ((2 : ℂ) * T.val p (e.val x) *
          originalChartDifferential R.toRiemannSurface e x v *
          originalChartDifferential R.toRiemannSurface e x w).re := by
    change (2 : ℝ) * (quadraticDifferentialTensor R T).val.toFun x v w = _
    rw [quadraticDifferentialTensor_apply R T p x hx v w]
    let z : ℂ := T.val p (e.val x) *
      originalChartDifferential R.toRiemannSurface e x v *
      originalChartDifferential R.toRiemannSurface e x w
    have hs : (2 : ℂ) * T.val p (e.val x) *
        originalChartDifferential R.toRiemannSurface e x v *
        originalChartDifferential R.toRiemannSurface e x w = (2 : ℂ) * z := by
      dsimp only [z]
      ring
    have hr : ((2 : ℂ) * z).re = (2 : ℝ) * z.re := by
      rw [Complex.mul_re]
      norm_num
    exact ((congrArg Complex.re hs).trans hr).symm
  have hn := metricTensorPointwisePairing_book_coefficients R G
    ((2 : ℝ) • quadraticDifferentialTensor R Q)
    ((2 : ℝ) • quadraticDifferentialTensor R P) e x hx
    0 0 (Q.val p (e.val x)) (P.val p (e.val x))
    (by
      intro v w
      simpa only [zero_mul, zero_add,
        SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply] using htwice Q v w)
    (by
      intro v w
      simpa only [zero_mul, zero_add,
        SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply] using htwice P v w)
  calc
    rho ^ 2 * ((1 / 4 : ℝ) * metricTensorPointwisePairing R G.metric
        ((2 : ℝ) • quadraticDifferentialTensor R Q)
        ((2 : ℝ) • quadraticDifferentialTensor R P) x) =
        (0 * 0 + 4 * (Q.val p (e.val x) * conj (P.val p (e.val x))).re) / 2 := hn
    _ = 2 * (Q.val p (e.val x) * conj (P.val p (e.val x))).re := by ring

end LowDimensionalTopology.Geometry.Teichmuller
