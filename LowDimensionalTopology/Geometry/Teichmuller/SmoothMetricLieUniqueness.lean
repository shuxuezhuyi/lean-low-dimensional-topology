module

public import LowDimensionalTopology.Geometry.Teichmuller.SmoothMetricFamilyVelocity
public import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Uniqueness of the native metric Lie tensor

The full original coordinate law fixes a genuine tensor on every tangent
pair. Consequently the scalar pullback derivative is independent of the
chosen actual family with the same native velocity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
namespace SmoothSurfaceMetric

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The full original-chart expression determines the native Lie tensor. -/
theorem metricLieTensor_unique
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ (V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X))
        (L K : SmoothSymmetricTwoTensor R),
      HasOriginalMetricLieCoordinates R g V L →
      HasOriginalMetricLieCoordinates R g V K → L = K := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro V L K hL hK
  apply Subtype.ext
  apply ContMDiffSection.ext
  intro x
  let e : OriginalComplexChart R.toRiemannSurface :=
    ⟨chartAt ℂ x, chart_mem_atlas ℂ x⟩
  have hx : x ∈ e.val.source := mem_chart_source ℂ x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  let y : X := e.val.symm (e.val x)
  have hy : y ∈ e.val.source := e.val.map_target hz
  have hyx : y = x := e.val.left_inv hx
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e y hy
  let B := Complex.basisOneI.map D.symm.toLinearEquiv
  have hbilin : (L.val y).toLinearMap₁₂ = (K.val y).toLinearMap₁₂ := by
    apply LinearMap.ext_basis B B
    intro i j
    change L.val y (D.symm (Complex.basisOneI i)) (D.symm (Complex.basisOneI j)) =
      K.val y (D.symm (Complex.basisOneI i)) (D.symm (Complex.basisOneI j))
    have hLi := hL e (e.val x) hz i j
    have hKi := hK e (e.val x) hz i j
    exact hLi.trans hKi.symm
  have hbilinX : (L.val x).toLinearMap₁₂ = (K.val x).toLinearMap₁₂ := by
    exact Eq.mp (congrArg (fun t : X =>
      (L.val t).toLinearMap₁₂ = (K.val t).toLinearMap₁₂) hyx) hbilin
  ext a b
  exact congrArg (fun A => A a b) hbilinX

/-- Any actual jointly smooth family with the same velocity differentiates
to the same native tensor on every original tangent pair. -/
theorem hasDerivAt_pullback_of_sameNativeVelocity
    (Phi : ℝ → SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (hzero : ∀ x : X, (Phi 0).toHomeomorph x = x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (∀ x : X, ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × X => (Phi p.1).toHomeomorph p.2) (0, x)) →
    ∀ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
      (∀ (e : OriginalComplexChart R.toRiemannSurface)
          (x : X) (hx : x ∈ e.val.source),
        HasDerivAt (fun t : ℝ => e.val ((Phi t).toHomeomorph x))
          (SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx (V x)) 0) →
      ∀ L : SmoothSymmetricTwoTensor R,
        HasOriginalMetricLieCoordinates R g V L →
        ∀ (x : X) (a b : RealSurfaceTangent R.toRiemannSurface x),
          HasDerivAt (fun t : ℝ => (pullback (Phi t) g).inner x a b)
            (L.val x a b) 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro hPhi V hV L hL
  rcases exists_metricLieTensor_of_smoothFamily R Phi g hzero hPhi V hV with
    ⟨K, hKderiv, hKcoord⟩
  have hKL : K = L := metricLieTensor_unique R g V K L hKcoord hL
  simpa only [hKL] using hKderiv

end SmoothSurfaceMetric
end LowDimensionalTopology.Geometry.Teichmuller
