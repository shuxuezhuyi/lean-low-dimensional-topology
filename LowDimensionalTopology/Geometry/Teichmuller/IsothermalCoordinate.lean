module

public import LowDimensionalTopology.Geometry.Teichmuller.RiemannianConformality
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Orientation-compatible isothermal coordinates

An isothermal coordinate is a local smooth coordinate agreeing with the
given orientation and satisfying the full identity `g = ρ (du² + dv²)`
for a positive smooth function `ρ`.

This definition allows every genuine local coordinate; neither a global
homeomorphism of the plane nor a Beltrami solution is included as extra data.
It does not assert existence for an arbitrary metric.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff InnerProductSpace

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}

/-- A local isothermal coordinate for the actual original smooth metric.
The real and imaginary parts of `coordinate` are the two real coordinates.
The metric equality is imposed on every pair of original tangent vectors. -/
structure IsothermalCoordinate (g : SmoothSurfaceMetric R) where
  coordinate : OpenPartialHomeomorph X ℂ
  smooth_toFun :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (coordinate : X → ℂ) coordinate.source
  smooth_invFun :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (coordinate.symm : ℂ → X) coordinate.target
  orientation_preserving :
    ∀ e : OriginalComplexChart R, ∀ z ∈ (e.val.symm.trans coordinate).source,
      0 < realJacobian (e.val.symm.trans coordinate) z
  density : X → ℝ
  density_smooth :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ density coordinate.source
  density_pos : ∀ x ∈ coordinate.source, 0 < density x
  inner_eq :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ x ∈ coordinate.source, ∀ v w : RealSurfaceTangent R x,
      g.inner x v w = density x *
        ⟪mvfderiv 𝓘(ℝ, ℂ) (coordinate : X → ℂ) x v,
          mvfderiv 𝓘(ℝ, ℂ) (coordinate : X → ℂ) x w⟫_ℝ

namespace AtlasInducedMetric

/-- Every original complex chart of an actually compatible metric is an
isothermal coordinate, with the original metric's own positive smooth density.
No local-solution or metric-existence theorem is assumed here. -/
def isothermalCoordinate (g : AtlasInducedMetric R) (e : OriginalComplexChart R) :
    IsothermalCoordinate g.metric where
  coordinate := e.val
  smooth_toFun := by
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    exact contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property)
  smooth_invFun := by
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    exact contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property)
  orientation_preserving := by
    intro f z hz
    exact preservesComplexOrientation_id R.toRiemannAtlas
      f.val f.property e.val e.property z hz
  density := g.density e
  density_smooth := g.density_smooth e
  density_pos := g.density_pos e
  inner_eq := g.inner_eq e

end AtlasInducedMetric

end LowDimensionalTopology.Geometry.Teichmuller
