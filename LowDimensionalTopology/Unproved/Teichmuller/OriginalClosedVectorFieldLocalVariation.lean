module

public import LowDimensionalTopology.Geometry.Teichmuller.MappingClassGroup
public import LowDimensionalTopology.Geometry.Teichmuller.RiemannianConformality
public import LowDimensionalTopology.Geometry.Teichmuller.SmoothFormInterior
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Actual local diffeomorphism variations of original smooth vector fields

The classical input produces a jointly smooth local family in the existing
homotopy-identity group, with the prescribed native velocity. It contains
no metric, tensor, coordinate Lie formula, or orthogonality conclusion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller
universe u

/-- Every original smooth vector field is the actual initial velocity of a
local jointly smooth family in the same existing homotopy-identity group. -/
def OriginalClosedVectorFieldLocalVariation
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) : Prop :=
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  ∀ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
    ∃ (epsilon : ℝ), 0 < epsilon ∧
      ∃ Phi : ℝ → ↥(OrientedSurfaceAut.homotopyIdentitySubgroup R),
        (∀ x : X, (Phi 0).val.smooth.toHomeomorph x = x) ∧
        ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
          (fun p : ℝ × X => (Phi p.1).val.smooth.toHomeomorph p.2)
          (Set.Ioo (-epsilon) epsilon ×ˢ Set.univ) ∧
        ∀ (e : OriginalComplexChart R.toRiemannSurface)
            (x : X) (hx : x ∈ e.val.source),
          HasDerivAt (fun t : ℝ => e.val ((Phi t).val.smooth.toHomeomorph x))
            (SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx (V x)) 0

end LowDimensionalTopology.Unproved.Teichmuller
