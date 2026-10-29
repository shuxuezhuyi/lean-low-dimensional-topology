module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonLocalCoefficients
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The explicit WP local smoothness obligation

The analytic local-smoothness input from the source is retained as an
explicit proposition; its precise source and reason are recorded in the
central unproved ledger. No proof is supplied by this definition.

This is real C∞ smoothness of the same original integral-defined tangent
family in its already existing actual holomorphic Bers chart. It is not
complex C∞, and neither an arbitrary coefficient family nor a replacement
metric occurs in the proposition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller.TeichmullerSpace
open Geometry.Teichmuller.GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : QuasiconformalSmoothing.{0})

/-- The original WP Hermitian form has real C∞ coefficients in the actual
canonical Bers charts of the original native Teichmüller space. -/
def WeilPeterssonLocalCoefficientSmoothness : Prop :=
  ∀ (a : Geometry.Teichmuller.TeichmullerSpace.{0,0} R) (j k : Fin (3*g-3)),
    ContDiffOn ℝ ∞
      (nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree hsmooth a j k)
      (nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth a).target

end LowDimensionalTopology.Unproved.Teichmuller
