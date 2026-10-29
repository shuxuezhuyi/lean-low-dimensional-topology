module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedGeodesicLength
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSmoothForm

/-!
# Length-dual vectors for the native marked-length function

This equation predicate records a property of a supplied tangent vector on
the existing native real tangent fibre. It does not assert the property
for an arbitrary vector. Its coefficient is one with the normalization
`gWP = 2 Re hWP`. Actual FN producers prove the property for their own
geometrically identified signed unit-twist vectors.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth

/-- The supplied vector's contraction with the native WP form is the complete
actual marked-length differential at the same point. This is not reciprocity
and does not assert that an FN twist vector exists. -/
def WolpertLengthDualityAt (q : Geometry.Teichmuller.TeichmullerSpace.{0,0} R)
    (α : LiZhongQC.Loop X) (v : letI := C; TangentSpace RI q) : Prop := by
  let := C
  exact ∀ z,
    nativeWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hfree hsmooth q ![v, z] =
      mfderiv RI 𝓘(ℝ) (markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α) q z

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

namespace LowDimensionalTopology.Unproved.Teichmuller

/-- Legacy name for the supplied-vector length-duality equation predicate. -/
abbrev WolpertLengthDualityAt :=
  @LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace.WolpertLengthDualityAt

end LowDimensionalTopology.Unproved.Teichmuller
