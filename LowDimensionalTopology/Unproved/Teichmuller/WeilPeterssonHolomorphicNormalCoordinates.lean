module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSmoothForm
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSmoothRealMetric

/-!
# The explicit holomorphic normal-coordinate obligation

The local change acts inside the existing full Bers coordinate target.
Its transported coefficients evaluate the original native Hermitian form
on the actual inverse Bers differential. The real metric has twice these
Hermitian coefficients. No existence proof is supplied here.
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

local notation "I" => Fin (3*g-3)
local notation "E" => I → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "H" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

/-- Smoothness and closedness of the actual original WP metric imply
holomorphic coordinates in which its real coefficient matrix is the identity
at the center and has zero real first derivative. -/
def WeilPeterssonHolomorphicNormalCoordinates : Prop :=
  letI := C
  let U := (chart (basePoint R)).target
  let coefficient (χ : OpenPartialHomeomorph E E) (x : E) (j k : I) : ℂ :=
    let q := (chart (basePoint R)).symm (χ x)
    let L := K q
    let A := fderiv ℂ (χ : E → E) x
    (H q).inner (L.symm (A (Pi.single k 1))) (L.symm (A (Pi.single j 1)))
  WeilPeterssonLocalCoefficientSmoothness R hp hg hgenus hΓ hfree hsmooth →
  (∀ t ∈ U, extDerivWithin Ω U t = 0) →
  ∀ t ∈ U, ∃ χ : OpenPartialHomeomorph E E,
    0 ∈ χ.source ∧ χ 0 = t ∧ χ.target ⊆ U ∧
    DifferentiableOn ℂ (χ : E → E) χ.source ∧
    DifferentiableOn ℂ (χ.symm : E → E) χ.target ∧
    ∀ j k : I,
      2 * coefficient χ 0 j k = (if j = k then 1 else 0) ∧
      HasFDerivAt (fun x : E => 2 * coefficient χ x j k) (0 : E →L[ℝ] ℂ) 0

end LowDimensionalTopology.Unproved.Teichmuller
