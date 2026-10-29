module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedGeodesicLength
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSmoothForm
public import LowDimensionalTopology.Geometry.Teichmuller.WolpertLengthDuality

/-!
# Reciprocity from Wolpert length duality on the native real tangent fibre

Reciprocity follows by evaluating the two length-duality identities and
using alternation.

This conditional theorem uses the actual marked geodesic-length functions and
the existing native WP two-form. Its two hypotheses are the preceding Wolpert
duality identities, with the normalization `g = 2 Re h`. Constructing
the FN tangent vectors and proving those identities are separate obligations.
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
local notation "realForm" =>
  nativeWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hfree hsmooth
local notation "lengthOf" => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus

/-- The two preceding length-duality identities imply reciprocity for the
actual length differentials on the same native real tangent fibre. -/
theorem nativeMarkedLengthReciprocity_of_wolpertDuality
    (q : TeichmullerSpace.{0,0} R) (α β : LiZhongQC.Loop X)
    (v w : letI := C; TangentSpace RI q)
    (hα : WolpertLengthDualityAt R hp hg hgenus hΓ hfree hsmooth q α v)
    (hβ : WolpertLengthDualityAt R hp hg hgenus hΓ hfree hsmooth q β w) :
    letI := C
    mfderiv RI 𝓘(ℝ) (lengthOf β) q v =
      -mfderiv RI 𝓘(ℝ) (lengthOf α) q w := by
  let := C
  dsimp only [WolpertLengthDualityAt] at hα hβ
  rw [← hβ v, ← hα w]
  change @Eq ℝ (realForm q ![w, v]) (-(realForm q ![v, w]))
  simpa only [ContinuousAlternatingMap.coe_toAlternatingMap,
    Matrix.cons_cons_comp_swap_zero_one] using
    (realForm q).toAlternatingMap.map_swap ![v, w]
      (by decide : (0 : Fin 2) ≠ 1)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
