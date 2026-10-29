module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSmoothForm
public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealTangentTrivialization
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Smooth native vector coefficients in the original WP chart

The coordinates use the actual real Bers differential and the same original
chart inverse. Their smoothness is read from the existing tangent-bundle
section coordinates; no tangent-fibre norm or new vector-field frame is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3*g-3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "c" => nativeWeilPeterssonCoordinateChart
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)

/-- The actual native vector field has smooth coefficients throughout the
same full original real Bers chart target. -/
theorem nativeWP_vectorFieldCoordinates_contDiffOn :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ W : FormInterior.SmoothVectorField RI (M := T),
      ContDiffOn ℝ ∞ (fun z : E => D ((c).symm z) (W ((c).symm z))) (c).target := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro W
  have hcoords (q : T) : ContMDiffAt RI RI ∞ (fun r : T => D r (W r)) q := by
    let e := trivializationAt E (TangentSpace RI) q
    apply ((Bundle.contMDiffAt_section q).mp (W.contMDiff q)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace RI) q)] with r hr
    change (D r).toContinuousLinearMap (W r) = (e ⟨r, W r⟩).2
    rw [← nativeWeilPeterssonRealTangentCoordinateEquiv_trivialization
      R hp hg hgenus hΓ hfree hsmooth q r]
    exact e.continuousLinearMapAt_apply_of_mem ℝ hr (W r)
  have hinv := contMDiffOn_chart_symm (I := RI) (n := ∞) (x := basePoint R)
  change ContMDiffOn RI RI ∞ (c).symm (c).target at hinv
  intro z hz
  have h := (hcoords ((c).symm z)).comp z
    (hinv.contMDiffAt ((c).open_target.mem_nhds hz))
  simpa only [Function.comp_def] using h.contDiffAt.contDiffWithinAt

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
