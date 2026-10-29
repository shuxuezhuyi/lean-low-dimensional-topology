module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealTangent

/-!
# The actual real Bers tangent coordinates and singleton trivializations

Only the same original canonical atlas and its actual chart differentials occur.
The original complex coordinate equivalence supplies both continuity proofs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle
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
local notation "TI" => 𝓘(ℂ, E)
local notation "RI" => 𝓘(ℝ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "coord" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "realify" => nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "realManifold" =>
  Topology.IsOpenEmbedding.isManifold_singleton (I := RI) (n := ω)
    (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth)

/-- The existing actual complex coordinate map, on the original real tangent. -/
def nativeWeilPeterssonRealTangentCoordinateEquiv (a : TeichmullerSpace.{0,0} R) :
    letI := C
    TangentSpace RI a ≃L[ℝ] E := by
  let := C
  let L : TangentSpace TI a ≃L[ℝ] E :=
    { (coord a).toLinearEquiv.restrictScalars ℝ with
      continuous_toFun := (coord a).continuous
      continuous_invFun := (coord a).symm.continuous }
  exact (realify a).trans L

local notation "realCoord" =>
  nativeWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth

/-- This coordinate equivalence is the actual real Bers differential. -/
theorem nativeWeilPeterssonRealTangentCoordinateEquiv_apply (a : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v : TangentSpace RI a,
      realCoord a v = (NormedSpace.fromTangentSpace (𝕜 := ℝ) (BC a))
        (mfderiv RI RI BC a v) := by
  let := C
  exact nativeRealComplexTangentEquiv_coordinate_apply R hp hg hgenus hΓ hfree hsmooth a

/-- Every actual tangent trivialization is the same actual real Bers differential. -/
theorem nativeWeilPeterssonRealTangentCoordinateEquiv_trivialization
    (a q : TeichmullerSpace.{0,0} R) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    (trivializationAt E (TangentSpace RI) a).continuousLinearMapAt ℝ q =
      (realCoord q).toContinuousLinearMap := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  have hq : q ∈ (chartAt E a).source := mem_chart_source E q
  have ht := TangentBundle.continuousLinearMapAt_trivializationAt (I := RI) hq
  apply ContinuousLinearMap.ext
  intro v
  have hc : realCoord q v = mfderiv RI RI (extChartAt RI a) q v :=
    nativeWeilPeterssonRealTangentCoordinateEquiv_apply R hp hg hgenus hΓ hfree hsmooth q v
  exact (congrArg (fun L : TangentSpace RI q →L[ℝ] E => L v) ht).trans hc.symm

/-- The inverse actual tangent trivialization is the inverse real Bers differential. -/
theorem nativeWeilPeterssonRealTangentCoordinateEquiv_symmL
    (a q : TeichmullerSpace.{0,0} R) :
    letI := C
    letI : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
    (trivializationAt E (TangentSpace RI) a).symmL ℝ q =
      (realCoord q).symm.toContinuousLinearMap := by
  let := C
  let : IsManifold RI ω (TeichmullerSpace.{0,0} R) := realManifold
  let e := trivializationAt E (TangentSpace RI) a
  have hq : q ∈ e.baseSet := mem_chart_source E q
  have ht : e.continuousLinearMapAt ℝ q = (realCoord q).toContinuousLinearMap :=
    nativeWeilPeterssonRealTangentCoordinateEquiv_trivialization R hp hg hgenus hΓ hfree hsmooth a q
  apply ContinuousLinearMap.ext
  intro v
  apply (realCoord q).injective
  have he : realCoord q (e.symmL ℝ q v) = v :=
    (congrArg (fun L : TangentSpace RI q →L[ℝ] E => L (e.symmL ℝ q v)) ht).symm.trans
      (e.continuousLinearMapAt_symmL hq v)
  exact he.trans ((realCoord q).apply_symm_apply v).symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
