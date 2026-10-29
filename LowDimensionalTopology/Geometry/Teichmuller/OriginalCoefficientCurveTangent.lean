module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalLengthCoefficientTangent
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# The actual original coefficient curve and its native base tangent

The real derivative of the same weighted Bers curve is transported through
the existing linear Bers coordinates. The actual chart inverse recovers
native differentiability, with exactly the original projection tangent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter
open scoped UpperHalfPlane Manifold ContDiff Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "T" => TeichmullerSpace R
local notation "B" => Space Γ
local notation "E" => Fin (3 * g - 3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "RI" => 𝓘(ℝ, E)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "W" => weightedLinearBersCoordinates R hg hgenus hP hΓ hp
local notation "b" => basePoint R
local notation "c" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth b
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "r" => nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth

/-- A same original weighted Bers curve through the identity marking has
the actual coefficient-projection tangent in the actual native real chart. -/
theorem sameOriginalCoefficientCurve_native_base_tangent
    (γ : ℝ → T) (hγzero : γ 0 = b) (ν : B)
    (hcurve :
      let := NormedSpace.restrictScalars ℝ ℂ (BersWeighted.Automorphic Γ)
      let := IsScalarTower.restrictScalars ℝ ℂ (BersWeighted.Automorphic Γ)
      let : ContinuousSMul ℝ (BersWeighted.Automorphic Γ) := IsScalarTower.continuousSMul ℂ
      HasDerivAt (fun t : ℝ => (W).symm (BC (γ t)))
        (fderiv ℂ (BersWeighted.automorphicProjection hΓ) 0 ν) 0) :
    letI := C
    MDifferentiableAt 𝓘(ℝ) RI γ 0 ∧
      HasDerivAt (fun t : ℝ => BC (γ t))
        (D b ((r b).symm (mfderiv 𝓘(ℂ, B) TI β 0 ν))) 0 := by
  let := C
  let : IsManifold RI ω T :=
    (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth).isManifold_singleton
  let := NormedSpace.restrictScalars ℝ ℂ (BersWeighted.Automorphic Γ)
  let := IsScalarTower.restrictScalars ℝ ℂ (BersWeighted.Automorphic Γ)
  let : ContinuousSMul ℝ (BersWeighted.Automorphic Γ) := IsScalarTower.continuousSMul ℂ
  let WR : BersWeighted.Automorphic Γ →L[ℝ] E :=
    (W).toContinuousLinearMap.restrictScalars ℝ
  have h := WR.hasFDerivAt.comp_hasDerivAt 0 hcurve
  have hd : WR (fderiv ℂ (BersWeighted.automorphicProjection hΓ) 0 ν) =
      D b ((r b).symm (mfderiv 𝓘(ℂ, B) TI β 0 ν)) := by
    rw [nativeRealCoefficientTangent_coordinates,
      BersWeighted.fderiv_automorphicProjection]
    rfl
  have hBC : HasDerivAt (fun t : ℝ => BC (γ t))
      (D b ((r b).symm (mfderiv 𝓘(ℂ, B) TI β 0 ν))) 0 := by
    apply (h.congr_deriv hd).congr_of_eventuallyEq
    exact Eventually.of_forall fun t => ((W).apply_symm_apply (BC (γ t))).symm
  refine ⟨?_, hBC⟩
  have hcinv : MDifferentiableAt RI RI (c).symm (c b) :=
    (mdifferentiable_chart (I := RI) b).symm.mdifferentiableAt
      ((c).map_source (mem_chart_source E b))
  have hzero : BC (γ 0) = c b := by rw [hγzero]; rfl
  have hcomp := hcinv.comp_of_eq 0 hBC.differentiableAt.mdifferentiableAt hzero
  apply hcomp.congr_of_eventuallyEq
  exact Eventually.of_forall fun t =>
    ((c).left_inv (show γ t ∈ (c).source from mem_chart_source E (γ t))).symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
