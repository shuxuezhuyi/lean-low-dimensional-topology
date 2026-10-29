module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalWPCorrectedMixedHessian
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonBaseCoordinateClosedness

/-!
# The actual mixed Hessian at the native harmonic base point

The genuine integral first variation gives the full zero first derivative
of each original coefficient. Consequently every inverse correction in the
established lowered formula vanishes there, without a new normalization input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "H" => nativeWeilPeterssonLocalCoefficient
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "Dz" => nativeWeilPeterssonCoordinateDz (g := g)
local notation "Dbar" => nativeWeilPeterssonCoordinateDbar (g := g)
local notation "L" => nativeWeilPeterssonLoweredCurvatureExpression
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "C4" => nativeWeilPeterssonLoweredContraction
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

private theorem base_zero_mem_target : (0 : E) ∈ (chart (basePoint R)).target := by
  let := C
  have h := (chart (basePoint R)).map_source (mem_chart_source E (basePoint R))
  simpa only [nativeWeilPeterssonCoordinateChart_coe, bersCoordinates_basePoint] using h

/-- The original full lowered coefficient at the base point is its actual
mixed Hessian; the first-variation producer eliminates every inverse term. -/
theorem nativeWeilPeterssonBaseLowered_eq_actual_mixedHessian
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hvariation : Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0}) (j k l m : I) :
    L j k l m 0 = Dz (fun t => Dbar (H j k) m t) l 0 := by
  have h0 := base_zero_mem_target R hp hg hgenus hΓ hfree hsmooth
  have hΩ : DifferentiableAt ℝ Ω 0 :=
    ((contDiffOn_nativeWeilPeterssonFundamentalRealCoordinateForm_of_localSmoothness
      R hp hg hgenus hΓ hfree hsmooth hWP (basePoint R)).contDiffAt
        ((chart (basePoint R)).open_target.mem_nhds h0)).differentiableAt (by simp)
  have hd (a b : I) := hasFDerivAt_nativeWeilPeterssonBaseCoefficient_zero
    R hp hg hgenus hΓ hfree hsmooth hvariation hjets hΩ a b
  have hDz (a b c : I) : Dz (H a b) c 0 = 0 := by
    unfold nativeWeilPeterssonCoordinateDz
    rw [(hd a b).fderiv]
    simp
  rw [nativeWeilPeterssonLoweredCurvatureExpression_eq_corrected_mixed
    R hp hg hgenus hΓ hfree hsmooth hWP (basePoint R) 0 h0]
  simp only [hDz, zero_mul, Finset.sum_const_zero, sub_zero]

/-- The unchanged four-direction contraction at the base point is the
finite contraction of those actual mixed coefficient derivatives. -/
theorem nativeWeilPeterssonBaseLoweredContraction_eq_actual_mixedHessianSum
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hvariation : Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0}) (u v w s : E) :
    C4 u v w s 0 = ∑ j, ∑ k, ∑ l, ∑ m,
      Dz (fun t => Dbar (H j k) m t) l 0 * u j * conj (v k) * w l * conj (s m) := by
  unfold nativeWeilPeterssonLoweredContraction
  simp_rw [nativeWeilPeterssonBaseLowered_eq_actual_mixedHessian
    R hp hg hgenus hΓ hfree hsmooth hWP hvariation hjets]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
