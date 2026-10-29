module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSesquilinearContinuity
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonNativeDiagonalTrace
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSectionalExpressionSign

/-!
# Diagonal kernel control from the same second-variation input

The four-direction convergence statement already contains its diagonal
specialization. The original squared-modulus identity converts that
specialization to energy integrability. The actual mixed-kernel continuity
and native trace producers supply the remaining two diagonal clauses.
The second-variation hypothesis remains explicit throughout.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "chart" => nativeWeilPeterssonCoordinateChart
  R hp hg hgenus hΓ hfree hsmooth
local notation "S" => nativeWeilPeterssonHolomorphicSectionalExpression
  R hp hg hgenus hΓ hfree hsmooth

/-- Diagonal energy integrability follows from the same four-direction
convergence. Continuity and the exact native trace are produced separately;
no diagonal-control or strict-sign premise is assumed. -/
theorem nativeWeilPeterssonDiagonalKernelControl_of_secondVariation
    (hvariation : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth) :
    LowDimensionalTopology.Unproved.Teichmuller.WeilPeterssonDiagonalKernelControl
      R hp hg hgenus hΓ hfree hsmooth := by
  intro a ν P F hF v
  have hfour := (hvariation a ν P F hF).1.2.2 v v v v
  have hinner (ζ : ℍ) : Integrable (SourceKernel.energy (μ ν P F hF v) ζ) flatArea := by
    simpa only [SourceKernel.four_self, RCLike.re_eq_complex_re, Complex.ofReal_re] using
      (hfour.1 ζ).re
  have houter : IntegrableOn
      (fun ζ => ∫ z : ℍ, SourceKernel.energy (μ ν P F hF v) ζ z ∂flatArea) F flatArea := by
    simpa only [SourceKernel.four_self, integral_complex_ofReal, RCLike.re_eq_complex_re,
      Complex.ofReal_re] using hfour.2.re
  refine ⟨hinner, houter, ?_, ?_⟩
  · intro ζ
    exact nativeWeilPetersson_sesquilinear_continuous_right
      R hp hg hgenus hΓ hfree hsmooth ν P F hF v v ζ
  · exact nativeWeilPetersson_sesquilinear_diagonal_trace
      R hp hg hgenus hΓ hfree hsmooth a ν P F hF v

/-- The actual sectional coordinate expression has strict negative real
part under second variation, using the produced diagonal control. -/
theorem nativeWeilPeterssonSectionalExpression_re_neg_of_secondVariation
    (hvariation : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (a : TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (v : E) (hv : v ≠ 0) :
    (S a v ((chart a) (β ν.val))).re < 0 := by
  exact nativeWeilPeterssonSectionalExpression_re_neg
    R hp hg hgenus hΓ hfree hsmooth hvariation a ν P F hF
      (nativeWeilPeterssonDiagonalKernelControl_of_secondVariation
        R hp hg hgenus hΓ hfree hsmooth hvariation) v hv

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
