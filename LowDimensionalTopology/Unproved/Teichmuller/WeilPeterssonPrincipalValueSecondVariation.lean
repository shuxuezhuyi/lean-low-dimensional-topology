module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSourceKernels

/-!
# Two explicit analytic obligations for the original WP second variation

The first fixes the singular inner PV, the lower outer Hilbert evaluation,
ordinary-kernel convergence and the complete four-direction formula for the
actual coefficient expression, with its original inverse and connection.
The corrected B coefficient arguments are justified by English C in (7.59)
and LearningMath printed 810, footnote 21, rather than the conflicting print
in English (7.61). The second fixes diagonal integrability, vertical continuity
and the trace identity. Neither asserts curvature negativity or identifies a
coordinate expression with geometric Riemann curvature.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller.TeichmullerSpace
open Geometry.Teichmuller.GammaMeasurableBeltrami
open Geometry.Teichmuller.NormalizedCoefficientTransport
open Geometry.Teichmuller.WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "hP" => canonicalHandleGroupPresentation g
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "coeff" => nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree hsmooth
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth
local notation "C4" => nativeWeilPeterssonLoweredContraction R hp hg hgenus hΓ hfree hsmooth

/-- Source-specific convergence and the full source identity for the actual
lowered expression. The inverse/connection correction is retained in that
unchanged expression; this is not an ordinary-Hessian formula in arbitrary
Bers coordinates. The first block contains the inner PV and ordinary-integral
convergence. Projection `.2.1` uses the same Hilbert limit at lower bar ζ,
where the upper support is nonsingular; `.2.2` is the full source identity.
Identification with geometric Riemann curvature remains a separate obligation. -/
def WeilPeterssonPrincipalValueSecondVariation : Prop :=
  ∀ (a : Geometry.Teichmuller.TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Geometry.Fuchsian.HalfPlaneFuchsianGroup
      ((deformedGroup hΓ ν).map Geometry.Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Geometry.Fuchsian.IsHalfPlaneFundamentalRegion P F),
    ((∀ (v : E) (z ξ : ℍ), SourceKernel.PrincipalValueExists
        (SourceKernel.innerInput (μ ν P F hF v) z) ξ) ∧
      (∀ (u v : E) (ζ z : ℍ), SourceKernel.SesquilinearIntegralExists
        (μ ν P F hF u) (μ ν P F hF v) ζ z) ∧
      (∀ u v w s : E,
        (∀ ζ : ℍ, Integrable (SourceKernel.four (μ ν P F hF u) (μ ν P F hF v)
          (μ ν P F hF w) (μ ν P F hF s) ζ) flatArea) ∧
        IntegrableOn (fun ζ => ∫ z : ℍ,
          SourceKernel.four (μ ν P F hF u) (μ ν P F hF v)
            (μ ν P F hF w) (μ ν P F hF s) ζ z ∂flatArea) F flatArea)) ∧
    (∀ (u v : E) (z ζ : ℍ), SourceKernel.PrincipalValueExists
      (SourceKernel.outerInput (μ ν P F hF u) (μ ν P F hF v) z) (conj (ζ : ℂ))) ∧
    ∀ u v w s : E,
      C4 a u v w s ((chart a) (β ν.val)) =
        ((12 / Real.pi ^ 5 : ℝ) : ℂ) *
          ∫ ζ in F, ∫ z : ℍ,
            SourceKernel.four (μ ν P F hF u) (μ ν P F hF v)
              (μ ν P F hF w) (μ ν P F hF s) ζ z ∂flatArea ∂flatArea

/-- Independent analytic control of the corrected diagonal source kernel.
There is no positivity field: square-integral positivity is a proved consumer.
The trace is the same original first-linear WP pairing. For the original real
metric `g = 2 Re h`, its real part is `-(π²/24) g(v,v)`. -/
def WeilPeterssonDiagonalKernelControl : Prop :=
  ∀ (a : Geometry.Teichmuller.TeichmullerSpace.{0,0} R) (ν : Ball Γ)
    (P : Geometry.Fuchsian.HalfPlaneFuchsianGroup
      ((deformedGroup hΓ ν).map Geometry.Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Geometry.Fuchsian.IsHalfPlaneFundamentalRegion P F) (v : E),
    (∀ ζ : ℍ, Integrable (SourceKernel.energy (μ ν P F hF v) ζ) flatArea) ∧
    IntegrableOn (fun ζ => ∫ z : ℍ, SourceKernel.energy (μ ν P F hF v) ζ z ∂flatArea)
      F flatArea ∧
    (∀ ζ : ℍ, Continuous (SourceKernel.sesquilinear (μ ν P F hF v) (μ ν P F hF v) ζ)) ∧
    (∫ ζ in F, SourceKernel.sesquilinear (μ ν P F hF v) (μ ν P F hF v) ζ ζ ∂flatArea) =
      ((-(Real.pi ^ 2 / 12) : ℝ) : ℂ) *
        ∑ j, ∑ k, v j * conj (v k) * coeff a j k ((chart a) (β ν.val))

end LowDimensionalTopology.Unproved.Teichmuller
