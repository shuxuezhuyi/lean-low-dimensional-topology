module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFinslerPathLength
public import LowDimensionalTopology.Geometry.Teichmuller.BersDerivativeQuotient
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Basic.ENNReal.Real

/-!
# The original infinitesimal polar function on cotangents

The polar supremum uses the actual infinitesimal tangent function. Its extended
nonnegative value does not presume boundedness. At each original coefficient
centre the native quadratic covector is given by the actual inverse Bers
coordinate differential and the original integral pairing.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "F₀" => originalInfinitesimalTangentFunction R hg hgenus hΓ hfree hp hsmooth

/-- The extended polar supremum on the original complex cotangent fibre.
Finiteness and norm properties are separate assertions. -/
def originalInfinitesimalCotangentFunction (a : TeichmullerSpace R) :
    letI := C
    StrongDual ℂ (TangentSpace 𝓘(ℂ, E) a) → ℝ≥0∞ := by
  let := C
  exact fun ℓ => ⨆ v : TangentSpace 𝓘(ℂ, E) a, ⨆ (_h : F₀ a v ≤ 1),
    ENNReal.ofReal ‖ℓ v‖

/-- Each vector in the actual infinitesimal unit ball contributes to its polar supremum. -/
theorem norm_pairing_le_originalInfinitesimalCotangentFunction (a : TeichmullerSpace R) :
    letI := C
    ∀ (ℓ : StrongDual ℂ (TangentSpace 𝓘(ℂ, E) a))
      (v : TangentSpace 𝓘(ℂ, E) a), F₀ a v ≤ 1 →
        ENNReal.ofReal ‖ℓ v‖ ≤
          originalInfinitesimalCotangentFunction R hg hgenus hΓ hfree hp hsmooth a ℓ := by
  let := C
  intro ℓ v hv
  exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)

variable (ν : Ball Γ)
local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "pY" => deformedTargetCover R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "Δ" => deformedGroup hΓ ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)

variable (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (D : Set ℍ) (hD : Fuchsian.IsHalfPlaneFundamentalRegion P D)
local notation "Q" => NativePetersson.Space Y P pY hpY D hD

/-- The full original tangent pairing with native quadratic differentials on
its actual normalized target, through the genuine Bers coordinate derivative. -/
def originalDeformedTangentQuadraticDuality :
    letI := C
    TangentSpace 𝓘(ℂ, E) (β ν.val) ≃L[ℂ] StrongDual ℂ Q := by
  let := C
  exact ((canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth (β ν.val)).trans
      (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm).trans
        (BersWeighted.automorphicPeterssonDuality Y pY hpY hΔ P D hD)

/-- Evaluation against a native quadratic differential gives a continuous
complex covector on the tangent at the same original coefficient centre. -/
def originalNativeQuadraticCovector (q : Q) :
    letI := C
    StrongDual ℂ (TangentSpace 𝓘(ℂ, E) (β ν.val)) := by
  let := C
  exact (ContinuousLinearMap.apply ℂ ℂ q).comp
    (originalDeformedTangentQuadraticDuality R hg hgenus hΓ hfree hp hsmooth ν P D hD).toContinuousLinearMap

/-- On every genuine coefficient projection derivative the native covector
is the original integral with the actual transported Beltrami direction. -/
theorem originalNativeQuadraticCovector_projection_derivative
    (q : Q) (μ : Space Γ) :
    letI := C
    originalNativeQuadraticCovector R hg hgenus hΓ hfree hp hsmooth ν P D hD q
      (mfderiv 𝓘(ℂ, Space Γ) 𝓘(ℂ, E) β ν.val μ) =
        ∫ z in UpperHalfPlane.coe '' D,
          planeRepresentative (gammaDerivative hΓ ν μ).val z *
            QuadraticBergman.uniformizedQuadratic Y pY
              (NativePetersson.toQuadratic Y P pY hpY D hD q) z := by
  let := C
  change BersWeighted.automorphicPeterssonDuality Y pY hpY hΔ P D hD
    ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm
      (canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp hsmooth (β ν.val) (mfderiv 𝓘(ℂ, Space Γ) 𝓘(ℂ, E) β ν.val μ))) q = _
  rw [canonicalBersTangentEquiv_mfderiv_coefficientProjection_nonzero]
  change BersWeighted.automorphicPeterssonDuality Y pY hpY hΔ P D hD
    ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm
      ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν)
        (BersWeighted.automorphicIntegralOperator hΔ (gammaDerivative hΓ ν μ)))) q = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact BersWeighted.automorphicPeterssonDuality_apply_derivative
    Y pY hpY hΔ P D hD (gammaDerivative hΓ ν μ) q

/-- The original extended infinitesimal cometric evaluated on native
quadratic covectors at every original coefficient centre. -/
def originalNativeQuadraticCotangentFunction (q : Q) : ℝ≥0∞ := by
  let := C
  exact originalInfinitesimalCotangentFunction R hg hgenus hΓ hfree hp hsmooth (β ν.val)
    (originalNativeQuadraticCovector R hg hgenus hΓ hfree hp hsmooth ν P D hD q)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
