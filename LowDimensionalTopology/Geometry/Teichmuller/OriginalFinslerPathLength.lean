module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalInfinitesimalDistanceDescent
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersProjectionTopology
public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealTangent
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Original infinitesimal path length and its path infimum

Choose genuine coefficient presentations using the proved surjectivity of
the original projection and its actual derivative. The explicit descent
premise proves agreement with every such presentation. Path velocities are
the real manifold derivatives in the same original atlas.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

local notation "π" => coefficientProjectionBall R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "E" => Fin (3 * g - 3) → ℂ

/-- The actual distance variation evaluated using genuine coefficient
presentations of the original point and its Bers tangent coordinate. -/
def originalInfinitesimalFunctionInBersFrame
    (a : TeichmullerSpace R) (w : BersWeighted.Automorphic Γ) : ℝ :=
  let ξ := (coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp a).choose
  let η := (nonzeroBersDerivative_surjective R hp hg hgenus hΓ ξ w).choose
  coefficientInfinitesimalTeichmullerFunction R hg hgenus hΓ hfree hp ξ η

/-- Under the explicit descent premise, every actual coefficient presentation
recovers the same value, including its actual nonzero projection derivative. -/
theorem originalInfinitesimalFunctionInBersFrame_projection
    (hdesc : Unproved.Teichmuller.OriginalInfinitesimalDistanceDescent
      R hg hgenus hΓ hfree hp) (ξ : Ball Γ) (η : Space Γ) :
    originalInfinitesimalFunctionInBersFrame R hg hgenus hΓ hfree hp
      (π ξ) (nonzeroBersDerivative R hp hg hgenus hΓ ξ η) =
        coefficientInfinitesimalTeichmullerFunction R hg hgenus hΓ hfree hp ξ η := by
  have hξ := coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp (π ξ)
  have hη := nonzeroBersDerivative_surjective R hp hg hgenus hΓ hξ.choose
    (nonzeroBersDerivative R hp hg hgenus hΓ ξ η)
  exact hdesc hξ.choose ξ hη.choose η hξ.choose_spec hη.choose_spec

variable (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth

/-- The distance variation on the actual original complex tangent fibre,
using the derivative of its actual Bers chart. -/
def originalInfinitesimalTangentFunction (a : TeichmullerSpace R) :
    letI := C
    TangentSpace 𝓘(ℂ, E) a → ℝ := by
  let := C
  exact fun v => originalInfinitesimalFunctionInBersFrame R hg hgenus hΓ hfree hp a
    (canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth a v)

/-- On an actual projection derivative this tangent function is precisely
the original directional distance formula, under its explicit descent premise. -/
theorem originalInfinitesimalTangentFunction_projection_derivative
    (hdesc : Unproved.Teichmuller.OriginalInfinitesimalDistanceDescent
      R hg hgenus hΓ hfree hp) (ξ : Ball Γ) (η : Space Γ) :
    letI := C
    originalInfinitesimalTangentFunction R hg hgenus hΓ hfree hp hsmooth
      (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ξ.val)
      (mfderiv 𝓘(ℂ, Space Γ) 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp)
        ξ.val η) =
          coefficientInfinitesimalTeichmullerFunction R hg hgenus hΓ hfree hp ξ η := by
  let := C
  dsimp only [originalInfinitesimalTangentFunction]
  rw [canonicalBersTangentEquiv_mfderiv_coefficientProjection_nonzero,
    coefficientProjection_ball]
  exact originalInfinitesimalFunctionInBersFrame_projection
    R hg hgenus hΓ hfree hp hdesc ξ η

/-- The integral of the actual infinitesimal function on the real velocity
of a curve in the original Teichmuller space. -/
def originalFinslerPathLength (c : ℝ → TeichmullerSpace R) : ℝ := by
  let := C
  exact ∫ t in (0 : ℝ)..1,
    originalInfinitesimalTangentFunction R hg hgenus hΓ hfree hp hsmooth (c t)
      (nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth (c t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1))

/-- A finite subdivision of the unit interval on each closed subinterval of
which the same original curve is smooth. -/
def IsOriginalPiecewiseSmoothPath (c : ℝ → TeichmullerSpace R) : Prop :=
  letI := C
  ∃ (n : ℕ) (t : Fin (n + 1) → ℝ),
    StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      ∀ i : Fin n, ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c
        (Icc (t i.castSucc) (t i.succ))

/-- The infimum of the original infinitesimal lengths of all piecewise
smooth paths with the specified original marked endpoints. -/
def originalFinslerPathDistance (a b : TeichmullerSpace R) : ℝ :=
  sInf {L : ℝ | ∃ c : ℝ → TeichmullerSpace R,
    IsOriginalPiecewiseSmoothPath R hg hgenus hΓ hfree hp hsmooth c ∧
    c 0 = a ∧ c 1 = b ∧
    L = originalFinslerPathLength R hg hgenus hΓ hfree hp hsmooth c}

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
