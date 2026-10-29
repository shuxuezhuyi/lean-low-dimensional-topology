module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCoordinateExpressions
public import LowDimensionalTopology.External.LiZhongQC.Ch02.S11_IntegralOperators
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Source-corrected WP kernels and original coordinate directions

For the source's A(bar ζ,bar z), the inner evaluation is a genuine principal
value; the outer Hilbert operator is evaluated at the lower point bar ζ and
has no singularity on the upper-half-plane support. The mixed B(ζ,bar z)
kernel uses ordinary integrals. Its coefficient arguments follow the first
six-factor term of English (7.59) and LearningMath printed 810, footnote 21:
μ(η) conj(ν(ξ)). English (7.61) prints the opposite arguments; that conflict
is corrected explicitly here. No convergence or source identity is proved.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

/-- The original Cauchy square kernel, with both complex arguments explicit. -/
def cauchySquare (z w : ℂ) : ℂ := 1 / (z - w) ^ 2

/-- Zero extension of an actual upper-half-plane coefficient. -/
def upperExtension (μ : ℍ → ℂ) (z : ℂ) : ℂ :=
  if hz : 0 < z.im then μ ⟨z, hz⟩ else 0

/-- Inner input for the original iterated principal value. -/
def innerInput (μ : ℍ → ℂ) (z : ℍ) : ℂ → ℂ :=
  upperExtension (fun η => μ η * cauchySquare η (conj (z : ℂ)))

/-- Outer input for the Hilbert evaluation at the lower point bar ζ. -/
def outerInput (μ ν : ℍ → ℂ) (z : ℍ) : ℂ → ℂ :=
  upperExtension (fun ξ => μ ξ * LiZhongQC.hilbertHSmooth (innerInput ν z) ξ)

/-- The source A(bar ζ,bar z), with a singular inner PV and lower outer evaluation. -/
def bilinear (μ ν : ℍ → ℂ) (ζ z : ℍ) : ℂ :=
  (Real.pi : ℂ) ^ 2 * LiZhongQC.hilbertHSmooth (outerInput μ ν z) (conj (ζ : ℂ))

/-- The corrected mixed integrand: all three factors cross the half-planes.
The arguments μ(η) conj(ν(ξ)) are forced by English C in (7.59) and are
displayed explicitly in LearningMath printed 810, footnote 21. -/
def sesquilinearIntegrand (μ ν : ℍ → ℂ) (ζ z ξ η : ℍ) : ℂ :=
  cauchySquare (conj (ξ : ℂ)) ζ * cauchySquare (conj (ξ : ℂ)) η *
    cauchySquare η (conj (z : ℂ)) * μ η * conj (ν ξ)

/-- The corrected nonsingular source B(ζ,bar z), using ordinary iterated integrals. -/
def sesquilinear (μ ν : ℍ → ℂ) (ζ z : ℍ) : ℂ :=
  ∫ ξ : ℍ, ∫ η : ℍ, sesquilinearIntegrand μ ν ζ z ξ η ∂flatArea ∂flatArea

/-- Exact convergence of the ordinary inner and outer integrals defining B.
Each `Integrable` also supplies the required a.e. strong measurability. -/
def SesquilinearIntegralExists (μ ν : ℍ → ℂ) (ζ z : ℍ) : Prop :=
  (∀ ξ : ℍ, Integrable (sesquilinearIntegrand μ ν ζ z ξ) flatArea) ∧
  Integrable (fun ξ : ℍ => ∫ η : ℍ, sesquilinearIntegrand μ ν ζ z ξ η ∂flatArea)
    flatArea

/-- Existence is stated for the actual punctured integrals defining hilbertHSmooth. -/
def PrincipalValueExists (input : ℂ → ℂ) (z : ℂ) : Prop :=
  (∀ r : ℝ, 0 < r →
    IntegrableOn (fun ξ => input ξ / (ξ - z) ^ 2) {ξ : ℂ | r < ‖ξ - z‖}) ∧
  Tendsto
    (fun r : ℝ => -(1 / (Real.pi : ℂ)) *
      ∫ ξ in {ξ : ℂ | r < ‖ξ - z‖}, input ξ / (ξ - z) ^ 2)
    (𝓝[>] (0 : ℝ)) (𝓝 (LiZhongQC.hilbertHSmooth input z))

/-- The source four-direction integrand, using A(bar ζ,bar z) and corrected B(ζ,bar z). -/
def four (u v w s : ℍ → ℂ) (ζ z : ℍ) : ℂ :=
  (bilinear u w ζ z + bilinear w u ζ z) *
      conj (bilinear v s ζ z + bilinear s v ζ z) +
    2 * sesquilinear u v ζ z * conj (sesquilinear s w ζ z)

/-- The literal diagonal squared-modulus integrand, with no positivity premise. -/
def energy (μ : ℍ → ℂ) (ζ z : ℍ) : ℝ :=
  ‖bilinear μ μ ζ z + bilinear μ μ ζ z‖ ^ 2 +
    2 * ‖sesquilinear μ μ ζ z‖ ^ 2

theorem energy_nonneg (μ : ℍ → ℂ) (ζ z : ℍ) : 0 ≤ energy μ ζ z := by
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _))

/-- The diagonal source contraction is exactly the real squared-modulus sum. -/
@[simp] theorem four_self (μ : ℍ → ℂ) (ζ z : ℍ) :
    four μ μ μ μ ζ z = (energy μ ζ z : ℂ) := by
  simp only [four, energy, mul_assoc, Complex.mul_conj',
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport NativePetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree
local notation "L" => nativeWeilPeterssonLoweredCurvatureExpression R hp hg hgenus hΓ hfree hsmooth

/-- The actual original harmonic coefficient of the inverse Bers tangent vector. -/
def nativeWeilPeterssonSourceDirection (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (v : E) : ℍ → ℂ := by
  let := C
  exact fun z => (TH ν P F hF hsmooth ((K (β ν.val)).symm v)).val.val z

/-- Full four-direction contraction of the unchanged actual lowered expression. -/
def nativeWeilPeterssonLoweredContraction (a : TeichmullerSpace.{0,0} R)
    (u v w s t : E) : ℂ :=
  ∑ j, ∑ k, ∑ l, ∑ m, L a j k l m t * u j * conj (v k) * w l * conj (s m)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
