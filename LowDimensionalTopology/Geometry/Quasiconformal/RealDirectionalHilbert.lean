module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The real and circular Hilbert transforms

The real transform has positive `1 / π` coefficient and denominator
`x - ξ`. The circular transform averages directions over `[0, π]` with
the weight `exp (-iθ)` and coefficient `1 / 2`.

As with Mathlib's other improper-integral definitions, a `limUnder` value
does not assert convergence. The corresponding convergence predicates
below record that separate obligation explicitly.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The real-line truncation with coefficient `1 / π` and denominator `x - ξ`. -/
def realHilbertTruncation (φ : ℝ → ℂ) (ξ ε : ℝ) : ℂ :=
  (1 / (Real.pi : ℂ)) *
    ∫ x in {x : ℝ | ε < |x - ξ|}, φ x / ((x - ξ : ℝ) : ℂ)

/-- The real-line Hilbert transform, initially used on smooth compact tests. -/
def realHilbertTransform (φ : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (realHilbertTruncation φ ξ)

/-- Existence of the literal principal value at one real point. -/
def HasRealHilbertPrincipalValue (φ : ℝ → ℂ) (ξ : ℝ) : Prop :=
  Tendsto (realHilbertTruncation φ ξ) (𝓝[>] (0 : ℝ))
    (𝓝 (realHilbertTransform φ ξ))

/-- The Hilbert transform along the line through `ζ` with angle `θ`. -/
def directionalHilbertTransform (φ : ℂ → ℂ) (θ : ℝ) (ζ : ℂ) : ℂ :=
  realHilbertTransform
    (fun x : ℝ => φ ((x : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ)) 0

/-- The circular directional average `S`. -/
def circularHilbertTransform (φ : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∫ θ in (0 : ℝ)..Real.pi,
    directionalHilbertTransform φ θ ζ * Complex.exp (-((θ : ℂ) * I))

/-- The radial truncation in the second displayed definition of `S`. -/
def circularHilbertTruncation (φ : ℂ → ℂ) (ζ : ℂ) (ε : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ z in {z : ℂ | ε < ‖z‖}, φ (z + ζ) / (z * (‖z‖ : ℂ))

/-- The planar principal-value expression for the same circular operator.
Its agreement with the directional average is a separate analytic claim. -/
def radialCircularHilbertTransform (φ : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (circularHilbertTruncation φ ζ)

/-- Convergence of the radial truncations to the directional average `S`. -/
def HasCircularHilbertPrincipalValue (φ : ℂ → ℂ) (ζ : ℂ) : Prop :=
  Tendsto (circularHilbertTruncation φ ζ) (𝓝[>] (0 : ℝ))
    (𝓝 (circularHilbertTransform φ ζ))

end LowDimensionalTopology.Geometry.Quasiconformal
