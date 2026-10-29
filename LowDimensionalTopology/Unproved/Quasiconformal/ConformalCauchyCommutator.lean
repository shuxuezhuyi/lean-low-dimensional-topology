module

public import LowDimensionalTopology.External.LiZhongQC.Ch03.S15_Distortion

/-!
# Ordinary conformal Cauchy commutator differentiation

This proposition concerns one fixed conformal map and one locally regular L2
input. Importing it supplies no proof. First-order ordinary integrability and
the regular-kernel L2 condition are explicit prerequisites.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Unproved.Quasiconformal

open LiZhongQC

/-- Differentiating an ordinary Cauchy pullback after subtracting the ordinary
normalized potential gives the regular conformal kernel correction. The input
is locally C1 on the upper half-plane and belongs to planar L2. All first-order
integrals and the regular-kernel L2 condition are explicit prerequisites. -/
def ConformalCauchyCommutatorDifferentiation : Prop :=
  ∀ (F h : ℂ → ℂ) (a : ℂ),
    IsKQCNormalizedPlane F 3 → DifferentiableOn ℂ F upperHalf → a ∈ lowerHalf →
      MemLp h 2 (volume : Measure ℂ) → ContDiffOn ℝ 1 h upperHalf →
      (∀ y ∉ upperHalf, h y = 0) →
      (∀ ξ : ℍ, Integrable
        (fun y : ℂ => h y * (1 / (y - ξ) - 1 / (y - a))) volume) →
      (∀ ξ : ℍ, IntegrableOn
        (fun y : ℂ => h y * deriv F y / (F y - F ξ)) upperHalf) →
      ∀ x : ℍ,
        MemLp (upperHalf.indicator (fun y : ℂ =>
          deriv F x * deriv F y / (F x - F y) ^ 2 - 1 / ((x : ℂ) - y) ^ 2))
          2 (volume : Measure ℂ) →
        let U := fun v : ℂ => -(1 / Real.pi : ℂ) *
          ∫ y : ℂ in upperHalf, h y * deriv F y / (F y - F v)
        let P := fun v : ℂ => -(1 / Real.pi : ℂ) *
          ∫ y : ℂ, h y * (1 / (y - v) - 1 / (y - a))
        DifferentiableAt ℝ (fun v : ℂ => U v - P v) (x : ℂ) ∧
          dz (fun v : ℂ => U v - P v) x = -(1 / Real.pi : ℂ) *
            ∫ y : ℂ in upperHalf, h y *
              (deriv F x * deriv F y / (F x - F y) ^ 2 - 1 / ((x : ℂ) - y) ^ 2)

end LowDimensionalTopology.Unproved.Quasiconformal
