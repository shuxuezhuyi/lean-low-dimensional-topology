module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicBeltrami
public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalHalfPlaneSolution
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Ring

/-! # The same canonical harmonic Beltrami family and its explicit Eichler jets -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane ComplexConjugate BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces LiZhongQC QuadraticBergman
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

/-- The literal original harmonic coefficient, before taking any AE class. -/
def harmonicPlane (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℂ) : ℂ :=
  (z.im : ℂ) ^ 2 * conj (uniformizedQuadratic R p q z)

theorem harmonicPlane_eq_coefficient
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    harmonicPlane R p q z = NativeHarmonicBeltrami.coefficient R p q z :=
  (NativeHarmonicBeltrami.coefficient_eq_uniformized R p q z).symm

/-- The existing normalized symmetric solution for the actual coefficient t times ν. -/
def canonicalFamily (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (t : ℂ) : ℂ → ℂ :=
  fMuSym (fun z => t * harmonicPlane R p q z)

/-- The actual finite source-coordinate family, before restricting to a coordinate axis. -/
def coordinateFamily {n : ℕ}
    (q : Fin n → HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (t : Fin n → ℂ) : ℂ → ℂ :=
  fMuSym (fun z => ∑ i, t i * harmonicPlane R p (q i) z)

theorem coordinateFamily_axis {n : ℕ}
    (q : Fin n → HolomorphicQuadraticDifferential R.toRiemannAtlas) (j : Fin n) (a : ℂ) :
    coordinateFamily R p q (Pi.single j a) = canonicalFamily R p (q j) a := by
  classical
  unfold coordinateFamily canonicalFamily
  congr 1
  funext z
  simp [Pi.single_apply]

theorem canonicalFamily_zero (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    canonicalFamily R p q 0 = id := by
  have he : symmetricExtension (0 : ℂ → ℂ) = 0 := by
    funext z
    simp only [symmetricExtension, Pi.zero_apply, map_zero, ite_self]
  unfold canonicalFamily
  simp only [zero_mul]
  change normalizedSolution (symmetricExtension (0 : ℂ → ℂ)) = id
  rw [he, bB_l_normalizedSolution_zero]

variable {R p}

/-- The full real-linear parameter jet of the original normalized map. -/
def eichlerPointJet (ψ : ℂ → ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.mul ℝ ℂ
      ((z.im : ℂ) ^ 2 * conj (deriv (deriv ψ) z) -
        Complex.I * z.im * conj (deriv ψ z) - conj (ψ z) / 2) -
    (ContinuousLinearMap.mul ℝ ℂ (ψ z / 2)).comp Complex.conjCLE.toContinuousLinearMap

/-- Its actual spatial z-derivative jet, retaining both complex parameter directions. -/
def eichlerDzJet (ψ : ℂ → ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.mul ℝ ℂ
      (-Complex.I * z.im * conj (deriv (deriv ψ) z) - conj (deriv ψ z) / 2) -
    (ContinuousLinearMap.mul ℝ ℂ (deriv ψ z / 2)).comp Complex.conjCLE.toContinuousLinearMap

/-- The elementary cancellation holds for every complex parameter vector. -/
theorem eichlerJet_im_eq (ψ : ℂ → ℂ) (z a : ℂ) :
    (eichlerPointJet ψ z a).im = z.im * (eichlerDzJet ψ z a).re := by
  simp [eichlerPointJet, eichlerDzJet, ContinuousLinearMap.mul_apply',
    Complex.mul_re, Complex.mul_im, pow_two]
  ring

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
