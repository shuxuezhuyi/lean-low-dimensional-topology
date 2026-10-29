module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealDirectionalHilbert
public import LowDimensionalTopology.Geometry.Quasiconformal.HilbertLpOperator

/-!
# The unfinished and omitted Hilbert-transform assertions

The Riesz estimate, circular estimate and factorization are recorded as
unproved propositions with their exact operators and constants.
Importing them supplies no proofs or axioms.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff
open LowDimensionalTopology.Geometry.Quasiconformal

namespace LowDimensionalTopology.Unproved.Quasiconformal

/-- The full real-line Riesz assertion with one specified family of constants.
The notes' proof is incomplete. Complex tests include the real-valued case
via the usual embedding. The principal-value convergence is explicit. -/
def RealHilbertEstimate (A : ℝ → ℝ) : Prop :=
  ContinuousOn A (Ici 2) ∧ A 2 = 1 ∧
    ∀ (p : ℝ), 2 ≤ p → ∀ (φ : ℝ → ℂ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∀ ξ : ℝ, HasRealHilbertPrincipalValue φ ξ) ∧
        MemLp (realHilbertTransform φ) (ENNReal.ofReal p) (volume : Measure ℝ) ∧
        (eLpNorm (realHilbertTransform φ) (ENNReal.ofReal p)
          (volume : Measure ℝ)).toReal ≤
          A p * (eLpNorm φ (ENNReal.ofReal p) (volume : Measure ℝ)).toReal

/-- The real-line Riesz estimate, without an asserted proof. -/
def RieszRealHilbertEstimate : Prop :=
  ∃ A : ℝ → ℝ, RealHilbertEstimate A

/-- The equality of the two displayed definitions of `S`, including genuine
radial principal-value convergence for every smooth compact planar test. -/
def CircularHilbertPrincipalValue : Prop :=
  ∀ (φ : ℂ → ℂ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∀ ζ : ℂ, HasCircularHilbertPrincipalValue φ ζ

/-- An actual Lp continuous-linear operator extends the literal directional
average on every smooth compact test. Input Lp membership is derived from
the test's continuity and compact support. -/
def IsCircularHilbertLpExtension (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (S : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) : Prop :=
  ∀ (φ : ℂ → ℂ)
      (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
      (hcompact : HasCompactSupport φ),
    (S ((hφ.continuous.memLp_of_hasCompactSupport hcompact).toLp φ) : ℂ → ℂ)
      =ᵐ[volume] circularHilbertTransform φ

/-- The unproved circular Hilbert estimate with the exact `π A_p / 2` bound
and the extension on the same planar Lp space, conditional on the stated
real-line Riesz estimate. -/
def CircularHilbertLpEstimate : Prop :=
  ∀ (A : ℝ → ℝ), RealHilbertEstimate A → ∀ (p : ℝ) (hp : 2 ≤ p),
    let : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp)⟩
    ∃ S : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →L[ℂ]
        Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ),
      ‖S‖ ≤ Real.pi / 2 * A p ∧
      IsCircularHilbertLpExtension p S ∧
      ∀ (φ : ℂ → ℂ),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
          MemLp (circularHilbertTransform φ) (ENNReal.ofReal p)
              (volume : Measure ℂ) ∧
          (eLpNorm (circularHilbertTransform φ) (ENNReal.ofReal p)
            (volume : Measure ℂ)).toReal ≤
            (Real.pi / 2 * A p) *
              (eLpNorm φ (ENNReal.ofReal p) (volume : Measure ℂ)).toReal

/-- The unproved factorization of the planar Hilbert transform.
The second `S` acts by the actual Lp extension, since its input need not
have compact support. Equality holds in the original planar Lp space.
`hilbertLp` is the accepted actual extension of the planar transform `T`,
with coefficient `-1/π` and squared Cauchy denominator. -/
def CircularHilbertFactorization : Prop :=
  ∀ (p : ℝ) (hp : 2 ≤ p),
    let : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp)⟩
    ∀ S : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →L[ℂ]
        Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ),
      IsCircularHilbertLpExtension p S →
      ∀ (φ : ℂ → ℂ)
          (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
          (hcompact : HasCompactSupport φ),
        let f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) :=
          (hφ.continuous.memLp_of_hasCompactSupport hcompact).toLp φ
        hilbertLp (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hp) f = -S (S f)

end LowDimensionalTopology.Unproved.Quasiconformal
