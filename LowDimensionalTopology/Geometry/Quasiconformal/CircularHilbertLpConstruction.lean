module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertLpExistence
public import LowDimensionalTopology.Geometry.Quasiconformal.RealHilbertRiesz

/-!
# Construction of circular Hilbert Lp operators

The proved real-line estimate supplies circular Hilbert operators on every
planar Lp space with exponent at least two. Their smooth compact test outputs
agree almost everywhere with the actual radial principal values.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Unproved.Quasiconformal

/-- The same continuous constant family gives actual circular Hilbert
operators, their test estimates, and genuine radial principal values. -/
theorem radialCircularHilbertLp_exists :
    ∃ A : ℝ → ℝ, ContinuousOn A (Ici 2) ∧ A 2 = 1 ∧ RealHilbertEstimate A ∧
      ∀ (p : ℝ) (hp : 2 ≤ p),
        let : Fact (1 ≤ ENNReal.ofReal p) :=
          ⟨by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal
              (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp)⟩
        ∃ S : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →L[ℂ]
            Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ),
          ‖S‖ ≤ Real.pi / 2 * A p ∧ IsCircularHilbertLpExtension p S ∧
          (∀ (φ : ℂ → ℂ),
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
              MemLp (circularHilbertTransform φ) (ENNReal.ofReal p)
                  (volume : Measure ℂ) ∧
                (eLpNorm (circularHilbertTransform φ) (ENNReal.ofReal p)
                  (volume : Measure ℂ)).toReal ≤
                  (Real.pi / 2 * A p) *
                    (eLpNorm φ (ENNReal.ofReal p) (volume : Measure ℂ)).toReal) ∧
          ∀ (φ : ℂ → ℂ)
              (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
              (hcφ : HasCompactSupport φ),
            ∀ᵐ ζ : ℂ ∂volume,
              Tendsto (circularHilbertTruncation φ ζ) (𝓝[>] (0 : ℝ))
                (𝓝 ((S ((hφ.continuous.memLp_of_hasCompactSupport hcφ).toLp φ) :
                  ℂ → ℂ) ζ)) := by
  exact exists_radialCircularHilbertLp rieszRealHilbertEstimate


end LowDimensionalTopology.Geometry.Quasiconformal
