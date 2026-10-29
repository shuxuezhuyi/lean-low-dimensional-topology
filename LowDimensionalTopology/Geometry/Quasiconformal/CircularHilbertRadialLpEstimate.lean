module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertLpEstimate

/-!
# Radial principal values for the circular Lp extension

The real-line Riesz family supplies the actual same-Lp circular operator.
The separate circular principal-value bridge identifies its smooth compact
test outputs with genuine radial truncation limits almost everywhere.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Unproved.Quasiconformal

/-- The same Riesz family controls the actual circular Lp extensions, and
the supplied principal-value bridge gives genuine radial convergence to
their actual Lp representatives on all smooth compact tests. -/
theorem exists_radialCircularHilbertLp_of_realRiesz
    (hRiesz : RieszRealHilbertEstimate) (hPV : CircularHilbertPrincipalValue) :
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
  obtain ⟨A, hcont, htwo, hA, hLp⟩ := exists_circularHilbertLp_of_realRiesz hRiesz
  refine ⟨A, hcont, htwo, hA, ?_⟩
  intro p hp
  let : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp)⟩
  obtain ⟨S, hnorm, hExt, htest⟩ := hLp p hp
  refine ⟨S, hnorm, hExt, htest, ?_⟩
  intro φ hφ hcφ
  have hAE : (S ((hφ.continuous.memLp_of_hasCompactSupport hcφ).toLp φ) : ℂ → ℂ)
      =ᵐ[volume] circularHilbertTransform φ := hExt φ hφ hcφ
  filter_upwards [hAE] with ζ hζ
  simpa only [HasCircularHilbertPrincipalValue, hζ] using hPV φ hφ hcφ ζ

end LowDimensionalTopology.Geometry.Quasiconformal
