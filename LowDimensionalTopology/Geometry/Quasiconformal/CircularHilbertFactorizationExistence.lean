module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertFactorization
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertLpConstruction

/-!
# Actual circular Lp witnesses with the planar factorization

The actual radial operator family supplies bounded circular extensions.
Their norms, compact-test values, and genuine radial limits are retained
when adjoining the planar factorization.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Unproved.Quasiconformal

/-- There are actual same-plane Lp operators with the
original norm bounds, compact-test extension, genuine radial limits,
and factorization on the original compact smooth test classes. -/
theorem exists_factored_radialCircularHilbertLp :
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
          (∀ (φ : ℂ → ℂ)
              (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
              (hcφ : HasCompactSupport φ),
            ∀ᵐ ζ : ℂ ∂volume,
              Tendsto (circularHilbertTruncation φ ζ) (𝓝[>] (0 : ℝ))
                (𝓝 ((S ((hφ.continuous.memLp_of_hasCompactSupport hcφ).toLp φ) :
                  ℂ → ℂ) ζ))) ∧
          ∀ (φ : ℂ → ℂ)
              (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
              (hcφ : HasCompactSupport φ),
            let f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) :=
              (hφ.continuous.memLp_of_hasCompactSupport hcφ).toLp φ
            hilbertLp (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hp) f = -S (S f) := by
  obtain ⟨A, hAc, hA2, hA, hfamily⟩ := radialCircularHilbertLp_exists
  refine ⟨A, hAc, hA2, hA, ?_⟩
  intro p hp
  let : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal
        (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp)⟩
  dsimp only
  obtain ⟨S, hbound, hS, htests, hradial⟩ := hfamily p hp
  refine ⟨S, hbound, hS, htests, hradial, ?_⟩
  intro φ hφ hcφ
  exact circularHilbertFactorization p hp S hS φ hφ hcφ

end LowDimensionalTopology.Geometry.Quasiconformal
