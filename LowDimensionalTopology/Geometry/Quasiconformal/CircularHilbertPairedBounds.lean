module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealHilbertPrincipalValue
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Uniform cancellation bounds for the circular Hilbert rays

Pairing the two opposite rays removes the pole before angular integration.
The bounds and radial support are uniform in the direction angle.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped NNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- A global Lipschitz bound gives a uniform bound for every paired ray. -/
theorem norm_realHilbertPairedKernel_affineLine_le {φ : ℂ → ℂ} {L : ℝ≥0}
    (hL : LipschitzWith L φ) (θ : ℝ) (ζ : ℂ) {r : ℝ} (hr : r ≠ 0) :
    ‖realHilbertPairedKernel
      (fun x : ℝ => φ ((x : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ)) 0 r‖ ≤ 2 * L := by
  let u := Complex.exp ((θ : ℂ) * I)
  have hu : ‖u‖ = 1 := by simp [u, Complex.norm_exp]
  have hd : dist ((r : ℂ) * u + ζ) (((-r : ℝ) : ℂ) * u + ζ) = 2 * |r| := by
    rw [dist_eq_norm]
    have heq : (r : ℂ) * u + ζ - (((-r : ℝ) : ℂ) * u + ζ) =
        (2 : ℂ) * (r : ℂ) * u := by
      push_cast
      ring
    rw [heq, norm_mul, norm_mul, hu]
    simp
  have hb := hL.dist_le_mul ((r : ℂ) * u + ζ) (((-r : ℝ) : ℂ) * u + ζ)
  rw [dist_eq_norm, hd] at hb
  rw [realHilbertPairedKernel_of_ne _ 0 hr]
  simp only [zero_add, zero_sub, norm_smul, Real.norm_eq_abs, abs_inv]
  change |r|⁻¹ * ‖φ ((r : ℂ) * u + ζ) - φ (((-r : ℝ) : ℂ) * u + ζ)‖ ≤ _
  calc
    _ ≤ |r|⁻¹ * ((L : ℝ) * (2 * |r|)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg r))
    _ = 2 * L := by
      field_simp [abs_ne_zero.mpr hr]

/-- One finite radial bound works for every affine line through the same point. -/
theorem exists_uniform_affineLine_paired_support {φ : ℂ → ℂ}
    (hc : HasCompactSupport φ) (ζ : ℂ) :
    ∃ R : ℝ, 0 < R ∧ ∀ (θ r : ℝ), R ≤ |r| →
      realHilbertPairedKernel
        (fun x : ℝ => φ ((x : ℂ) * Complex.exp ((θ : ℂ) * I) + ζ)) 0 r = 0 := by
  obtain ⟨R₀, hR₀, hbound⟩ := hc.isCompact.isBounded.exists_pos_norm_le
  refine ⟨R₀ + ‖ζ‖ + 1, by positivity, ?_⟩
  intro θ r hr
  let u := Complex.exp ((θ : ℂ) * I)
  have hu : ‖u‖ = 1 := by simp [u, Complex.norm_exp]
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, abs_zero] at hr
    linarith [norm_nonneg ζ]
  have hz (t : ℝ) (ht : |t| = |r|) : φ ((t : ℂ) * u + ζ) = 0 := by
    by_contra h
    have hb := hbound ((t : ℂ) * u + ζ) (subset_tsupport φ h)
    have hn : |r| ≤ ‖(t : ℂ) * u + ζ‖ + ‖ζ‖ := by
      calc
        |r| = ‖(t : ℂ) * u‖ := by rw [norm_mul, hu]; simpa using ht.symm
        _ = ‖((t : ℂ) * u + ζ) - ζ‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖(t : ℂ) * u + ζ‖ + ‖ζ‖ := norm_sub_le _ _
    linarith
  rw [realHilbertPairedKernel_of_ne _ 0 hr0]
  simp only [zero_add, zero_sub]
  change r⁻¹ • (φ ((r : ℂ) * u + ζ) - φ (((-r : ℝ) : ℂ) * u + ζ)) = 0
  rw [hz r rfl, hz (-r) (abs_neg r), sub_self, smul_zero]

end LowDimensionalTopology.Geometry.Quasiconformal
