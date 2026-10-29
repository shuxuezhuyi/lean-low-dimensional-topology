module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyCosets
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.NormNum

/-!
# Finite norm-integral bounds for actual angular coset coefficients

These intermediate estimates explicitly take uniqueness of the nonzero
coset coefficient at each point. That geometric input concerns the actual
coefficients and must be supplied by the original covering and its collar.
Each kernel term has genuine absolute integrability before finite linearity
or the bounded-partial-sum criterion is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

variable (θ : Width) (Γ : Subgroup Deck) (s : ℝ)

local notation "Cosets" => Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))

/-- Pointwise uniqueness of the nonzero actual coset coefficient gives a uniform
bound on every finite sum of the genuine kernel norm integrals. -/
theorem sum_integral_norm_rightCoset_kernel_le
    (hsep : ∀ ζ : ℂ, ∀ u v : Cosets,
      rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0 →
      rightCosetInfinitesimalZeroExtension θ Γ s v ζ ≠ 0 → u = v)
    (F : Finset Cosets) (z : ℂ) :
    ∑ u ∈ F, ∫ ζ : ℂ, ‖rightCosetInfinitesimalZeroExtension θ Γ s u ζ *
      Quasiconformal.firstVariationKernel z ζ‖ ≤
    (1 / (4 * (θ : ℝ))) * ∫ ζ : ℂ, ‖Quasiconformal.firstVariationKernel z ζ‖ := by
  classical
  have hB : 0 ≤ 1 / (4 * (θ : ℝ)) :=
    one_div_nonneg.mpr (mul_nonneg (by norm_num) θ.property.1.le)
  have hpoint (ζ : ℂ) :
      ∑ u ∈ F, ‖rightCosetInfinitesimalZeroExtension θ Γ s u ζ *
        Quasiconformal.firstVariationKernel z ζ‖ ≤
      (1 / (4 * (θ : ℝ))) * ‖Quasiconformal.firstVariationKernel z ζ‖ := by
    by_cases h : ∃ u ∈ F, rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0
    · obtain ⟨u, hu, hne⟩ := h
      rw [Finset.sum_eq_single u]
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (norm_rightCosetInfinitesimalZeroExtension_le θ Γ s u ζ) (norm_nonneg _)
      · intro v _hF hvu
        have hv : rightCosetInfinitesimalZeroExtension θ Γ s v ζ = 0 := by
          by_contra hnv
          exact hvu (hsep ζ v u hnv hne)
        rw [hv, zero_mul, norm_zero]
      · intro hnot
        exact (hnot hu).elim
    · have hz : ∑ u ∈ F, ‖rightCosetInfinitesimalZeroExtension θ Γ s u ζ *
          Quasiconformal.firstVariationKernel z ζ‖ = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        have hzero : rightCosetInfinitesimalZeroExtension θ Γ s u ζ = 0 := by
          by_contra hne
          exact h ⟨u, hu, hne⟩
        rw [hzero, zero_mul, norm_zero]
      rw [hz]
      exact mul_nonneg hB (norm_nonneg _)
  have hterm (u : Cosets) : Integrable (fun ζ : ℂ =>
      ‖rightCosetInfinitesimalZeroExtension θ Γ s u ζ *
        Quasiconformal.firstVariationKernel z ζ‖) (volume : Measure ℂ) :=
    (integrable_rightCosetInfinitesimalZeroExtension_mul_firstVariationKernel θ Γ s u z).norm
  have hkernel : Integrable (fun ζ : ℂ => ‖Quasiconformal.firstVariationKernel z ζ‖)
      (volume : Measure ℂ) := (LiZhongQC.ah_ker_integrable z).norm
  calc
    _ = ∫ ζ : ℂ, ∑ u ∈ F, ‖rightCosetInfinitesimalZeroExtension θ Γ s u ζ *
        Quasiconformal.firstVariationKernel z ζ‖ :=
      (integral_finsetSum F (fun u _ => hterm u)).symm
    _ ≤ ∫ ζ : ℂ, (1 / (4 * (θ : ℝ))) * ‖Quasiconformal.firstVariationKernel z ζ‖ :=
      integral_mono (integrable_finsetSum F (fun u _ => hterm u))
        (hkernel.const_mul _) hpoint
    _ = _ := integral_const_mul _ _

/-- The finite actual norm-integral bounds imply summability, without a
summability or convergence hypothesis. -/
theorem summable_integral_norm_rightCoset_kernel
    (hsep : ∀ ζ : ℂ, ∀ u v : Cosets,
      rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0 →
      rightCosetInfinitesimalZeroExtension θ Γ s v ζ ≠ 0 → u = v) (z : ℂ) :
    Summable (fun u : Cosets => ∫ ζ : ℂ,
      ‖rightCosetInfinitesimalZeroExtension θ Γ s u ζ *
        Quasiconformal.firstVariationKernel z ζ‖) := by
  exact summable_of_sum_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (fun F => sum_integral_norm_rightCoset_kernel_le θ Γ s hsep F z)

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
