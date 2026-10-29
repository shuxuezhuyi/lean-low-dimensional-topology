/-
Copyright (c) 2026 Wu Xiaobin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wu Xiaobin (original unfolding argument)
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.MeasurablePoincareSeed
public import LowDimensionalTopology.Geometry.Teichmuller.RawAutomorphicKernelInvariant
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBergmanProjection

/-!
# The original rough-coefficient seed expands to the literal Bergman integral

The same coefficient remains inside the given fundamental-domain integral.
The full original matrix sum has its true ineffective multiplicity; the full
actual projective-image series cancels precisely that same positive integer.

The unfolding argument adapts `AutomorphicPoincare.seed_matrix_sum` and
`h36p_c_unfold_int` from Wu Xiaobin's Li-Zhong-QC-formalization, commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0),
`LiZhongQC/Ch11/S36_Hamilton.lean`. The raw coefficient is not assumed
holomorphic, and no reproducing formula for that coefficient is used.
See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AutomorphicPoincare

open Surfaces LiZhongQC QuadraticBergman ProjectivePoincare

private theorem raw_kernel_integrand_eq (f : ℂ → ℂ) (z ζ : ℂ) :
    (ζ.im : ℂ) ^ 2 * f ζ * conj (halfPlaneQuadraticKernel z ζ) =
      (12 / Real.pi : ℂ) * h36p_c_K f ζ z := by
  unfold halfPlaneQuadraticKernel
  simp only [map_div₀, map_pow, map_sub, Complex.conj_conj, map_ofNat,
    Complex.conj_ofReal]
  have hp : (z - conj ζ) ^ 4 = (conj ζ - z) ^ 4 := by ring
  rw [hp]
  unfold h36p_c_K
  ring

private theorem raw_kernel_integrableOn
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict upperHalf))
    (ha : ∀ A ∈ Γ, ∀ z ∈ upperHalf,
      f (h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = f z)
    (hb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict upperHalf), ‖f z‖ * z.im ^ 2 ≤ M)
    {z : ℂ} (hz : z ∈ upperHalf) :
    IntegrableOn (fun ζ => h36p_c_K f ζ z) upperHalf := by
  have hi := MeasurableQuadratic.bergman_integrable f hf ha hb hz
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hc : (Real.pi / 12 : ℂ) * (12 / Real.pi : ℂ) = 1 := by field_simp
  apply IntegrableOn.congr_fun_ae (hi.const_mul (Real.pi / 12 : ℂ))
  exact Eventually.of_forall fun ζ => by
    dsimp only
    rw [raw_kernel_integrand_eq f z ζ, ← mul_assoc, hc, one_mul]

/-- The original matrix group sums the same literal raw seed to the literal
Bergman integral with precisely its actual ineffective-kernel multiplicity. -/
theorem raw_seed_matrix_sum
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict upperHalf))
    (ha : ∀ A ∈ Γ, ∀ z ∈ upperHalf,
      f (h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = f z)
    (hb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict upperHalf), ‖f z‖ * z.im ^ 2 ≤ M)
    {z : ℂ} (hz : z ∈ upperHalf) :
    h36p_theta Γ (seed F f) z =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) * MeasurableQuadratic.bergman f z := by
  have hGi := raw_kernel_integrableOn hf ha hb hz
  have hU := h36p_c_unfold_int hΓ hF hGi
  let c : ℂ := 12 / Real.pi
  have hterm : ∀ A : Γ,
      c * (∫ ζ in F, h36p_c_K f ζ (h36p_m A.val z)) /
        ((A.val 1 0 : ℂ) * z + A.val 1 1) ^ 4 =
      c * ∫ ζ in F, h36p_c_K f ζ (h36p_m A.val z) /
        ((A.val 1 0 : ℂ) * z + A.val 1 1) ^ 4 := by
    intro A
    rw [mul_div_assoc, integral_div]
  have hterm2 : ∀ A : Γ,
      c * ∫ ζ in F, h36p_c_K f ζ (h36p_m A.val⁻¹ z) /
        (((A.val⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
          (A.val⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) ^ 4 =
      c * ∫ ζ in F, ((‖(A.val 1 0 : ℂ) * ζ + A.val 1 1‖⁻¹ ^ 4 : ℝ) : ℂ) *
        h36p_c_K f (h36p_m A.val ζ) z := by
    intro A
    congr 1
    exact setIntegral_congr_fun hF.2.1 fun ζ hζ =>
      rawAutomorphicKernel_invariant ha A.property (hF.1 hζ) hz
  have hre := (Equiv.inv Γ).tsum_eq (fun A : Γ => c * ∫ ζ in F,
    h36p_c_K f ζ (h36p_m A.val z) / ((A.val 1 0 : ℂ) * z + A.val 1 1) ^ 4)
  have hβ : c * (∫ ζ in upperHalf, h36p_c_K f ζ z) = MeasurableQuadratic.bergman f z :=
    seed_eq_kernel upperHalf f z
  change (∑' A : Γ, c * (∫ ζ in F, h36p_c_K f ζ (h36p_m A.val z)) /
    ((A.val 1 0 : ℂ) * z + A.val 1 1) ^ 4) = _
  rw [tsum_congr hterm, ← hre]
  change (∑' A : Γ, c * ∫ ζ in F, h36p_c_K f ζ (h36p_m A.val⁻¹ z) /
    (((A.val⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) * z +
      (A.val⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1) ^ 4) = _
  rw [tsum_congr hterm2, tsum_mul_left, hU]
  calc
    c * ((Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) *
        ∫ ζ in upperHalf, h36p_c_K f ζ z) =
        (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) *
          (c * ∫ ζ in upperHalf, h36p_c_K f ζ z) := by ring
    _ = _ := by rw [hβ]

/-- Every original rough automorphic coefficient on the same compact source
has its literal Bergman integral equal to the full actual projective series
of its unchanged seed on any given fundamental domain. -/
theorem projective_raw_seed_eq_bergman
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {p : ℍ → X} (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict upperHalf))
    (ha : ∀ A ∈ Γ, ∀ z ∈ upperHalf,
      f (h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = f z)
    (hb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict upperHalf), ‖f z‖ * z.im ^ 2 ≤ M)
    {z : ℂ} (hz : z ∈ upperHalf) :
    ProjectivePoincare.series Γ (seed F f) z = MeasurableQuadratic.bergman f z := by
  have hseed := source_seed_differentiableOn_and_phiArea_lt_top R hΓ hp hF hf hb
  have hm : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℂ) ≠ 0 := by
    exact_mod_cast (h36p_mult_pos (Γ := Γ)).ne'
  have he := raw_seed_matrix_sum hΓ hF hf ha hb hz
  rw [ProjectivePoincare.matrix_sum_eq_card_mul Γ hΓ hseed.1 hseed.2 hz] at he
  exact mul_left_cancel₀ hm he

end LowDimensionalTopology.Geometry.Teichmuller.AutomorphicPoincare
