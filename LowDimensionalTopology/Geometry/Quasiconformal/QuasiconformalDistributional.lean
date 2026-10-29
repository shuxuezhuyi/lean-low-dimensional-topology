/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.WirtingerWeakApproximation
public import Mathlib.Tactic.Linarith

/-!
# Analytic Definition A-prime with its genuine local L1 contract

The weak predicate uses actual compact smooth tests, with local integrability
of both derivative functions. Homeomorphism and orientation are explicit.
Neither ACL nor total differentiability nor an analytic/geometric equivalence
is part of this definition: these are conclusions of the proofs below.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The fixed-K form of Analytic Definition A-prime, retaining a genuine
orientation-preserving homeomorphism and actual local L1 weak derivatives. -/
def IsDistributionallyKQuasiconformal (f : ℂ → ℂ) (U : Set ℂ) (K : ℝ) : Prop :=
  IsOpen U ∧ 1 ≤ K ∧ LiZhongQC.IsHomeomorphOnto f U (f '' U) ∧
    LiZhongQC.IsSensePreserving f U ∧
      ∃ g h : ℂ → ℂ, HasDistributionalWirtingerDerivatives f g h U ∧
        ∀ᵐ z ∂(volume.restrict U),
          ‖g z‖ + ‖h z‖ ≤ K * (‖g z‖ - ‖h z‖)

/-- Genuine geometric and distributional quasiconformality agree with the same K.
The reverse direction proves ACL and actual total differentiability a.e.; they
are not hypotheses hidden in the distributional definition. -/
theorem geometric_iff_distributional {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ} :
    LiZhongQC.IsKQC f U K ↔ IsDistributionallyKQuasiconformal f U K := by
  constructor
  · intro hf
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.isSensePreserving,
      LiZhongQC.dz f, LiZhongQC.dzbar f,
      quasiconformal_distributional_wirtinger_derivatives hf,
      geometric_quasiconformal_derivative_inequality hf⟩
  · rintro ⟨hU, hK, hhomeo, -, g, h, hw, hbound⟩
    apply geometric_iff_analytic.mpr
    refine ⟨hU, hK, hhomeo, (isACL_of_distributional_wirtinger hU hhomeo.1 hw).1, ?_⟩
    filter_upwards [homeomorph_wirtinger_eq_distributional_ae hU hhomeo hw, hbound]
      with z hz hboundz
    rw [hz.1, hz.2]
    exact hboundz

/-- Analytic Definitions A and A-prime are equivalent with the same K. -/
theorem analytic_iff_distributional {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ} :
    IsAnalyticallyKQuasiconformal f U K ↔ IsDistributionallyKQuasiconformal f U K :=
  geometric_iff_analytic.symm.trans geometric_iff_distributional

/-- Literal Analytic Definition A-prime: an orientation-preserving homeomorphism
whose two distributional Wirtinger derivatives are locally integrable and obey
`|f_zbar| ≤ k |f_z|` almost everywhere for one constant `0 ≤ k < 1`. -/
def IsDistributionallyQuasiconformal (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  IsOpen U ∧ LiZhongQC.IsHomeomorphOnto f U (f '' U) ∧
    LiZhongQC.IsSensePreserving f U ∧
      ∃ g h : ℂ → ℂ, HasDistributionalWirtingerDerivatives f g h U ∧
        ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
          ∀ᵐ z ∂(volume.restrict U), ‖h z‖ ≤ k * ‖g z‖

/-- The literal k-form and fixed-K form of the weak definition have the same
admissible maps, with the usual exact conversion of distortion constants. -/
theorem distributional_iff_exists_K {f : ℂ → ℂ} {U : Set ℂ} :
    IsDistributionallyQuasiconformal f U ↔
      ∃ K : ℝ, IsDistributionallyKQuasiconformal f U K := by
  constructor
  · rintro ⟨hU, hhomeo, horient, g, h, hw, k, hk0, hk1, hbound⟩
    have hkpos : 0 < 1 - k := by linarith
    have hK : 1 ≤ (1 + k) / (1 - k) := by
      rw [le_div_iff₀ hkpos]
      linarith
    refine ⟨(1 + k) / (1 - k), hU, hK, hhomeo, horient, g, h, hw, ?_⟩
    filter_upwards [hbound] with z hz
    rw [div_mul_eq_mul_div, le_div_iff₀ hkpos]
    nlinarith
  · rintro ⟨K, hU, hK, hhomeo, horient, g, h, hw, hbound⟩
    have hKpos : 0 < K + 1 := by linarith
    have hk0 : 0 ≤ (K - 1) / (K + 1) := div_nonneg (by linarith) hKpos.le
    have hk1 : (K - 1) / (K + 1) < 1 := by
      rw [div_lt_iff₀ hKpos]
      linarith
    refine ⟨hU, hhomeo, horient, g, h, hw, (K - 1) / (K + 1), hk0, hk1, ?_⟩
    exact hbound.mono fun z hz => (wirtinger_inequality_iff hK).1 hz

/-- Quasiconformality is equivalent to the genuine locally integrable weak formulation. -/
theorem quasiconformal_iff_distributional {f : ℂ → ℂ} {U : Set ℂ} :
    LiZhongQC.IsQuasiconformal f U ↔ IsDistributionallyQuasiconformal f U := by
  rw [distributional_iff_exists_K]
  change (∃ K : ℝ, LiZhongQC.IsKQC f U K) ↔
    ∃ K : ℝ, IsDistributionallyKQuasiconformal f U K
  exact exists_congr fun K => geometric_iff_distributional

end LowDimensionalTopology.Geometry.Quasiconformal
