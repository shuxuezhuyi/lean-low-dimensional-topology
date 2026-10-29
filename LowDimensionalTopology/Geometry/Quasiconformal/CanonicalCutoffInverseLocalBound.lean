module

public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalLocalizedFactorDerivative
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.Conformal
public import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# The actual conformal cutoff factor has a local Lipschitz inverse

The inverse bound is derived from the genuine local holomorphy of the actual
plane homeomorphism. The final consumer keeps the original canonical maps.
No inverse bound, power estimate, or supplied factorization is an assumption.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology Metric Complex
open scoped NNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- A plane homeomorphism holomorphic near zero, fixing zero, has an actual
Lipschitz inverse on a neighborhood of zero. -/
theorem conformal_homeomorph_inverse_lipschitz_zero (H : ℂ ≃ₜ ℂ)
    {U : Set ℂ} (hU : IsOpen U) (h0U : (0 : ℂ) ∈ U)
    (hH : DifferentiableOn ℂ H U) (h0 : H 0 = 0) :
    ∃ K : ℝ≥0, ∃ V ∈ 𝓝 (0 : ℂ), LipschitzOnWith K H.symm V := by
  have hi0 : H.symm 0 = 0 := (H.symm_apply_eq).2 h0.symm
  have hne : deriv H 0 ≠ 0 :=
    LiZhongQC.deriv_ne_zero_of_injOn hU hH H.injective.injOn h0U
  have hstrict : HasStrictDerivAt H (deriv H 0) (H.symm 0) := by
    rw [hi0]
    exact (hH.analyticAt (hU.mem_nhds h0U)).hasStrictDerivAt
  have hinv : HasStrictDerivAt H.symm (deriv H 0)⁻¹ 0 :=
    HasStrictDerivAt.of_local_left_inverse H.symm.continuous.continuousAt
      hstrict hne (Filter.Eventually.of_forall H.apply_symm_apply)
  exact hinv.hasStrictFDerivAt.exists_lipschitzOnWith

/-- The internally constructed compact cutoff map is bounded near zero by
the same original canonical full-plane map, with no support condition on it. -/
theorem canonical_cutoff_norm_le_original_near_zero
    (μ : Teichmuller.MeasurableBeltramiBall) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (0 : ℂ) δ,
      ‖Teichmuller.MeasurableBeltramiBall.normalizedSolution
          (canonicalBallFourCutoff μ) z‖ ≤
        L * ‖Teichmuller.MeasurableBeltramiBall.normalizedSolution μ z‖ := by
  let F := Teichmuller.MeasurableBeltramiBall.normalizedSolution μ
  let G := Teichmuller.MeasurableBeltramiBall.normalizedSolution (canonicalBallFourCutoff μ)
  let H : ℂ ≃ₜ ℂ := G.symm.trans F
  have hF0 : F 0 = 0 :=
    (Teichmuller.MeasurableBeltramiBall.normalizedSolution_spec μ).1.2.2.1
  have hG0 : G 0 = 0 :=
    (Teichmuller.MeasurableBeltramiBall.normalizedSolution_spec
      (canonicalBallFourCutoff μ)).1.2.2.1
  have hiG0 : G.symm 0 = 0 := (G.symm_apply_eq).2 hG0.symm
  have hH0 : H 0 = 0 := by
    change F (G.symm 0) = 0
    rw [hiG0, hF0]
  have h0U : (0 : ℂ) ∈ G '' ball 0 4 :=
    ⟨0, mem_ball_self (by norm_num), hG0⟩
  have hH : DifferentiableOn ℂ H (G '' ball 0 4) :=
    (normalizedSolution_cutoff_conformal_factor μ (ball 0 4) isOpen_ball).1
  obtain ⟨K, V, hV, hLip⟩ := conformal_homeomorph_inverse_lipschitz_zero H
    (G.isOpenMap _ isOpen_ball) h0U hH hH0
  have hiH0 : H.symm 0 = 0 := (H.symm_apply_eq).2 hH0.symm
  have hpre : F ⁻¹' V ∈ 𝓝 (0 : ℂ) :=
    F.continuous.continuousAt.preimage_mem_nhds (by simpa only [hF0] using hV)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨K, K.coe_nonneg, δ, hδ, ?_⟩
  intro z hz
  have hbound := hLip.dist_le_mul (F z) (hsub hz) 0 (mem_of_mem_nhds hV)
  have hcancel : H.symm (F z) = G z := by
    change G (F.symm (F z)) = G z
    rw [F.symm_apply_apply]
  simpa only [hcancel, hiH0, dist_zero_right] using hbound

end LowDimensionalTopology.Geometry.Quasiconformal
