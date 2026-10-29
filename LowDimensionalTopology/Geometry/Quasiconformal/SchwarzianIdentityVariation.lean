/-
The parameter Taylor, Cauchy estimate and Schwarzian differentiation proofs adapt
Wu Xiaobin's Li-Zhong-QC-formalization, pinned commit
1c0d5473c020b66ed5106331a38a61536760b9b2, under Apache 2.0.
The domain below is any actual fixed open subset of the complex plane.
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton

/-!
# Spatial third derivatives of genuine analytic variations at the identity

The parameter and spatial domains are actual fixed open sets. Separate
holomorphy and actual local uniform bounds give the derivative interchange by
Taylor's estimate and Cauchy's estimate. No Schwarzian variation is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology Complex
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal.SchwarzianVariation

/-- The actual parameter derivative commutes with three spatial derivatives
on any fixed open domain for a locally bounded holomorphic family. -/
theorem hasDerivAt_iteratedDeriv_three_at_identity
    {P U : Set ℂ} (h0 : (0 : ℂ) ∈ P) (hU : IsOpen U)
    {F : ℂ → ℂ → ℂ} {V : ℂ → ℂ}
    (ha : ∀ w ∈ U, DifferentiableOn ℂ (fun t => F t w) P)
    (hb : ∀ t ∈ P, DifferentiableOn ℂ (F t) U)
    (hc : ∀ t₀ ∈ P, ∀ w₀ ∈ U, ∃ ε > 0, ball t₀ ε ⊆ P ∧ ball w₀ ε ⊆ U ∧
      ∃ M : ℝ, ∀ t ∈ ball t₀ ε, ∀ w ∈ ball w₀ ε, ‖F t w‖ ≤ M)
    (hF0 : F 0 = id)
    (hV : ∀ w ∈ U, HasDerivAt (fun t => F t w) (V w) 0)
    {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun t => iteratedDeriv 3 (F t) z) (iteratedDeriv 3 V z) 0 := by
  have hVd : DifferentiableOn ℂ V U := by
    have h := LiZhongQC.bB_h0_deriv_holo (P := U) (U := P) (F := fun w t => F t w)
      (fun t ht => hb t ht) (fun w hw => ha w hw)
      (fun w₀ hw₀ t₀ ht₀ => by
        obtain ⟨ε, hε, h1, h2, M, hM⟩ := hc t₀ ht₀ w₀ hw₀
        exact ⟨ε, hε, h2, h1, M, fun w hw t ht => hM t ht w hw⟩) 0 h0
    exact h.congr fun w hw => (hV w hw).deriv.symm
  obtain ⟨ε, hε, hPε, hUε, M, hM⟩ := hc 0 h0 z hz
  have htay : ∀ t : ℂ, ‖t‖ < ε / 2 → ∀ w ∈ ball z ε,
      ‖F t w - w - t * V w‖ ≤ 8 * M / ε ^ 2 * ‖t‖ ^ 2 := by
    intro t ht w hw
    have hwU : w ∈ U := hUε hw
    have hg : DifferentiableOn ℂ (fun s => F s w) (ball 0 ε) := (ha w hwU).mono hPε
    have h := LiZhongQC.bB_h0_taylor_le hε hg (fun s hs => hM s hs w hw) ht
    rw [zero_add, (hV w hwU).deriv, hF0] at h
    exact h
  let C : ℝ := (Nat.factorial 3 : ℝ) * (8 * M / ε ^ 2) / (ε / 2) ^ 3
  have hd3 : ∀ t : ℂ, ‖t‖ < ε / 2 →
      ‖iteratedDeriv 3 (F t) z - t * iteratedDeriv 3 V z‖ ≤ C * ‖t‖ ^ 2 := by
    intro t ht
    have htP : t ∈ P := hPε (mem_ball_zero_iff.mpr (by linarith))
    have hE : DifferentiableOn ℂ (fun w => F t w - w - t * V w) U :=
      ((hb t htP).sub differentiableOn_id).sub (hVd.const_mul t)
    have hsub : closedBall z (ε / 2) ⊆ U :=
      (closedBall_subset_ball (by linarith)).trans hUε
    have hbd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 3
      (by linarith : 0 < ε / 2) (hE.diffContOnCl_ball hsub)
      (fun w hw => htay t ht w
        (closedBall_subset_ball (by linarith) (sphere_subset_closedBall hw)))
    rw [LiZhongQC.b36_q_iteratedDeriv3_lin hU hz (hb t htP) hVd t] at hbd
    calc _ ≤ _ := hbd
      _ = C * ‖t‖ ^ 2 := by dsimp only [C]; ring
  have hzero : iteratedDeriv 3 (F 0) z = 0 := by
    rw [hF0]
    exact LiZhongQC.b36_q_iteratedDeriv3_id z
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM 0 (mem_ball_self hε) z (mem_ball_self hε))
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hδ : 0 < min (ε / 2) (c / (C + 1)) := lt_min (by linarith) (by positivity)
  filter_upwards [ball_mem_nhds (0 : ℂ) hδ] with t ht
  rw [mem_ball_zero_iff, lt_min_iff] at ht
  rw [hzero, sub_zero, sub_zero, smul_eq_mul]
  calc ‖iteratedDeriv 3 (F t) z - t * iteratedDeriv 3 V z‖ ≤ C * ‖t‖ ^ 2 := hd3 t ht.1
    _ ≤ c * ‖t‖ := by
      have h1 : C * ‖t‖ ≤ c := by
        have h := ht.2
        rw [lt_div_iff₀ (by positivity)] at h
        nlinarith [norm_nonneg t]
      nlinarith [norm_nonneg t]

/-- The actual Schwarzian of the family has the third spatial derivative of
its actual first variation as parameter derivative at the identity. -/
theorem hasDerivAt_schwarzian_at_identity
    {P U : Set ℂ} (hP : IsOpen P) (h0 : (0 : ℂ) ∈ P) (hU : IsOpen U)
    {F : ℂ → ℂ → ℂ} {V : ℂ → ℂ}
    (ha : ∀ w ∈ U, DifferentiableOn ℂ (fun t => F t w) P)
    (hb : ∀ t ∈ P, DifferentiableOn ℂ (F t) U)
    (hc : ∀ t₀ ∈ P, ∀ w₀ ∈ U, ∃ ε > 0, ball t₀ ε ⊆ P ∧ ball w₀ ε ⊆ U ∧
      ∃ M : ℝ, ∀ t ∈ ball t₀ ε, ∀ w ∈ ball w₀ ε, ‖F t w‖ ≤ M)
    (hF0 : F 0 = id)
    (hV : ∀ w ∈ U, HasDerivAt (fun t => F t w) (V w) 0)
    {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (fun t => LiZhongQC.schwarzian (F t) z) (iteratedDeriv 3 V z) 0 := by
  obtain ⟨hd1, hd2, -⟩ := LiZhongQC.bB_h0_deriv123_holo hU ha hb hc z hz
  have hn : P ∈ 𝓝 (0 : ℂ) := hP.mem_nhds h0
  have e1 := (hd1.differentiableAt hn).hasDerivAt
  have e2 := (hd2.differentiableAt hn).hasDerivAt
  have e3 : HasDerivAt (fun t => deriv (deriv (deriv (F t))) z)
      (iteratedDeriv 3 V z) 0 := by
    have h := hasDerivAt_iteratedDeriv_three_at_identity h0 hU ha hb hc hF0 hV hz
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h
  have v1 : deriv (F 0) z = 1 := by rw [hF0, deriv_id]
  have v2 : deriv (deriv (F 0)) z = 0 := by rw [hF0, deriv_id', deriv_const]
  have v3 : deriv (deriv (deriv (F 0))) z = 0 := by
    rw [hF0, deriv_id', deriv_const', deriv_const]
  have hne : ∀ᶠ t in 𝓝 (0 : ℂ), deriv (F t) z ≠ 0 :=
    e1.continuousAt.eventually_ne (by simpa only [v1] using one_ne_zero)
  have hS := (((e3.mul e1).sub (e2.mul e2)).div (e1.pow 2)
    (pow_ne_zero 2 (by simpa only [v1] using one_ne_zero))).sub
    (((e2.div e1 (by simpa only [v1] using one_ne_zero)).pow 2).const_mul (1 / 2))
  have hS' : HasDerivAt (fun t =>
      (deriv (deriv (deriv (F t))) z * deriv (F t) z -
        deriv (deriv (F t)) z * deriv (deriv (F t)) z) / deriv (F t) z ^ 2 -
      1 / 2 * (deriv (deriv (F t)) z / deriv (F t) z) ^ 2) (iteratedDeriv 3 V z) 0 := by
    convert hS using 1
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, v1, v2, v3]
    ring
  refine hS'.congr_of_eventuallyEq ?_
  filter_upwards [hP.mem_nhds h0, hne] with t ht htn
  exact LiZhongQC.bB_hs_schwarzian_eq ((hb t ht).analyticAt (hU.mem_nhds hz)) htn

end LowDimensionalTopology.Geometry.Quasiconformal.SchwarzianVariation
