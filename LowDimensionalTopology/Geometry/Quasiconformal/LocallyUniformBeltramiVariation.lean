/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.BeltramiVariation
public import LowDimensionalTopology.External.LiZhongQC.Ch05.S21_UniversalTeichmuller
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Locally uniform first variation of normalized plane solutions

Scalar holomorphic dependence, the normalized plane growth estimate, and the
Cauchy Taylor bound give a quadratic remainder with a constant uniform on each
bounded disc, including for coefficients with unbounded support. Normalization
of the coefficient direction then transfers this bound to actual L-infinity
classes and their canonical normalized homeomorphisms.

The analytic estimates and the explicit derivative computation used below are
due to Wu Xiaobin, from commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
The fixed external source retains complete author and license records. All new
bridges use its proved public interfaces and Mathlib public APIs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory Filter Topology Complex
open scoped ENNReal
open LowDimensionalTopology.Geometry.Teichmuller

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem normalizedMap_eq {μ f g : ℂ → ℂ}
    (hf : LiZhongQC.IsNormalizedSolution f μ) (hg : LiZhongQC.IsNormalizedSolution g μ) :
    f = g :=
  LiZhongQC.thm13_5_uniqueness_plane hf.1 hg.1 hf.2.1 hg.2.1
    (Filter.EventuallyEq.trans hf.2.2.2.2 (Filter.EventuallyEq.symm hg.2.2.2.2)) hf.2.2.1 hf.2.2.2.1 hg.2.2.1 hg.2.2.2.1

private theorem selectedPlaneSolution_spec {μ : ℂ → ℂ} {k : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1) (hμ : LiZhongQC.IsBeltramiCoeff μ univ k) :
    LiZhongQC.IsNormalizedSolution (LiZhongQC.normalizedSolution μ) μ := by
  have hex : ∃ f : ℂ → ℂ, LiZhongQC.IsNormalizedSolution f μ :=
    (LiZhongQC.thm13_7_normalized_existence hk₀ hk hμ).imp fun _ hf => hf.1
  rw [LiZhongQC.normalizedSolution, dite_eq_left hex]
  exact hex.choose_spec

private theorem scaledCoefficient_half {ν : ℂ → ℂ}
    (hν : LiZhongQC.IsBeltramiCoeff ν univ 1) {t : ℂ} (ht : ‖t‖ < 1 / 2) :
    LiZhongQC.IsBeltramiCoeff (fun ζ => t * ν ζ) univ (1 / 2) := by
  refine ⟨aestronglyMeasurable_const.mul hν.1, hν.2.mono ?_⟩
  intro ζ hζ
  calc ‖t * ν ζ‖ = ‖t‖ * ‖ν ζ‖ := norm_mul _ _
    _ ≤ ‖t‖ * 1 := mul_le_mul_of_nonneg_left hζ (norm_nonneg _)
    _ ≤ 1 / 2 := by simpa only [mul_one] using ht.le

private theorem normalizedPlane_half {μ F : ℂ → ℂ}
    (hF : LiZhongQC.IsNormalizedSolution F μ)
    (hμ : LiZhongQC.IsBeltramiCoeff μ univ (1 / 2)) :
    LiZhongQC.IsKQCNormalizedPlane F 3 := by
  obtain ⟨G, -, hGK, huniq⟩ := LiZhongQC.thm13_7_normalized_existence
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hμ
  refine ⟨?_, hF.2.1, hF.2.2.1, hF.2.2.2.1⟩
  rw [huniq F hF]
  convert hGK using 1; norm_num

private theorem scalarPlaneSolution_zero (ν : ℂ → ℂ) :
    LiZhongQC.normalizedSolution (fun ζ => (0 : ℂ) * ν ζ) = id := by
  have hzero : (fun ζ => (0 : ℂ) * ν ζ) = (0 : ℂ → ℂ) := by funext ζ; simp
  rw [hzero]
  exact LiZhongQC.bB_l_normalizedSolution_zero

private theorem scalarPlaneSolution_hasDerivAt {ν : ℂ → ℂ}
    (hν : LiZhongQC.IsBeltramiCoeff ν univ 1) (w : ℂ) :
    HasDerivAt (fun t : ℂ => LiZhongQC.normalizedSolution (fun ζ => t * ν ζ) w)
      (LiZhongQC.ahVar ν w) 0 := by
  have hμ : ∀ t ∈ ball (0 : ℂ) (1 / 2),
      LiZhongQC.IsBeltramiCoeff (fun ζ => t * ν ζ) univ (1 / 2) :=
    fun t ht => scaledCoefficient_half hν (mem_ball_zero_iff.mp ht)
  have hf : ∀ t ∈ ball (0 : ℂ) (1 / 2),
      LiZhongQC.IsNormalizedSolution (LiZhongQC.normalizedSolution (fun ζ => t * ν ζ))
        (fun ζ => t * ν ζ) :=
    fun t ht => selectedPlaneSolution_spec (by norm_num) (by norm_num) (hμ t ht)
  have hd := LiZhongQC.ahT_hasDerivAt isOpen_ball
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hμ
    (fun ζ => (differentiable_id.mul_const (ν ζ)).differentiableOn) hf
    (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)) w
  have hF0 := scalarPlaneSolution_zero ν
  have hdot : LiZhongQC.ahT_dot (fun ζ => deriv (fun s : ℂ => s * ν ζ) 0)
      (fun ζ => (0 : ℂ) * ν ζ)
      (LiZhongQC.normalizedSolution (fun ζ => (0 : ℂ) * ν ζ)) = ν := by
    rw [hF0]
    funext ζ
    have hinv : Function.invFunOn (id : ℂ → ℂ) univ ζ = ζ :=
      (injOn_id univ).leftInvOn_invFunOn (mem_univ ζ)
    have hdz : LiZhongQC.dz id ζ = 1 := by
      simp only [LiZhongQC.dz, fderiv_id, ContinuousLinearMap.id_apply]
      rw [I_mul_I]
      ring
    have hder : deriv (fun s : ℂ => s * ν ζ) 0 = ν ζ := by simp
    simp [LiZhongQC.ahT_dot, hinv, hdz, hder]
  rw [hdot, hF0] at hd
  exact hd

/-- The actual scalar family has a quadratic error uniform in every bounded disc.
The coefficient direction may have arbitrary, noncompact support. -/
theorem scalar_normalizedSolution_uniform_quadratic (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : ℂ → ℂ), LiZhongQC.IsBeltramiCoeff ν univ 1 →
      ∀ t : ℂ, ‖t‖ < 1 / 4 → ∀ w : ℂ, ‖w‖ ≤ R →
        ‖LiZhongQC.normalizedSolution (fun ζ => t * ν ζ) w - w - t * LiZhongQC.ahVar ν w‖ ≤
          C * ‖t‖ ^ 2 := by
  let M : ℝ := max (LiZhongQC.lambdaInv (3 * LiZhongQC.quadLambda R)) 1
  have hM : 0 ≤ M := le_trans zero_le_one (le_max_right _ _)
  refine ⟨8 * M / (1 / 2 : ℝ) ^ 2, by positivity, ?_⟩
  intro ν hν t ht w hw
  have hμ : ∀ s ∈ ball (0 : ℂ) (1 / 2),
      LiZhongQC.IsBeltramiCoeff (fun ζ => s * ν ζ) univ (1 / 2) :=
    fun s hs => scaledCoefficient_half hν (mem_ball_zero_iff.mp hs)
  have hf : ∀ s ∈ ball (0 : ℂ) (1 / 2),
      LiZhongQC.IsNormalizedSolution (LiZhongQC.normalizedSolution (fun ζ => s * ν ζ))
        (fun ζ => s * ν ζ) :=
    fun s hs => selectedPlaneSolution_spec (by norm_num) (by norm_num) (hμ s hs)
  have hhol := LiZhongQC.thm13_8_ahlfors_bers_holomorphic isOpen_ball
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hμ
    (fun ζ => (differentiable_id.mul_const (ν ζ)).differentiableOn) hf w
  have hbound : ∀ s ∈ ball (0 : ℂ) (1 / 2),
      ‖LiZhongQC.normalizedSolution (fun ζ => s * ν ζ) w‖ ≤ M := by
    intro s hs
    exact (LiZhongQC.UniversalTeichmuller.ut2_nb_upper
      (normalizedPlane_half (hf s hs) (hμ s hs)) hR hw).trans (le_max_left _ _)
  have hT := LiZhongQC.bB_h0_taylor_le (c := (0 : ℂ)) (ε := (1 / 2 : ℝ))
    (M := M) (by norm_num) hhol hbound
    (h := t) (by convert ht using 1; norm_num)
  have hder := (scalarPlaneSolution_hasDerivAt hν w).deriv
  have hzero : LiZhongQC.normalizedSolution (fun ζ => (0 : ℂ) * ν ζ) w = w :=
    congrFun (scalarPlaneSolution_zero ν) w
  simpa only [zero_add, hzero, hder] using hT

private theorem sourceVariation_mul (ν : ℂ → ℂ) (a w : ℂ) :
    LiZhongQC.ahVar (fun ζ => a * ν ζ) w = a * LiZhongQC.ahVar ν w := by
  have heq : (fun ζ => (a * ν ζ) * LiZhongQC.ahKer w ζ) =
      fun ζ => a * (ν ζ * LiZhongQC.ahKer w ζ) := by funext ζ; ring
  unfold LiZhongQC.ahVar
  rw [heq, integral_const_mul]
  ring

/-- The canonical normalized map on the actual L-infinity ball has a uniformly
quadratic first-variation remainder on each bounded disc, including at the zero class. -/
theorem normalizedSolution_uniform_quadratic (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : MeasurableBeltramiBall, ‖μ.val‖ < 1 / 4 →
      ∀ w : ℂ, ‖w‖ ≤ R →
        ‖MeasurableBeltramiBall.normalizedSolution μ w - w - firstVariation μ.val w‖ ≤
          C * ‖μ.val‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := scalar_normalizedSolution_uniform_quadratic R hR
  refine ⟨C, hC, ?_⟩
  intro μ hμsmall w hw
  by_cases hzero : ‖μ.val‖ = 0
  · have hμzero : μ.val = 0 := norm_eq_zero.mp hzero
    have hae : (μ.val : ℂ → ℂ) =ᵐ[volume] (0 : ℂ → ℂ) := by
      rw [hμzero]
      exact Lp.coeFn_zero ℂ (⊤ : ℝ≥0∞) volume
    have hid : LiZhongQC.IsNormalizedSolution (Homeomorph.refl ℂ) (0 : ℂ → ℂ) :=
      LiZhongQC.td_id_normalized (Eventually.of_forall fun _ => rfl)
    have hF := normalized_beltrami_homeomorph_unique
      (MeasurableBeltramiBall.normalizedSolution_isNormalized_of_ae μ hae) hid
    have hV : firstVariation μ.val w = 0 := by
      apply norm_le_zero_iff.mp
      simpa only [hzero, mul_zero] using firstVariation_norm_le μ.val w
    simp [hF, hV, hzero]
  · let a : ℂ := (‖μ.val‖ : ℝ)
    have ha : a ≠ 0 := Complex.ofReal_ne_zero.mpr hzero
    have hanorm : ‖a‖ = ‖μ.val‖ := Complex.norm_of_nonneg (norm_nonneg _)
    let ν : ℂ → ℂ := fun ζ => a⁻¹ * μ.val ζ
    have hν : LiZhongQC.IsBeltramiCoeff ν univ 1 := by
      have hμ := MeasurableBeltramiSpace.isBeltramiCoeff μ.val
      refine ⟨aestronglyMeasurable_const.mul hμ.1, hμ.2.mono ?_⟩
      intro ζ hζ
      change ‖a⁻¹ * μ.val ζ‖ ≤ 1
      rw [norm_mul, norm_inv, hanorm]
      exact (mul_le_mul_of_nonneg_left hζ (inv_nonneg.mpr (norm_nonneg _))).trans
        (by rw [inv_mul_cancel₀ hzero])
    have hcoeff : (fun ζ => a * ν ζ) = (μ.val : ℂ → ℂ) := by
      funext ζ
      dsimp only [ν]
      rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    have hsmall : ‖a‖ < 1 / 4 := by rw [hanorm]; exact hμsmall
    have hFspec : LiZhongQC.IsNormalizedSolution
        (LiZhongQC.normalizedSolution (fun ζ => a * ν ζ)) (μ.val : ℂ → ℂ) := by
      rw [hcoeff]
      exact selectedPlaneSolution_spec (norm_nonneg _) (MeasurableBeltramiBall.norm_lt_one μ)
        (MeasurableBeltramiSpace.isBeltramiCoeff μ.val)
    have hF : LiZhongQC.normalizedSolution (fun ζ => a * ν ζ) =
        (MeasurableBeltramiBall.normalizedSolution μ : ℂ → ℂ) :=
      normalizedMap_eq hFspec (MeasurableBeltramiBall.normalizedSolution_spec μ).1
    have hV : a * LiZhongQC.ahVar ν w = firstVariation μ.val w := by
      calc
        a * LiZhongQC.ahVar ν w = LiZhongQC.ahVar (fun ζ => a * ν ζ) w :=
          (sourceVariation_mul ν a w).symm
        _ = LiZhongQC.ahVar μ.val w := congrArg (fun ρ => LiZhongQC.ahVar ρ w) hcoeff
        _ = firstVariation μ.val w := (firstVariation_eq_source μ.val w).symm
    have h := hbound ν hν a hsmall w hw
    rw [hF, hV, hanorm] at h
    exact h

end LowDimensionalTopology.Geometry.Quasiconformal
