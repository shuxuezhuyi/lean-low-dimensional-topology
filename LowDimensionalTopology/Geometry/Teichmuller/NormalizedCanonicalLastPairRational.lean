module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalFrickeRecovery
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic.FieldSimp

/-!
# Rational recovery of the actual final canonical pair

The convention is `M = [γ,D]⁻¹ = D γ D⁻¹ γ⁻¹`. Only the two actual
last matrices are recovered, up to explicit nonzero real scalars. Their raw
matrix-word invariant is therefore `trace² / det`, without a choice of roots.
The diagonal equations are reused from the credited Li-Zhong-QC source.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Matrix.Norms.Elementwise

namespace LowDimensionalTopology.Geometry.Teichmuller

abbrev LastPairRawMatrix := Matrix (Fin 2) (Fin 2) ℝ

def lastPairRationalK (M : LastPairRawMatrix) : ℝ :=
  (1 - M 0 0) / (M 1 1 - 1)

def lastPairRationalP (M : LastPairRawMatrix) : ℝ := M 0 1 / (1 - M 0 0)

def lastPairRationalQ (M : LastPairRawMatrix) : ℝ :=
  M 0 1 / (lastPairRationalK M - M 0 0)

def lastPairRationalS (M : LastPairRawMatrix) : ℝ :=
  (lastPairRationalP M - 1) / (1 - lastPairRationalQ M)

def lastPairAlphaRaw (M : LastPairRawMatrix) : LastPairRawMatrix :=
  !![lastPairRationalP M, lastPairRationalQ M * lastPairRationalS M;
    1, lastPairRationalS M]

def lastPairBetaRaw (M : LastPairRawMatrix) : LastPairRawMatrix :=
  !![lastPairRationalK M, 0; 0, 1]

/-- All four actual denominators and both scalar factors are nonzero; the
recovered matrices represent the SAME last two projective generators. -/
theorem lastPairRational_recovery (γ D : RealSL)
    (hD : D 0 1 = 0 ∧ D 1 0 = 0 ∧ 1 < D 0 0 ^ 2)
    (hfix : γ 0 0 + γ 0 1 = γ 1 0 + γ 1 1)
    (halt : 0 < γ 0 1 * γ 1 0) :
    let M := (D * γ * D⁻¹ * γ⁻¹).val
    (M 1 1 - 1 ≠ 0 ∧ 1 - M 0 0 ≠ 0 ∧
      lastPairRationalK M - M 0 0 ≠ 0 ∧ 1 - lastPairRationalQ M ≠ 0) ∧
      lastPairAlphaRaw M = (γ 1 0)⁻¹ • γ.val ∧
      lastPairBetaRaw M = D 0 0 • D.val ∧ γ 1 0 ≠ 0 ∧ D 0 0 ≠ 0 := by
  let M : LastPairRawMatrix := (D * γ * D⁻¹ * γ⁻¹).val
  change (_ ∧ _ ∧ _ ∧ _) ∧ _ ∧ _ ∧ _ ∧ _
  obtain ⟨hdetD, _, _⟩ := LiZhongQC.s27t_diag_facts hD
  have hdetγ := LiZhongQC.hnf_sl2_det γ
  obtain ⟨e00, e11⟩ := LiZhongQC.s27t_M_entries γ D hD.1 hD.2.1
  change M 0 0 = _ at e00
  change M 1 1 = _ at e11
  have hc : γ 1 0 ≠ 0 := by intro h; simp [h] at halt
  have had : 0 < γ 0 0 * γ 1 1 := by linarith
  have hd : γ 1 1 ≠ 0 := by intro h; simp [h] at had
  have hu : D 0 0 ≠ 0 := by intro h; simp [h] at hdetD
  have h11 : 0 < M 1 1 - 1 := by
    have h := LiZhongQC.s27t_comm_inv_11 γ D hD halt
    rw [LiZhongQC.s27t_comm_inv] at h
    change 1 < M 1 1 at h
    linarith
  have h00eq : 1 - M 0 0 = (D 0 0 ^ 2 - 1) * (γ 0 1 * γ 1 0) := by
    linear_combination -e00 - hdetγ
  have h00 : 0 < 1 - M 0 0 := by
    rw [h00eq]
    exact mul_pos (sub_pos.mpr hD.2.2) halt
  have hk : lastPairRationalK M = D 0 0 ^ 2 := by
    apply (div_eq_iff h11.ne').mpr
    have he : M 0 0 - 1 = D 0 0 ^ 2 * (1 - M 1 1) := by
      linear_combination e00 + D 0 0 ^ 2 * e11 + (1 + D 0 0 ^ 2) * hdetγ -
        (γ 0 1 * γ 1 0) * (D 0 0 * D 1 1 + 1) * hdetD
    linarith
  have hkeq : D 0 0 ^ 2 - M 0 0 = (D 0 0 ^ 2 - 1) * (γ 0 0 * γ 1 1) := by
    linear_combination -e00 - D 0 0 ^ 2 * hdetγ
  have hkpos : 0 < D 0 0 ^ 2 - M 0 0 := by
    rw [hkeq]
    exact mul_pos (sub_pos.mpr hD.2.2) had
  have e01 : M 0 1 = (D 0 0 ^ 2 - 1) * (γ 0 0 * γ 0 1) := by
    obtain ⟨i00, i01, i10, i11⟩ := LiZhongQC.s27t_inv_apply D
    obtain ⟨j00, j01, j10, j11⟩ := LiZhongQC.s27t_inv_apply γ
    dsimp only [M]
    simp only [LiZhongQC.s27t_mul_apply, i00, i01, i10, i11,
      j01, j11, hD.1, hD.2.1]
    linear_combination -(γ 0 0 * γ 0 1) * hdetD
  have hp : lastPairRationalP M = γ 0 0 / γ 1 0 := by
    apply (div_eq_div_iff h00.ne' hc).mpr
    rw [e01, h00eq]
    ring
  have hq : lastPairRationalQ M = γ 0 1 / γ 1 1 := by
    change M 0 1 / (lastPairRationalK M - M 0 0) = _
    rw [hk]
    apply (div_eq_div_iff hkpos.ne' hd).mpr
    rw [e01, hkeq]
    ring
  have hdb : γ 1 1 - γ 0 1 ≠ 0 := by
    intro h
    have hdb' : γ 1 1 = γ 0 1 := sub_eq_zero.mp h
    have hac : γ 0 0 = γ 1 0 := by linarith
    rw [hdb', hac] at hdetγ
    nlinarith only [hdetγ]
  have hqden : 1 - lastPairRationalQ M ≠ 0 := by
    rw [hq]
    intro h
    have hh := (eq_div_iff hd).mp (sub_eq_zero.mp h)
    apply hdb
    linarith
  have hs : lastPairRationalS M = γ 1 1 / γ 1 0 := by
    apply (div_eq_iff hqden).mpr
    rw [hp, hq]
    have hf := congrArg (fun z : ℝ => z * γ 1 1) hfix
    field_simp [hc, hd]
    nlinarith only [hfix, hf]
  refine ⟨⟨h11.ne', h00.ne', by
      change lastPairRationalK M - M 0 0 ≠ 0
      rw [hk]
      exact hkpos.ne', hqden⟩,
    ?_, ?_, hc, hu⟩
  · ext i j
    fin_cases i <;> fin_cases j
    · change lastPairRationalP M = (γ 1 0)⁻¹ * γ 0 0
      rw [hp, div_eq_mul_inv]
      ring
    · change lastPairRationalQ M * lastPairRationalS M = (γ 1 0)⁻¹ * γ 0 1
      rw [hq, hs]
      field_simp [hc, hd]
    · change 1 = (γ 1 0)⁻¹ * γ 1 0
      exact (inv_mul_cancel₀ hc).symm
    · change lastPairRationalS M = (γ 1 0)⁻¹ * γ 1 1
      rw [hs, div_eq_mul_inv]
      ring
  · ext i j
    fin_cases i <;> fin_cases j
    · change lastPairRationalK M = D 0 0 * D 0 0
      rw [hk, pow_two]
    · change 0 = D 0 0 * D 0 1
      rw [hD.1, mul_zero]
    · change 0 = D 0 0 * D 1 0
      rw [hD.2.1, mul_zero]
    · change 1 = D 0 0 * D 1 1
      exact hdetD.symm

/-- A locally fixed prefix sign recovers the inverse commutator, rather than
silently identifying the signed prefix with it. -/
theorem lastPair_inverse_commutator_from_prefix (η γ D : RealSL)
    (hD : D 0 1 = 0 ∧ D 1 0 = 0 ∧ 1 < D 0 0 ^ 2)
    (halt : 0 < γ 0 1 * γ 1 0)
    (hrel : η * LiZhongQC.commutatorSL γ D = 1 ∨
      η * LiZhongQC.commutatorSL γ D = -1) :
    (LiZhongQC.commutatorSL γ D)⁻¹ = if 0 < η 1 1 then η else -η := by
  have hM := LiZhongQC.s27t_comm_inv_11 γ D hD halt
  rcases LiZhongQC.s27t_eta_eq hrel with h | h
  · rw [h]
    simp only [show 0 < (LiZhongQC.commutatorSL γ D)⁻¹ 1 1 by linarith,
      ite_true]
  · rw [h]
    have hn : ¬0 < (-(LiZhongQC.commutatorSL γ D)⁻¹) 1 1 := by
      rw [LiZhongQC.s27t_neg_apply]
      linarith
    simp only [hn, ite_false, neg_neg]

/-- The explicit raw pair is analytic at every point where its FOUR concrete
denominators are nonzero. `lastPairRational_recovery` proves these facts for
every actual final pair; no analytic dependence of chosen models is assumed. -/
theorem lastPairRaw_analyticAt (M : LastPairRawMatrix)
    (h11 : M 1 1 - 1 ≠ 0) (h00 : 1 - M 0 0 ≠ 0)
    (hk : lastPairRationalK M - M 0 0 ≠ 0)
    (hq : 1 - lastPairRationalQ M ≠ 0) :
    AnalyticAt ℝ lastPairAlphaRaw M ∧ AnalyticAt ℝ lastPairBetaRaw M := by
  have hid : AnalyticAt ℝ (fun Z : LastPairRawMatrix => Z) M := analyticAt_id
  have he (i j : Fin 2) : AnalyticAt ℝ (fun Z : LastPairRawMatrix => Z i j) M :=
    analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hid i) j
  have hK : AnalyticAt ℝ lastPairRationalK M :=
    (analyticAt_const.sub (he 0 0)).div ((he 1 1).sub analyticAt_const) h11
  have hP : AnalyticAt ℝ lastPairRationalP M :=
    (he 0 1).div (analyticAt_const.sub (he 0 0)) h00
  have hQ : AnalyticAt ℝ lastPairRationalQ M :=
    (he 0 1).div (hK.sub (he 0 0)) hk
  have hS : AnalyticAt ℝ lastPairRationalS M :=
    (hP.sub analyticAt_const).div (analyticAt_const.sub hQ) hq
  constructor
  · apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    fin_cases i <;> fin_cases j
    · exact hP
    · exact hQ.mul hS
    · exact analyticAt_const
    · exact hS
  · apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    fin_cases i <;> fin_cases j
    · exact hK
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const

end LowDimensionalTopology.Geometry.Teichmuller
