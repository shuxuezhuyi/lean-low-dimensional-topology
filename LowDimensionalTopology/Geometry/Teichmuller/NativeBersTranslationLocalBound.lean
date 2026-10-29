module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslationPointNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.NativeAhlforsWeillSection

/-!
# A genuine local weighted-norm bound for the actual Bers translation

The actual inverse Bers epsilon estimate produces normalized coefficients
near the original universal point. True same-point naturality permits use
of its actual quotient representative. Exact coefficient translation
preserves the actual pseudo-hyperbolic distance; the source Bers estimate
then gives a fixed-base linear weighted-norm bound. The input norm is the
unchanged native weighted automorphic norm. No derivative or local inverse
is assumed in this estimate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The actual original Bers point in its genuine weighted automorphic space. -/
def baseBersValue (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) : BersWeighted.Automorphic Γ :=
  BersWeighted.automorphicProjection hΓ ν.val

theorem baseBersValue_toSource (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    ((baseBersValue hΓ ν).toSource : ℂ → ℂ) =
      LiZhongQC.bersFunction (toSourceGamma ν).val.val := by
  change BersWeighted.decode (BersWeighted.projection ν.val) = _
  rw [BersWeighted.projection, dite_eq_left (Ball.norm_lt_one ν),
    BersWeighted.decode_projectionValue, bersProjection_eq]
  rfl

private theorem log_quot_le_four_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1 / 2) :
    Real.log ((1 + x) / (1 - x)) ≤ 4 * x := by
  have hd : 0 < 1 - x := by linarith
  have hn : 0 < 1 + x := by linarith
  have hp := mul_nonneg hx0 (show 0 ≤ 1 - 2 * x by linarith)
  have hq : (1 + x) / (1 - x) ≤ 1 + 4 * x := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hn hd)
  linarith

/-- The true Bers-coordinate translation has a fixed-base local linear bound
in the original weighted norm, without assuming it is differentiable. -/
theorem sourceBersTranslation_local_bound (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ : BersWeighted.Automorphic Γ,
      c * ‖φ - baseBersValue hΓ ν‖ < 1 / 2 →
      LiZhongQC.bersNormL
          (LiZhongQC.b33_t_chi (toSourceGamma ν).val (φ.toSource : ℂ → ℂ)) ≤
        ENNReal.ofReal (12 * c * ‖φ - baseBersValue hΓ ν‖) := by
  let νH := (toSourceGamma ν).val
  let p : LiZhongQC.UniversalTeichmuller := Quotient.mk LiZhongQC.teichSetoid νH
  obtain ⟨c, hc, hcore⟩ := LiZhongQC.aw_core p
  refine ⟨c, hc, ?_⟩
  intro φ hφ
  let n := ‖φ - baseBersValue hΓ ν‖
  have hn : 0 ≤ n := norm_nonneg _
  have hx : 0 ≤ c * n := mul_nonneg hc.le hn
  have hsmall : c * n < 1 / 2 := hφ
  have hφL : (φ.toSource : ℂ → ℂ) ∈ LiZhongQC.bersSpaceL :=
    ⟨φ.toSource.property.1,
      (BersWeighted.Automorphic.bersNormL_toSource_le φ).trans_lt ENNReal.ofReal_lt_top⟩
  have hN := BersWeighted.Automorphic.bersNormL_toSource_le (φ - baseBersValue hΓ ν)
  have hsub : ((φ - baseBersValue hΓ ν).toSource : ℂ → ℂ) =
      (φ.toSource : ℂ → ℂ) - ((baseBersValue hΓ ν).toSource : ℂ → ℂ) := by
    change BersWeighted.decode (φ.val - (baseBersValue hΓ ν).val) =
      BersWeighted.decode φ.val - BersWeighted.decode (baseBersValue hΓ ν).val
    exact map_sub BersWeighted.decodeLinearMap _ _
  rw [hsub, baseBersValue_toSource] at hN
  have hN' : LiZhongQC.bersNormL ((φ.toSource : ℂ → ℂ) - LiZhongQC.bersMapU p) ≤
      ENNReal.ofReal n := by
    change LiZhongQC.bersNormL ((φ.toSource : ℂ → ℂ) -
      LiZhongQC.bersMapU (Quotient.mk LiZhongQC.teichSetoid νH)) ≤ ENNReal.ofReal n
    rw [LiZhongQC.aw_t_bersMapU_mk]
    exact hN
  have hnsmall : n < 1 / c := by
    apply (lt_div_iff₀ hc).mpr
    nlinarith
  obtain ⟨μ, hS, hv⟩ := hcore (φ.toSource : ℂ → ℂ) hφL n hn hN' hnsmall
  have hBF : LiZhongQC.bersFunction μ.val = (φ.toSource : ℂ → ℂ) := by
    funext z
    by_cases hz : z ∈ LiZhongQC.lowerHalf
    · rw [LiZhongQC.bersFunction, indicator_of_mem hz]
      exact hS z hz
    · rw [LiZhongQC.bersFunction, indicator_of_notMem hz]
      exact (φ.toSource.property.2.1 z hz).symm
  have hclass : (Quotient.mk LiZhongQC.teichSetoid p.out : LiZhongQC.UniversalTeichmuller) =
      Quotient.mk LiZhongQC.teichSetoid νH := Quotient.out_eq p
  have hchi := sourceBersTranslation_eq_of_samePoint p.out νH hclass
  have hb := LiZhongQC.eq21_10 (LiZhongQC.b33_t_tb p.out p.out) (LiZhongQC.b33_t_tb p.out μ)
  change LiZhongQC.bersNormL
      (LiZhongQC.bersFunction (LiZhongQC.translatedBeltrami p.out.val μ.val) -
        LiZhongQC.bersFunction (LiZhongQC.translatedBeltrami p.out.val p.out.val)) ≤
    ENNReal.ofReal (3 * LiZhongQC.UniversalTeichmuller.dilatationDiffNorm
      (LiZhongQC.translatedBeltrami p.out.val μ.val)
      (LiZhongQC.translatedBeltrami p.out.val p.out.val)) at hb
  rw [LiZhongQC.b33_t_dd_tb, LiZhongQC.b33_t_tb_self, LiZhongQC.b33_t_bf_zero,
    sub_zero] at hb
  have hd : LiZhongQC.UniversalTeichmuller.dilatationDiffNorm μ.val p.out.val ≤
      LiZhongQC.ut_v p.out μ := by
    rw [LiZhongQC.UniversalTeichmuller.ut_d_symm,
      (LiZhongQC.UniversalTeichmuller.ut_v_eq p.out μ).2]
    exact LiZhongQC.bB_le_log_quot ENNReal.toReal_nonneg
      (LiZhongQC.UniversalTeichmuller.ut_v_eq p.out μ).1
  have hl := log_quot_le_four_mul hx hsmall
  rw [← hchi, ← hBF, LiZhongQC.b33_t_chi_spec]
  exact hb.trans (ENNReal.ofReal_le_ofReal (by nlinarith))

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
