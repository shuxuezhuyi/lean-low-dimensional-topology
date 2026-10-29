/-
Analytic arguments adapted from Wu Xiaobin's Li-Zhong-QC-formalization,
commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.AnalyticGeometric
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith

/-!
# Maximal quasiconformal dilatation as an attained infimum

For an actual quasiconformal map on a nonempty open plane domain, the infimum
of its admissible distortion constants equals the essential supremum of the
actual Wirtinger distortion quotient. The optimal constant is attained.

The quasiconformal predicate here uses the preserved genuine quadrilateral
model. The analytic infimum below is proved equal for the actual analytic ACL
predicate. No identification with a separate intrinsic boundary-marking model
is asserted. Nonemptiness is necessary: the essential supremum on an empty
domain is zero, while every admissible distortion constant is at least one.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter

open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The infimum of the distortion constants of an actual quasiconformal map.
The results below use this definition only when the admissible set is nonempty. -/
def infimalDilatation (f : ℂ → ℂ) (D : Set ℂ) : ℝ :=
  sInf {K : ℝ | LiZhongQC.IsKQC f D K}

/-- The proved analytic/geometric equivalence preserves the entire admissible set,
and therefore the literal infimum of distortion constants. -/
theorem infimalDilatation_eq_analytic_inf (f : ℂ → ℂ) (D : Set ℂ) :
    infimalDilatation f D = sInf {K : ℝ | IsAnalyticallyKQuasiconformal f D K} := by
  apply congrArg sInf
  ext K
  exact geometric_iff_analytic

/-- On a nonempty domain the essential distortion quotient is at least one. -/
theorem one_le_essential_dilatation {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (hne : D.Nonempty) :
    1 ≤ LiZhongQC.maxDilatation f D := by
  have hμ : volume.restrict D ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact hf.1.measure_ne_zero volume hne
  calc
    (1 : ℝ≥0∞) = essSup (fun _ : ℂ => (1 : ℝ≥0∞)) (volume.restrict D) :=
      (essSup_const _ hμ).symm
    _ ≤ LiZhongQC.maxDilatation f D := by
      refine essSup_mono_ae ?_
      filter_upwards [LiZhongQC.thm9_6_cor2_jacobian_pos hf] with z hz
      unfold LiZhongQC.jacobian at hz
      have hlt : ‖LiZhongQC.dzbar f z‖ < ‖LiZhongQC.dz f z‖ := by
        nlinarith [norm_nonneg (LiZhongQC.dz f z), norm_nonneg (LiZhongQC.dzbar f z)]
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [le_div_iff₀ (by linarith)]
      linarith [norm_nonneg (LiZhongQC.dzbar f z)]

/-- An actual quasiconformal map attains every bound above its essential quotient. -/
theorem quasiconformal_of_essential_dilatation_le
    {f : ℂ → ℂ} {D : Set ℂ} {L K : ℝ}
    (hf : LiZhongQC.IsKQC f D L) (hK : 1 ≤ K)
    (hle : LiZhongQC.maxDilatation f D ≤ ENNReal.ofReal K) :
    LiZhongQC.IsKQC f D K := by
  refine (LiZhongQC.thm10_1_isKQC_iff hf.1 hK hf.2.2.1).mpr
    ⟨LiZhongQC.thm9_1_isACL hf, ?_⟩
  filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict D)
      (fun z => ENNReal.ofReal ((‖LiZhongQC.dz f z‖ + ‖LiZhongQC.dzbar f z‖) /
        (‖LiZhongQC.dz f z‖ - ‖LiZhongQC.dzbar f z‖))),
    LiZhongQC.thm9_6_cor2_jacobian_pos hf] with z hz hJ
  unfold LiZhongQC.jacobian at hJ
  have hlt : ‖LiZhongQC.dzbar f z‖ < ‖LiZhongQC.dz f z‖ := by
    nlinarith [norm_nonneg (LiZhongQC.dz f z), norm_nonneg (LiZhongQC.dzbar f z)]
  have hbound : ENNReal.ofReal ((‖LiZhongQC.dz f z‖ + ‖LiZhongQC.dzbar f z‖) /
      (‖LiZhongQC.dz f z‖ - ‖LiZhongQC.dzbar f z‖)) ≤ ENNReal.ofReal K := hz.trans hle
  rw [ENNReal.ofReal_le_ofReal_iff (by linarith), div_le_iff₀ (by linarith)] at hbound
  exact hbound

/-- Admissible constants are exactly the constants bounding the essential quotient. -/
theorem quasiconformal_iff_essential_dilatation_le
    {f : ℂ → ℂ} {D : Set ℂ} {L K : ℝ}
    (hf : LiZhongQC.IsKQC f D L) (hK : 1 ≤ K) :
    LiZhongQC.IsKQC f D K ↔ LiZhongQC.maxDilatation f D ≤ ENNReal.ofReal K :=
  ⟨fun h => (LiZhongQC.isKQC_maxDilatation_le h).1,
    quasiconformal_of_essential_dilatation_le hf hK⟩

/-- The essential quotient is finite, and its real value is an attained admissible bound. -/
theorem essential_dilatation_attained {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (hne : D.Nonempty) :
    LiZhongQC.maxDilatation f D ≠ ⊤ ∧
      1 ≤ (LiZhongQC.maxDilatation f D).toReal ∧
        LiZhongQC.IsKQC f D (LiZhongQC.maxDilatation f D).toReal := by
  have hfin : LiZhongQC.maxDilatation f D ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (LiZhongQC.isKQC_maxDilatation_le hf).1
  have hone : 1 ≤ (LiZhongQC.maxDilatation f D).toReal := by
    simpa using ENNReal.toReal_mono hfin (one_le_essential_dilatation hf hne)
  exact ⟨hfin, hone, quasiconformal_of_essential_dilatation_le hf hone
    (ENNReal.ofReal_toReal hfin).ge⟩

/-- The infimum definition agrees with the essential supremum of the actual
Wirtinger quotient, with no extra distortion or differentiability hypothesis. -/
theorem infimalDilatation_eq_essential_quotient {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (hne : D.Nonempty) :
    infimalDilatation f D = (LiZhongQC.maxDilatation f D).toReal := by
  obtain ⟨_, _, hattained⟩ := essential_dilatation_attained hf hne
  apply IsLeast.csInf_eq
  refine ⟨hattained, ?_⟩
  intro L hL
  have hupper := (LiZhongQC.isKQC_maxDilatation_le hL).1
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
  simpa only [ENNReal.toReal_ofReal (zero_le_one.trans hL.2.1)] using hreal

/-- The infimum is itself a valid distortion constant. -/
theorem infimalDilatation_isKQC {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (hne : D.Nonempty) :
    LiZhongQC.IsKQC f D (infimalDilatation f D) := by
  rw [infimalDilatation_eq_essential_quotient hf hne]
  exact (essential_dilatation_attained hf hne).2.2

/-- The infimal distortion constant is at least one. -/
theorem one_le_infimalDilatation {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (hne : D.Nonempty) : 1 ≤ infimalDilatation f D :=
  (infimalDilatation_isKQC hf hne).2.1

/-- Unit infimal distortion is exactly conformality. -/
theorem infimalDilatation_eq_one_iff_conformal {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (hne : D.Nonempty) :
    infimalDilatation f D = 1 ↔ LiZhongQC.IsConformalOnto f D (f '' D) := by
  constructor
  · intro h
    have hopt := infimalDilatation_isKQC hf hne
    rw [h] at hopt
    exact LiZhongQC.thm7_3_one_qc_conformal hopt
  · intro h
    apply le_antisymm ?_ (one_le_infimalDilatation hf hne)
    rw [infimalDilatation_eq_essential_quotient hf hne]
    have hupper := (LiZhongQC.isKQC_maxDilatation_le
      (LiZhongQC.isKQC_one_of_conformal hf.1 h)).1
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
    simpa using hreal

end LowDimensionalTopology.Geometry.Quasiconformal
