module

public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiSolution

/-!
# Localizing the actual canonical plane solution by a derived coefficient cutoff

The input is any original full-plane measurable coefficient in the unit ball.
The cutoff stays in that same native ball with no larger norm. Its actual
canonical normalized solution gives a genuine coordinate in which the original
canonical map is holomorphic on the cutoff domain. No support or smoothness
condition is imposed on the original input coefficient.

This is a localization ingredient; convergence of spatial derivatives in a
prescribed Lp norm is a separate analytic statement.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Metric
open LiZhongQC
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- The genuine coefficient class cut down to the chosen measurable domain. -/
def canonicalCoefficientCutoff (μ : MeasurableBeltramiBall)
    (D : Set ℂ) (hD : MeasurableSet D) : MeasurableBeltramiBall :=
  MeasurableBeltramiBall.ofCoefficient (norm_nonneg μ.val)
    (MeasurableBeltramiBall.norm_lt_one μ)
    (ahF_indicator_beltrami hD (MeasurableBeltramiSpace.isBeltramiCoeff μ.val))

/-- The derived native class is the actual indicator coefficient almost everywhere. -/
theorem canonicalCoefficientCutoff_coe_ae (μ : MeasurableBeltramiBall)
    (D : Set ℂ) (hD : MeasurableSet D) :
    ((canonicalCoefficientCutoff μ D hD).val : ℂ → ℂ) =ᵐ[volume]
      D.indicator (μ.val : ℂ → ℂ) :=
  MeasurableBeltramiBall.ofCoefficient_coe_ae (norm_nonneg μ.val)
    (MeasurableBeltramiBall.norm_lt_one μ)
    (ahF_indicator_beltrami hD (MeasurableBeltramiSpace.isBeltramiCoeff μ.val))

/-- Cutting down the original coefficient never increases its actual infinity norm. -/
theorem canonicalCoefficientCutoff_norm_le (μ : MeasurableBeltramiBall)
    (D : Set ℂ) (hD : MeasurableSet D) :
    ‖(canonicalCoefficientCutoff μ D hD).val‖ ≤ ‖μ.val‖ := by
  apply lpInfinity_norm_le_of_ae_bound _ (norm_nonneg μ.val)
  filter_upwards [canonicalCoefficientCutoff_coe_ae μ D hD,
    lpInfinity_norm_ae_le μ.val] with z hz hμz
  rw [hz]
  exact (norm_indicator_le_norm_self (μ.val : ℂ → ℂ) z).trans hμz

/-- The bounded support belongs to the internally constructed coefficient;
it is not a restriction on the original full-plane coefficient. -/
theorem canonicalCoefficientCutoff_ball_compactSupport (μ : MeasurableBeltramiBall)
    (r : ℝ) : HasCompactEssentialSupport
      ((canonicalCoefficientCutoff μ (ball 0 r) measurableSet_ball).val : ℂ → ℂ) := by
  refine ⟨closedBall 0 r, isCompact_closedBall _ _, ?_⟩
  filter_upwards [canonicalCoefficientCutoff_coe_ae μ (ball 0 r) measurableSet_ball]
    with z hz
  intro hzr
  rw [hz]
  exact indicator_of_notMem (fun hzb => hzr (ball_subset_closedBall hzb)) _

/-- The actual original canonical map, divided on the right by the actual
canonical cutoff map, is holomorphic throughout the cutoff image. -/
theorem normalizedSolution_cutoff_conformal_factor (μ : MeasurableBeltramiBall)
    (D : Set ℂ) (hD : IsOpen D) :
    let ν := canonicalCoefficientCutoff μ D hD.measurableSet
    let F := MeasurableBeltramiBall.normalizedSolution μ
    let G := MeasurableBeltramiBall.normalizedSolution ν
    DifferentiableOn ℂ (G.symm.trans F) (G '' D) ∧
      ∀ z : ℂ, F z = (G.symm.trans F) (G z) := by
  let ν := canonicalCoefficientCutoff μ D hD.measurableSet
  let F := MeasurableBeltramiBall.normalizedSolution μ
  let G := MeasurableBeltramiBall.normalizedSolution ν
  have hF := MeasurableBeltramiBall.normalizedSolution_spec μ
  have hG := MeasurableBeltramiBall.normalizedSolution_spec ν
  have heq : ∀ᵐ z ∂(volume.restrict D),
      complexDilatation F z = complexDilatation G z := by
    filter_upwards [ae_restrict_of_ae hF.1.2.2.2.2,
      ae_restrict_of_ae hG.1.2.2.2.2,
      ae_restrict_of_ae (canonicalCoefficientCutoff_coe_ae μ D hD.measurableSet),
      ae_restrict_mem hD.measurableSet] with z hf hg hcut hz
    rw [hf, hg, hcut, indicator_of_mem hz]
  obtain ⟨φ, hφ, hrepr⟩ := nxS_factor hD
    (nx_isKQC_restrict hF.2.1 hD (subset_univ D))
    (nx_isKQC_restrict hG.2.1 hD (subset_univ D)) heq
  have hpoint : ∀ z : ℂ, (G.symm.trans F) (G z) = F z := by
    intro z
    simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  refine ⟨?_, fun z => (hpoint z).symm⟩
  intro w hw
  exact (nxS_differentiableAt G hD hpoint hφ.1 hrepr hw).differentiableWithinAt

/-- A fixed larger disc supplies a compact coefficient and an actual
holomorphic outer factor for every original canonical normalized plane map. -/
theorem normalizedSolution_discCutoff_localization (μ : MeasurableBeltramiBall) :
    ∃ ν : MeasurableBeltramiBall, ‖ν.val‖ ≤ ‖μ.val‖ ∧
      HasCompactEssentialSupport (ν.val : ℂ → ℂ) ∧
      DifferentiableOn ℂ
        ((MeasurableBeltramiBall.normalizedSolution ν).symm.trans
          (MeasurableBeltramiBall.normalizedSolution μ))
        ((MeasurableBeltramiBall.normalizedSolution ν) '' ball 0 4) ∧
      ∀ z : ℂ, MeasurableBeltramiBall.normalizedSolution μ z =
        ((MeasurableBeltramiBall.normalizedSolution ν).symm.trans
          (MeasurableBeltramiBall.normalizedSolution μ))
          (MeasurableBeltramiBall.normalizedSolution ν z) := by
  let ν := canonicalCoefficientCutoff μ (ball 0 4) measurableSet_ball
  exact ⟨ν, canonicalCoefficientCutoff_norm_le μ _ measurableSet_ball,
    canonicalCoefficientCutoff_ball_compactSupport μ 4,
    (normalizedSolution_cutoff_conformal_factor μ (ball 0 4) isOpen_ball).1,
    (normalizedSolution_cutoff_conformal_factor μ (ball 0 4) isOpen_ball).2⟩

end LowDimensionalTopology.Geometry.Quasiconformal
