module

public import LowDimensionalTopology.Geometry.Quasiconformal.WirtingerWeakApproximation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Green's formula from genuine local L1 weak Wirtinger data

The boundary values are the original continuous function on an open
neighborhood of the closed disc. Actual compact smooth approximants converge
uniformly on that disc and in L1 for their weak derivatives. The formula is
therefore valid with local L1 data, without a C1 premise or an arbitrary
choice of boundary values for an L1 class.

Uses the credited LiZhongQC Green formula and the native proved mollifier
approximation; see THIRD_PARTY_NOTICES.md.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The actual continuous boundary trace and the actual local L1 weak
antiholomorphic derivative satisfy Green's formula on every enclosed disc. -/
theorem green_of_distributional_wirtinger
    {U : Set ℂ} {f g h : ℂ → ℂ} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hw : HasDistributionalWirtingerDerivatives f g h U)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hsub : closedBall c R ⊆ U) :
    CircleIntegrable f c R ∧
      (∮ z in C(c, R), f z) = 2 * I * ∫ z in ball c R, h z := by
  have hloc : ∀ C ⊆ U, IsCompact C →
      MemLp g 1 (volume.restrict C) ∧ MemLp h 1 (volume.restrict C) := by
    intro C hCU hC
    exact ⟨memLp_one_iff_integrable.mpr (hw.2.1.integrableOn_compact_subset hCU hC),
      memLp_one_iff_integrable.mpr (hw.2.2.1.integrableOn_compact_subset hCU hC)⟩
  obtain ⟨φ, hφ, hval, _, hbar⟩ := exists_smooth_compact_wirtinger_approximation
    hU hf hw le_rfl (by simp : (1 : ℝ≥0∞) ≠ ⊤) hloc (isCompact_closedBall c R) hsub
  have hbarBall : Tendsto (fun n => eLpNorm (fun z => dzbar (φ n) z - h z)
      1 (volume.restrict (ball c R))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbar
      (fun _ => bot_le) (fun n => ?_)
    exact eLpNorm_mono_measure _ (Measure.restrict_mono ball_subset_closedBall le_rfl)
  have hI : Tendsto (fun n => ∫ z in ball c R, dzbar (φ n) z) atTop
      (𝓝 (∫ z in ball c R, h z)) := by
    apply tendsto_integral_of_L1' h
      (Eventually.of_forall fun n => ?_) (by simpa only [Pi.sub_def] using hbarBall)
    exact ((continuous_dzbar ((hφ n).1.of_le (by simp))).continuousOn.integrableOn_compact
      (isCompact_closedBall c R)).mono_set ball_subset_closedBall
  have hcircle : Tendsto (fun n => ∮ z in C(c, R), φ n z) atTop
      (𝓝 (∮ z in C(c, R), f z)) :=
    TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn hR.le
      (Eventually.of_forall fun n => (hφ n).1.continuous.continuousOn)
      (hval.mono sphere_subset_closedBall)
  have hright : Tendsto (fun n => ∮ z in C(c, R), φ n z) atTop
      (𝓝 (2 * I * ∫ z in ball c R, h z)) := by
    apply (hI.const_mul (2 * I)).congr'
    exact Eventually.of_forall fun n =>
      (eq11_9_green_dz hR ((hφ n).1.of_le (by simp)).contDiffOn).symm
  exact ⟨(hf.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable hR.le,
    tendsto_nhds_unique hcircle hright⟩

end LowDimensionalTopology.Geometry.Quasiconformal
