/-
The cutoff and two-disc Green proof pattern is adapted from Wu Xiaobin's
Li-Zhong-QC-formalization, commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertKernel

/-!
# The inverse-norm Green identity on a punctured disc

A smooth cutoff removes the pole before applying the existing ordinary
Green theorem twice. The unmodified inverse-norm kernel is recovered on
the actual annulus, retaining its inner boundary term.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem contDiffAt_shiftedInverseNormKernel {z w : ℂ} (hw : w ≠ z) :
    ContDiffAt ℝ 1 (fun v : ℂ => inverseNormKernel (v - z)) w := by
  have hn : ContDiffAt ℝ 1 (fun v : ℂ => ‖v - z‖) w :=
    (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hw)
  have he : ContDiffAt ℝ 1 (fun v : ℂ => (‖v - z‖ : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w hn
  exact he.inv (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw)))

private theorem dz_shiftedInverseNormKernel {z w : ℂ} (hw : w ≠ z) :
    LiZhongQC.dz (fun v : ℂ => inverseNormKernel (v - z)) w =
      -(1 / 2 : ℂ) * (1 / ((w - z) * (‖w - z‖ : ℂ))) := by
  have hd0 := hasFDerivAt_inverseNormKernel (sub_ne_zero.mpr hw)
  have hd := hd0.comp w ((hasFDerivAt_id w).sub_const z)
  have heq : fderiv ℝ (fun v : ℂ => inverseNormKernel (v - z)) w =
      fderiv ℝ inverseNormKernel (w - z) := by
    have hfd := hd.fderiv
    simp only [Function.comp_def, id_eq] at hfd
    rw [hfd, hd0.fderiv]
    simp
  have hs : LiZhongQC.dz (fun v : ℂ => inverseNormKernel (v - z)) w =
      LiZhongQC.dz inverseNormKernel (w - z) := by simp only [LiZhongQC.dz, heq]
  have h := dz_negTwo_inverseNormKernel (sub_ne_zero.mpr hw)
  rw [LiZhongQC.dz_mul (differentiableAt_const (-2 : ℂ)) hd0.differentiableAt] at h
  have hc : LiZhongQC.dz (fun _ : ℂ => (-2 : ℂ)) (w - z) = 0 := by
    simp [LiZhongQC.dz]
  rw [hc, mul_zero, add_zero] at h
  rw [hs]
  linear_combination (-1 / 2 : ℂ) * h

private theorem exists_inverseNorm_cutoff (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ 1 χ ∧
      (∀ w ∈ ball z (r / 2), χ w = 0) ∧
      (∀ w : ℂ, r ≤ ‖w - z‖ → χ w = 1) ∧
      ContDiff ℝ 1 (fun w => χ w * inverseNormKernel (w - z)) := by
  obtain ⟨χ, hχ, hzero, hone, _⟩ := LiZhongQC.exists_kernel_cutoff z hr
  refine ⟨χ, hχ, hzero, hone, ?_⟩
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = z
  · subst w
    have hevent : (fun v : ℂ => χ v * inverseNormKernel (v - z)) =ᶠ[𝓝 z]
        fun _ => (0 : ℂ) := by
      filter_upwards [ball_mem_nhds z (by positivity : (0 : ℝ) < r / 2)] with v hv
      rw [hzero v hv, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hevent
  · exact hχ.contDiffAt.mul (contDiffAt_shiftedInverseNormKernel hw)

/-- Green's identity for the literal inverse-norm kernel on an annulus
whose outer circle has zero test values. -/
theorem integral_ball_diff_inverseNorm_dz {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {z : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hvan : ∀ θ : ℝ, φ (circleMap z R θ) = 0) :
    (∫ w in ball z R \ ball z r,
      inverseNormKernel (w - z) * LiZhongQC.dz φ w -
        (1 / 2 : ℂ) * φ w / ((w - z) * (‖w - z‖ : ℂ))) =
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        (inverseNormKernel (circleMap z r θ - z) * φ (circleMap z r θ)) *
          conj (deriv (circleMap z r) θ)) / (2 * I) := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨χ, _, _, hχ1, hχK⟩ := exists_inverseNorm_cutoff z hr
  let u : ℂ → ℂ := fun w => (χ w * inverseNormKernel (w - z)) * φ w
  have hu : ContDiff ℝ 1 u := hχK.mul hφ
  have hG1 := LiZhongQC.green_disc_dz_closedBall (c := z) hR hu.contDiffOn
  have hG2 := LiZhongQC.green_disc_dz_closedBall (c := z) hr hu.contDiffOn
  have hc1 (θ : ℝ) : u (circleMap z R θ) = 0 := by
    simp only [u, hvan θ, mul_zero]
  have hc2 (θ : ℝ) : u (circleMap z r θ) =
      inverseNormKernel (circleMap z r θ - z) * φ (circleMap z r θ) := by
    have h1 : r ≤ ‖circleMap z r θ - z‖ := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
    simp only [u, hχ1 _ h1, one_mul]
  simp only [hc1, zero_mul, intervalIntegral.integral_zero] at hG1
  simp only [hc2] at hG2
  have hint : IntegrableOn (LiZhongQC.dz u) (ball z R) :=
    ((LiZhongQC.continuous_dz hu).continuousOn.integrableOn_compact
      (isCompact_closedBall z R)).mono_set ball_subset_closedBall
  have hsplit := setIntegral_sdiff (μ := volume) measurableSet_ball hint
    (ball_subset_ball hrR.le)
  have h0 : ∫ w in ball z R, LiZhongQC.dz u w = 0 :=
    (mul_eq_zero.mp hG1.symm).resolve_left (by simp)
  have heq : (∫ w in ball z R \ ball z r, LiZhongQC.dz u w) =
      ∫ w in ball z R \ ball z r,
        inverseNormKernel (w - z) * LiZhongQC.dz φ w -
          (1 / 2 : ℂ) * φ w / ((w - z) * (‖w - z‖ : ℂ)) := by
    apply setIntegral_congr_ae (measurableSet_ball.diff measurableSet_ball)
    have hsphere : ∀ᵐ w : ℂ, w ∉ sphere z r := by
      rw [ae_iff]
      exact measure_mono_null (fun a ha => not_not.mp ha)
        (Measure.addHaar_sphere (volume : Measure ℂ) z r)
    filter_upwards [hsphere] with w hws hw
    have hge : r ≤ ‖w - z‖ := by
      have h := hw.2
      rwa [mem_ball, dist_eq_norm, not_lt] at h
    have hgt : r < ‖w - z‖ :=
      lt_of_le_of_ne hge fun h => hws (by rw [mem_sphere, dist_eq_norm]; exact h.symm)
    have hne : w ≠ z := by
      intro h
      rw [h, sub_self, norm_zero] at hgt
      linarith
    have hevent : u =ᶠ[𝓝 w] fun v => inverseNormKernel (v - z) * φ v := by
      have hopen : IsOpen {v : ℂ | r < ‖v - z‖} :=
        isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
      filter_upwards [hopen.mem_nhds hgt] with v hv
      simp only [u, hχ1 v hv.le, one_mul]
    rw [show LiZhongQC.dz u w =
        LiZhongQC.dz (fun v => inverseNormKernel (v - z) * φ v) w by
          simp only [LiZhongQC.dz, hevent.fderiv_eq],
      LiZhongQC.dz_mul
        ((contDiffAt_shiftedInverseNormKernel hne).differentiableAt one_ne_zero)
        ((hφ.differentiable one_ne_zero) w), dz_shiftedInverseNormKernel hne]
    ring
  rw [← heq, hsplit, h0, zero_sub, hG2,
    show (-2 * I * ∫ w in ball z r, LiZhongQC.dz u w) =
      -((∫ w in ball z r, LiZhongQC.dz u w) * (2 * I)) by ring,
    neg_div, mul_div_cancel_right₀ _ (by simp : (2 * I : ℂ) ≠ 0)]

end LowDimensionalTopology.Geometry.Quasiconformal
