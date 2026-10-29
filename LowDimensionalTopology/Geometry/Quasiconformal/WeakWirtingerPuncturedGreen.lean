module

public import LowDimensionalTopology.Geometry.Quasiconformal.WeakWirtingerPunctureCutoff
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Green's formula with an integrable puncture

Apply the genuine weak cutoff formula to two concentric discs. Subtraction
cancels the cutoff contribution exactly. The true inner-circle trace then
tends to zero under a power bound of exponent greater than minus one.
This does not impose a value or continuity at the puncture.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open scoped ContDiff
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The two genuine weak Green identities give the actual annular formula
for a continuous punctured function, without differentiability assumptions. -/
theorem annular_green_of_distributional_wirtinger
    {U : Set ℂ} {f g h : ℂ → ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f (U \ {0}))
    (hw : HasDistributionalWirtingerDerivatives f g h (U \ {0}))
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) (hsub : closedBall (0 : ℂ) R ⊆ U) :
    CircleIntegrable f 0 R ∧ CircleIntegrable f 0 ε ∧
      IntegrableOn h (ball (0 : ℂ) R \ ball 0 ε) ∧
      (∮ z in C(0, R), f z) - (∮ z in C(0, ε), f z) =
        2 * I * ∫ z in ball (0 : ℂ) R \ ball 0 ε, h z := by
  have hR : 0 < R := hε.trans hεR
  let b : ContDiffBump (0 : ℂ) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let χ : ℂ → ℂ := fun z => 1 - (b z : ℂ)
  have hχ : ContDiff ℝ ∞ χ :=
    contDiff_const.sub (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hzero : ∀ z ∈ ball (0 : ℂ) (ε / 4), χ z = 0 := by
    intro z hz
    have hb : b z = 1 := b.one_of_mem_closedBall (by
      simpa only [b, mem_closedBall, dist_zero_right] using (mem_ball_zero_iff.mp hz).le)
    simp only [χ, hb, Complex.ofReal_one, sub_self]
  have hone : ∀ z : ℂ, ε / 2 ≤ ‖z‖ → χ z = 1 := by
    intro z hz
    have hb : b z = 0 := b.zero_of_le_dist (by
      simpa only [b, dist_zero_right] using hz)
    simp only [χ, hb, Complex.ofReal_zero, sub_zero]
  have hd : ∀ z : ℂ, ε / 2 < ‖z‖ → dzbar χ z = 0 := by
    intro z hz
    have hev : χ =ᶠ[𝓝 z] fun _ => (1 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
      exact hone w hw.le
    rw [dzbar_congr_of_eventuallyEq hev]
    simp only [dzbar, fderiv_const_apply, _root_.zero_apply,
      mul_zero, add_zero, zero_div]
  let v : ℂ → ℂ := fun z => χ z * h z + dzbar χ z * f z
  have hweak := HasDistributionalWirtingerDerivatives.cutoff_puncture hU hw hχ
    (by positivity : 0 < ε / 4) hzero
  have hcut := continuousOn_puncture_cutoff hU hf hχ.continuous
    (by positivity : 0 < ε / 4) hzero
  obtain ⟨hcirR, hGR⟩ := green_of_distributional_wirtinger hU hcut hweak hR hsub
  obtain ⟨hcirε, hGε⟩ := green_of_distributional_wirtinger hU hcut hweak hε
    ((closedBall_subset_closedBall hεR.le).trans hsub)
  have hcircle : ∀ r : ℝ, ε ≤ r →
      EqOn (fun z => χ z * f z) f (sphere (0 : ℂ) r) := by
    intro r hr z hz
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    change χ z * f z = f z
    rw [hone z (by rw [hz']; linarith), one_mul]
  have hcR := circleIntegral.integral_congr hR.le (hcircle R hεR.le)
  have hcε := circleIntegral.integral_congr hε.le (hcircle ε le_rfl)
  have hi : IntegrableOn v (ball (0 : ℂ) R) :=
    (hweak.2.2.1.integrableOn_compact_subset hsub (isCompact_closedBall 0 R)).mono_set
      ball_subset_closedBall
  have hbsub : ball (0 : ℂ) ε ⊆ ball 0 R := ball_subset_ball hεR.le
  have hsplit : (∫ z in ball (0 : ℂ) R, v z) = (∫ z in ball (0 : ℂ) ε, v z) +
      ∫ z in ball (0 : ℂ) R \ ball 0 ε, v z := by
    rw [← setIntegral_union (Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx))
      (measurableSet_ball.diff measurableSet_ball) (hi.mono_set hbsub)
      (hi.mono_set sdiff_subset), union_sdiff_cancel hbsub]
  have heq : EqOn v h (ball (0 : ℂ) R \ ball 0 ε) := by
    intro z hz
    have hge : ε ≤ ‖z‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hz.2
    change χ z * h z + dzbar χ z * f z = h z
    rw [hone z (by linarith), hd z (by linarith), one_mul, zero_mul, add_zero]
  have hi' : IntegrableOn h (ball (0 : ℂ) R \ ball 0 ε) :=
    (integrableOn_congr_fun heq (measurableSet_ball.diff measurableSet_ball)).mp
      (hi.mono_set sdiff_subset)
  refine ⟨(circleIntegrable_congr (by
      simpa only [abs_of_pos hR] using (hcircle R hεR.le))).mp hcirR,
    (circleIntegrable_congr (by
      simpa only [abs_of_pos hε] using (hcircle ε le_rfl))).mp hcirε, hi', ?_⟩
  rw [← hcR, ← hcε, hGR, hGε, hsplit,
    setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball) heq]
  ring

private theorem punctured_area_integral_tendsto {h : ℂ → ℂ} {R : ℝ}
    (hi : IntegrableOn h (ball (0 : ℂ) R)) :
    Tendsto (fun ε : ℝ => ∫ z in ball (0 : ℂ) R \ ball 0 ε, h z)
      (𝓝[>] 0) (𝓝 (∫ z in ball (0 : ℂ) R, h z)) := by
  have ht : Tendsto (fun ε : ℝ => ∫ z in ball (0 : ℂ) R,
      (ball (0 : ℂ) ε)ᶜ.indicator h z) (𝓝[>] 0)
      (𝓝 (∫ z in ball (0 : ℂ) R, h z)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖h z‖)
      (Eventually.of_forall fun ε => hi.aestronglyMeasurable.indicator measurableSet_ball.compl)
      (Eventually.of_forall fun ε => Eventually.of_forall fun z =>
        norm_indicator_le_norm_self h z) hi.norm ?_
    filter_upwards [(volume.restrict (ball (0 : ℂ) R)).ae_ne 0] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (norm_pos_iff.mpr hz))] with ε hε
    have hz' : z ∈ (ball (0 : ℂ) ε)ᶜ := by
      simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hε.le
    exact (indicator_of_mem hz' h).symm
  convert ht using 1
  funext ε
  rw [integral_indicator measurableSet_ball.compl, Measure.restrict_restrict measurableSet_ball.compl]
  have hs : (ball (0 : ℂ) ε)ᶜ ∩ ball (0 : ℂ) R = ball (0 : ℂ) R \ ball 0 ε := by
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff, and_comm]
  rw [hs]

/-- A true continuous punctured trace with growth exponent greater than
minus one satisfies Green's formula when its actual weak derivative is L1.
The puncture value of the original function is unrestricted. -/
theorem green_of_distributional_wirtinger_puncture
    {U : Set ℂ} {f g h : ℂ → ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f (U \ {0}))
    (hw : HasDistributionalWirtingerDerivatives f g h (U \ {0}))
    {R : ℝ} (hR : 0 < R) (hsub : closedBall (0 : ℂ) R ⊆ U)
    (hi : IntegrableOn h (ball (0 : ℂ) R))
    {C α δ : ℝ} (hα : -1 < α) (hδ : 0 < δ)
    (hbound : ∀ z ∈ ball (0 : ℂ) δ \ {0}, ‖f z‖ ≤ C * ‖z‖ ^ α) :
    CircleIntegrable f 0 R ∧
      (∮ z in C(0, R), f z) = 2 * I * ∫ z in ball (0 : ℂ) R, h z := by
  have hsmall : Tendsto (fun ε : ℝ => ∮ z in C(0, ε), f z) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa only [mul_zero] using
        ((tendsto_id.mono_right nhdsWithin_le_nhds).rpow_const_nhds_zero
          (by linarith : 0 < α + 1)).const_mul (2 * Real.pi * C))
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    have hb : ∀ z ∈ sphere (0 : ℂ) ε, ‖f z‖ ≤ C * ε ^ α := by
      intro z hz
      have hn : ‖z‖ = ε := by simpa only [mem_sphere, dist_zero_right] using hz
      have hn0 : z ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact hε.1)
      have hzδ : z ∈ ball (0 : ℂ) δ \ {0} := by
        exact ⟨by simpa only [mem_ball, dist_zero_right, hn] using hε.2,
          by simpa only [mem_singleton_iff] using hn0⟩
      simpa only [hn] using hbound z hzδ
    calc
      ‖∮ z in C(0, ε), f z‖ ≤ 2 * Real.pi * ε * (C * ε ^ α) :=
        circleIntegral.norm_integral_le_of_norm_le_const hε.1.le hb
      _ = (2 * Real.pi * C) * ε ^ (α + 1) := by
        rw [Real.rpow_add hε.1, Real.rpow_one]
        ring
  have hleft : Tendsto (fun ε : ℝ => (∮ z in C(0, R), f z) -
      (∮ z in C(0, ε), f z)) (𝓝[>] 0) (𝓝 (∮ z in C(0, R), f z)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hsmall
  have hright := (punctured_area_integral_tendsto hi).const_mul (2 * I)
  have he : (fun ε : ℝ => (∮ z in C(0, R), f z) - (∮ z in C(0, ε), f z)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => 2 * I * ∫ z in ball (0 : ℂ) R \ ball 0 ε, h z) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with ε hε
    exact (annular_green_of_distributional_wirtinger hU hf hw hε.1 hε.2 hsub).2.2.2
  have hcir := (annular_green_of_distributional_wirtinger hU hf hw
    (by positivity : 0 < R / 2) (by linarith : R / 2 < R) hsub).1
  exact ⟨hcir, tendsto_nhds_unique hleft (hright.congr' he.symm)⟩

end LowDimensionalTopology.Geometry.Quasiconformal
