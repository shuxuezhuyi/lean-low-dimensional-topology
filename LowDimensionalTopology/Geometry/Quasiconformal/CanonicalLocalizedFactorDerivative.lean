module

public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalCoefficientLocalization
public import LowDimensionalTopology.Geometry.Quasiconformal.CompactCanonicalImageControl
public import LowDimensionalTopology.Geometry.Quasiconformal.NormalizedSolutionContinuity
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The actual uncut canonical map's holomorphic local factor

The auxiliary coefficient is derived internally from each original measurable
coefficient. Near zero coefficient, the actual cutoff image contains the fixed
larger disc, and the actual holomorphic factor converges uniformly there to
identity. Mathlib's Cauchy convergence theorem then gives uniform convergence
of its derivative on the fixed smaller closed disc.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- The actual native coefficient cut down on the larger disc. -/
abbrev canonicalBallFourCutoff (μ : MeasurableBeltramiBall) : MeasurableBeltramiBall :=
  canonicalCoefficientCutoff μ (ball 0 4) measurableSet_ball

/-- The actual holomorphic coordinate factor is a composition of the two
canonical maps, not an additional supplied function. -/
def canonicalLocalizedFactor (μ : MeasurableBeltramiBall) : ℂ ≃ₜ ℂ :=
  (MeasurableBeltramiBall.normalizedSolution (canonicalBallFourCutoff μ)).symm.trans
    (MeasurableBeltramiBall.normalizedSolution μ)

theorem canonicalBallFourCutoff_norm_tendsto_zero {ι : Type*} {l : Filter ι}
    (μ : ι → MeasurableBeltramiBall)
    (hμ : Tendsto (fun i => ‖(μ i).val‖) l (𝓝 0)) :
    Tendsto (fun i => ‖(canonicalBallFourCutoff (μ i)).val‖) l (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _)
    (fun i => canonicalCoefficientCutoff_norm_le (μ i) _ measurableSet_ball) hμ

private theorem canonical_error_on_closedBall {ι : Type*} {l : Filter ι}
    (μ : ι → MeasurableBeltramiBall)
    (hμ : Tendsto (fun i => ‖(μ i).val‖) l (𝓝 0)) (r ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ z ∈ closedBall (0 : ℂ) r,
      ‖MeasurableBeltramiBall.normalizedSolution (μ i) z - z‖ < ε := by
  have hclass : Tendsto (fun i => (μ i).val) l (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hμ
  have h := tendstoLocallyUniformly_iff_forall_isCompact.mp
    (normalizedSolution_tendstoLocallyUniformly_zero μ hclass)
    (closedBall (0 : ℂ) r) (isCompact_closedBall _ _)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h ε hε] with i hi
  intro z hz
  simpa only [id_eq, dist_eq_norm, norm_sub_rev] using hi z hz

/-- The variable cutoff image eventually contains the fixed disc of radius two. -/
theorem canonicalBallFourCutoff_eventually_covers_ball_two
    {ι : Type*} {l : Filter ι} (μ : ι → MeasurableBeltramiBall)
    (hμ : Tendsto (fun i => ‖(μ i).val‖) l (𝓝 0)) :
    ∀ᶠ i in l, ball (0 : ℂ) 2 ⊆
      (MeasurableBeltramiBall.normalizedSolution (canonicalBallFourCutoff (μ i))) '' ball 0 3 := by
  filter_upwards [canonical_error_on_closedBall
    (fun i => canonicalBallFourCutoff (μ i))
    (canonicalBallFourCutoff_norm_tendsto_zero μ hμ) 3 1 zero_lt_one] with i hi
  exact homeomorph_ball_two_subset_image_ball_three _ hi

/-- Holomorphy holds eventually on a genuine fixed open domain. -/
theorem canonicalLocalizedFactor_eventually_differentiableOn_ball_two
    {ι : Type*} {l : Filter ι} (μ : ι → MeasurableBeltramiBall)
    (hμ : Tendsto (fun i => ‖(μ i).val‖) l (𝓝 0)) :
    ∀ᶠ i in l, DifferentiableOn ℂ (canonicalLocalizedFactor (μ i)) (ball 0 2) := by
  filter_upwards [canonicalBallFourCutoff_eventually_covers_ball_two μ hμ] with i hi
  have h := (normalizedSolution_cutoff_conformal_factor (μ i) (ball 0 4) isOpen_ball).1
  apply h.mono
  intro w hw
  obtain ⟨z, hz, hzw⟩ := hi hw
  exact ⟨z, (ball_subset_ball (by norm_num : (3 : ℝ) ≤ 4)) hz, hzw⟩

/-- The actual outer factor tends uniformly to identity on the whole fixed disc. -/
theorem canonicalLocalizedFactor_tendstoUniformlyOn_ball_two
    {ι : Type*} {l : Filter ι} (μ : ι → MeasurableBeltramiBall)
    (hμ : Tendsto (fun i => ‖(μ i).val‖) l (𝓝 0)) :
    TendstoUniformlyOn (fun i z => canonicalLocalizedFactor (μ i) z)
      (id : ℂ → ℂ) l (ball 0 2) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [canonicalBallFourCutoff_eventually_covers_ball_two μ hμ,
    canonical_error_on_closedBall μ hμ 3 (ε / 2) (by positivity),
    canonical_error_on_closedBall (fun i => canonicalBallFourCutoff (μ i))
      (canonicalBallFourCutoff_norm_tendsto_zero μ hμ) 3 (ε / 2) (by positivity)]
    with i hcover hF hG
  intro w hw
  obtain ⟨z, hz, hzw⟩ := hcover hw
  have hzc := ball_subset_closedBall hz
  have hfactor : canonicalLocalizedFactor (μ i) w =
      MeasurableBeltramiBall.normalizedSolution (μ i) z := by
    rw [← hzw]
    simp only [canonicalLocalizedFactor, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  rw [id_eq, dist_comm, dist_eq_norm, hfactor, ← hzw]
  calc
    _ = ‖(MeasurableBeltramiBall.normalizedSolution (μ i) z - z) -
        (MeasurableBeltramiBall.normalizedSolution (canonicalBallFourCutoff (μ i)) z - z)‖ := by
      congr 1
      ring
    _ ≤ ‖MeasurableBeltramiBall.normalizedSolution (μ i) z - z‖ +
        ‖MeasurableBeltramiBall.normalizedSolution (canonicalBallFourCutoff (μ i)) z - z‖ :=
      norm_sub_le _ _
    _ < ε := by linarith [hF z hzc, hG z hzc]

/-- Mathlib's Cauchy theorem controls the actual spatial derivative uniformly
on the fixed smaller closed disc, with no assumption of a derivative bound. -/
theorem canonicalLocalizedFactor_deriv_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι} (μ : ι → MeasurableBeltramiBall)
    (hμ : Tendsto (fun i => ‖(μ i).val‖) l (𝓝 0)) :
    TendstoUniformlyOn (fun i => deriv (canonicalLocalizedFactor (μ i))) (fun _ => (1 : ℂ))
      l (closedBall 0 (3 / 2)) := by
  have hloc := TendstoUniformlyOn.tendstoLocallyUniformlyOn
    (canonicalLocalizedFactor_tendstoUniformlyOn_ball_two μ hμ)
  have h := hloc.deriv
    (canonicalLocalizedFactor_eventually_differentiableOn_ball_two μ hμ) isOpen_ball
  have hsub : closedBall (0 : ℂ) (3 / 2) ⊆ ball 0 2 := by
    intro z hz
    rw [mem_ball_zero_iff]
    have hz' := mem_closedBall_zero_iff.mp hz
    linarith
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp h
    (closedBall 0 (3 / 2)) hsub (isCompact_closedBall _ _)
  have hη : (deriv ∘ fun i z => canonicalLocalizedFactor (μ i) z) =
      (fun i => deriv (canonicalLocalizedFactor (μ i) : ℂ → ℂ)) := by
    funext i
    exact congrArg deriv (funext fun _ => rfl)
  rw [hη] at hu
  simpa only [deriv_id'] using hu

/-- The smaller original disc is eventually carried inside the fixed compact
set where the outer derivatives converge uniformly. -/
theorem canonicalBallFourCutoff_eventually_maps_ball_one
    {ι : Type*} {l : Filter ι} (μ : ι → MeasurableBeltramiBall)
    (hμ : Tendsto (fun i => ‖(μ i).val‖) l (𝓝 0)) :
    ∀ᶠ i in l, MapsTo
      (MeasurableBeltramiBall.normalizedSolution (canonicalBallFourCutoff (μ i)))
      (ball 0 1) (closedBall 0 (3 / 2)) := by
  filter_upwards [canonical_error_on_closedBall (fun i => canonicalBallFourCutoff (μ i))
    (canonicalBallFourCutoff_norm_tendsto_zero μ hμ) 3 (1 / 2) (by norm_num)] with i hi
  intro z hz
  rw [mem_closedBall_zero_iff]
  have hz1 := mem_ball_zero_iff.mp hz
  have hzc : z ∈ closedBall (0 : ℂ) 3 :=
    mem_closedBall_zero_iff.mpr (by linarith)
  have ht := norm_add_le
    (MeasurableBeltramiBall.normalizedSolution (canonicalBallFourCutoff (μ i)) z - z) z
  rw [sub_add_cancel] at ht
  linarith [hi z hzc]

end LowDimensionalTopology.Geometry.Quasiconformal
