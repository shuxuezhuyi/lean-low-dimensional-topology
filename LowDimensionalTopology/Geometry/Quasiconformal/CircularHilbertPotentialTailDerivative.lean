module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertKernel
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertRenormalizedKernel
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertLpTails
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Differentiating the actual potential tail away from its input support

A difference vanishing near the evaluation point has no moving kernel
pole on its support. The original planar Lp tail estimate dominates its
actual parameter derivative. Only integrability at the evaluation point
is required; the compact-test iteration supplies that fact separately.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex Metric

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem norm_fderiv_inverseNormKernel_tail_le {v : ℂ} (hv : v ≠ 0) :
    ‖fderiv ℝ inverseNormKernel v‖ ≤ (‖v‖ ^ 2)⁻¹ := by
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [(hasFDerivAt_inverseNormKernel hv).fderiv]
  calc
    ‖Complex.ofRealCLM.comp ((-(‖v‖ ^ 3)⁻¹) • innerSL ℝ v)‖ ≤
        ‖Complex.ofRealCLM‖ * ‖(-(‖v‖ ^ 3)⁻¹) • innerSL ℝ v‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = (‖v‖ ^ 3)⁻¹ * ‖v‖ := by
      rw [Complex.ofRealCLM_norm, one_mul, norm_smul, innerSL_apply_norm]
      simp only [Real.norm_eq_abs, abs_neg, abs_inv, abs_pow,
        abs_of_nonneg (norm_nonneg v)]
    _ = (‖v‖ ^ 2)⁻¹ := by field_simp [hv0.ne']

/-- A function vanishing near the evaluation point has a differentiable
renormalized potential whenever its actual value integral is integrable.
The derivative is the integral of the original kernel derivative. -/
theorem hasFDerivAt_renormalizedInverseNormPotential_of_vanishing {p : ℝ}
    (hp : 1 < p) {d : ℂ → ℂ}
    (hd : MemLp d (ENNReal.ofReal p) (volume : Measure ℂ)) (z : ℂ)
    {r : ℝ} (hr : 0 < r)
    (hzero : ∀ t : ℂ, ‖t - z‖ ≤ r → d t = 0)
    (hint : Integrable (fun t : ℂ => d t * renormalizedInverseNormKernel t z)
      (volume : Measure ℂ)) :
    HasFDerivAt (renormalizedInverseNormPotential d)
      (∫ t : ℂ, d t • ((fderiv ℝ inverseNormKernel (t - z)).comp
        (-ContinuousLinearMap.id ℝ ℂ))) z := by
  let F : ℂ → ℂ → ℂ := fun x t => d t * renormalizedInverseNormKernel t x
  let D : ℂ → ℂ → ℂ →L[ℝ] ℂ := fun x t => d t •
    ((fderiv ℝ inverseNormKernel (t - x)).comp (-ContinuousLinearMap.id ℝ ℂ))
  let B : ℂ → ℝ := fun t => 4 * ‖d t / (t - z) ^ 2‖
  let s : Set ℂ := {t : ℂ | r < ‖t - z‖}
  have hKmeas : Measurable inverseNormKernel :=
    (measurable_ofReal.comp measurable_norm).inv
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const (measurable_id.sub_const z).norm
  have hBint : Integrable B (volume : Measure ℂ) := by
    have hi : IntegrableOn B s (volume : Measure ℂ) :=
      (LiZhongQC.integrableOn_truncated_kernel hp hd z hr).norm.const_mul 4
    have hi' : Integrable (s.indicator B) (volume : Measure ℂ) :=
      (integrable_indicator_iff hs).mpr hi
    apply hi'.congr
    apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ s
    · exact indicator_of_mem ht B
    · rw [indicator_of_notMem ht]
      have htz : ‖t - z‖ ≤ r := le_of_not_gt ht
      simp only [B, hzero t htz, zero_div, norm_zero, mul_zero]
  have hgeom (t : ℂ) (ht : d t ≠ 0) (x : ℂ) (hx : x ∈ ball z (r / 2)) :
      t - x ≠ 0 ∧ ‖t - z‖ ≤ 2 * ‖t - x‖ := by
    have htz : r < ‖t - z‖ := lt_of_not_ge fun h => ht (hzero t h)
    have hxz : ‖x - z‖ < r / 2 := by
      simpa only [mem_ball, dist_eq_norm] using hx
    have htri : ‖t - z‖ ≤ ‖t - x‖ + ‖x - z‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (t - x) (x - z)
    constructor
    · apply norm_pos_iff.mp
      linarith
    · linarith
  have hDmeas : AEStronglyMeasurable (D z) (volume : Measure ℂ) := by
    have hcomp : Continuous
        (fun A : ℂ →L[ℝ] ℂ => A.comp (-ContinuousLinearMap.id ℝ ℂ)) :=
      continuous_id.clm_comp_const _
    have hfd : Measurable (fun t : ℂ => fderiv ℝ inverseNormKernel (t - z)) :=
      (measurable_fderiv ℝ inverseNormKernel).comp (measurable_id.sub_const z)
    exact hd.aestronglyMeasurable.smul
      (hcomp.measurable.comp hfd).aestronglyMeasurable
  have hbound (t x : ℂ) (hx : x ∈ ball z (r / 2)) : ‖D x t‖ ≤ B t := by
    by_cases ht : d t = 0
    · simp only [D, B, ht, zero_smul, norm_zero, zero_div, mul_zero, le_refl]
    · obtain ⟨htx, hcompdist⟩ := hgeom t ht x hx
      have hv : 0 < ‖t - z‖ := hr.trans
        (lt_of_not_ge fun h => ht (hzero t h))
      have hu : 0 < ‖t - x‖ := norm_pos_iff.mpr htx
      have hsq : ‖t - z‖ ^ 2 ≤ 4 * ‖t - x‖ ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hcompdist)
          (by positivity : 0 ≤ 2 * ‖t - x‖ + ‖t - z‖)]
      have hinv : (‖t - x‖ ^ 2)⁻¹ ≤ 4 * (‖t - z‖ ^ 2)⁻¹ := by
        calc
          (‖t - x‖ ^ 2)⁻¹ = 1 / ‖t - x‖ ^ 2 := (one_div _).symm
          _ ≤ 4 / ‖t - z‖ ^ 2 :=
            (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by
              simpa only [one_mul] using hsq)
          _ = 4 * (‖t - z‖ ^ 2)⁻¹ := div_eq_mul_inv _ _
      have hcompnorm : ‖(fderiv ℝ inverseNormKernel (t - x)).comp
          (-ContinuousLinearMap.id ℝ ℂ)‖ ≤ ‖fderiv ℝ inverseNormKernel (t - x)‖ := by
        simpa only [norm_neg, ContinuousLinearMap.norm_id, mul_one] using
          ContinuousLinearMap.opNorm_comp_le
            (fderiv ℝ inverseNormKernel (t - x)) (-ContinuousLinearMap.id ℝ ℂ)
      calc
        ‖D x t‖ = ‖d t‖ * ‖(fderiv ℝ inverseNormKernel (t - x)).comp
            (-ContinuousLinearMap.id ℝ ℂ)‖ := norm_smul _ _
        _ ≤ ‖d t‖ * (‖t - x‖ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left
            (hcompnorm.trans (norm_fderiv_inverseNormKernel_tail_le htx)) (norm_nonneg _)
        _ ≤ ‖d t‖ * (4 * (‖t - z‖ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
        _ = B t := by
          change ‖d t‖ * (4 * (‖t - z‖ ^ 2)⁻¹) =
            4 * ‖d t / (t - z) ^ 2‖
          rw [norm_div, norm_pow, div_eq_mul_inv]
          ring
  have hdiff (t x : ℂ) (hx : x ∈ ball z (r / 2)) :
      HasFDerivAt (fun y : ℂ => F y t) (D x t) x := by
    by_cases ht : d t = 0
    · have hconst : HasFDerivAt (fun _ : ℂ => (0 : ℂ)) (0 : ℂ →L[ℝ] ℂ) x :=
        hasFDerivAt_const (0 : ℂ) x
      simpa only [F, D, ht, zero_mul, zero_smul] using hconst
    · have hk := (hasFDerivAt_inverseNormKernel
        (hgeom t ht x hx).1).differentiableAt.hasFDerivAt
      have hshift : HasFDerivAt (fun y : ℂ => inverseNormKernel (t - y))
          ((fderiv ℝ inverseNormKernel (t - x)).comp
            (-ContinuousLinearMap.id ℝ ℂ)) x :=
        hk.comp x ((hasFDerivAt_id x).const_sub t)
      have hfun : (d t) • (fun y : ℂ => inverseNormKernel (t - y) - inverseNormKernel t) =
          fun y : ℂ => F y t := by
        funext y
        simp only [F, renormalizedInverseNormKernel, Pi.smul_apply, smul_eq_mul]
      rw [← hfun]
      exact (hshift.sub_const (inverseNormKernel t)).const_smul (d t)
  change HasFDerivAt (fun x : ℂ => ∫ t : ℂ, F x t) (∫ t : ℂ, D z t) z
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := F) (F' := D) (s := ball z (r / 2)) (bound := B)
    (ball_mem_nhds z (by positivity)) ?_ hint hDmeas
    (Eventually.of_forall fun t => fun x hx => hbound t x hx) hBint
    (Eventually.of_forall fun t => fun x hx => hdiff t x hx)
  apply Eventually.of_forall
  intro x
  exact hd.aestronglyMeasurable.mul
    (((hKmeas.comp (measurable_id.sub_const x)).sub hKmeas).aestronglyMeasurable)

end LowDimensionalTopology.Geometry.Quasiconformal
