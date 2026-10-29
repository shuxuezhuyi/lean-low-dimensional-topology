module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertLpTails
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertPrincipalValue
public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertSmoothLpApproximation
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Radial principal values for smooth functions in the original planar Lp

A compact smooth cutoff retains the function in a neighborhood of the pole.
The remainder has an ordinary integrable tail, so the radial principal value
exists without assigning an unproved directional integral to a noncompact
function.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- A compact smooth local representative supplies the local principal
value, and the remaining difference contributes its genuine integrable tail. -/
theorem tendsto_circularHilbertTruncation_of_local_compact {p : ℝ} (hp : 1 < p)
    {φ ψ : ℂ → ℂ}
    (hφ : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ))
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hlocal : ∀ w : ℂ, ‖w - z‖ ≤ r → φ w = ψ w) :
    Tendsto (circularHilbertTruncation φ z) (𝓝[>] (0 : ℝ))
      (𝓝 (circularHilbertTransform ψ z + (1 / (2 * (Real.pi : ℂ))) *
        ∫ w in {w : ℂ | r < ‖w - z‖},
          (φ w - ψ w) / ((w - z) * (‖w - z‖ : ℂ)))) := by
  have hψmem : MemLp ψ (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hψ.continuous.memLp_of_hasCompactSupport hcψ
  have hlim := (hasCircularHilbertPrincipalValue hψ hcψ z).add
    (tendsto_const_nhds (x := (1 / (2 * (Real.pi : ℂ))) *
      ∫ w in {w : ℂ | r < ‖w - z‖},
        (φ w - ψ w) / ((w - z) * (‖w - z‖ : ℂ))))
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
  have hsub := circularHilbertTruncation_sub hp hφ hψmem z hε.1
  rw [circularHilbertTruncation_eq_original_integral,
    integral_circularHilbertKernel_sub_eq_tail z hε.2 hlocal] at hsub
  linear_combination hsub

/-- Every smooth function in the actual planar Lp space has a genuine radial
principal value. The `limUnder` value is used only after proving convergence. -/
theorem tendsto_circularHilbertTruncation_smoothLp {p : ℝ} (hp : 1 < p)
    {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hmem : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ)) (z : ℂ) :
    Tendsto (circularHilbertTruncation φ z) (𝓝[>] (0 : ℝ))
      (𝓝 (radialCircularHilbertTransform φ z)) := by
  let χ : ContDiffBump z := ⟨1, 2, by norm_num, by norm_num⟩
  let ψ : ℂ → ℂ := fun w => χ w • φ w
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := χ.contDiff.smul hφ
  have hcψ : HasCompactSupport ψ := χ.hasCompactSupport.smul_right
  have hlocal (w : ℂ) (hw : ‖w - z‖ ≤ 1) : φ w = ψ w := by
    have hχ : χ w = 1 := χ.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hw)
    simp only [ψ, hχ, one_smul]
  have ht := tendsto_circularHilbertTruncation_of_local_compact hp hmem hψ hcψ z
    (by norm_num : (0 : ℝ) < 1) hlocal
  change Tendsto (circularHilbertTruncation φ z) (𝓝[>] (0 : ℝ))
    (𝓝 (limUnder (𝓝[>] (0 : ℝ)) (circularHilbertTruncation φ z)))
  exact tendsto_nhds_limUnder ⟨_, ht⟩

/-- The original compact-test circular transforms converge pointwise to
the genuine radial principal value of a smooth Lp function. -/
theorem circularHilbertTransform_cutoffApprox_tendsto {p : ℝ} (hp : 1 < p)
    {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hmem : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ)) (z : ℂ) :
    Tendsto (fun n : ℕ => circularHilbertTransform (circularSmoothLpCutoffApprox φ n) z)
      atTop (𝓝 (radialCircularHilbertTransform φ z)) := by
  let s : Set ℂ := {w : ℂ | 1 < ‖w - z‖}
  let F : ℕ → ℂ → ℂ := fun n w =>
    (φ w - circularSmoothLpCutoffApprox φ n w) / ((w - z) * (‖w - z‖ : ℂ))
  have hint : IntegrableOn (fun w : ℂ => φ w / ((w - z) * (‖w - z‖ : ℂ)))
      s (volume : Measure ℂ) :=
    integrableOn_circularHilbertKernel hp hmem z (by norm_num)
  have hFm : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (F n) (volume.restrict s) := by
    apply Eventually.of_forall
    intro n
    have hm : Measurable (F n) :=
      (hφ.continuous.sub (contDiff_circularSmoothLpCutoffApprox hφ n).continuous).measurable.div
        ((measurable_id.sub_const z).mul
          (measurable_ofReal.comp (measurable_id.sub_const z).norm))
    exact hm.aestronglyMeasurable.restrict
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ w ∂(volume.restrict s),
      ‖F n w‖ ≤ ‖φ w / ((w - z) * (‖w - z‖ : ℂ))‖ := by
    apply Eventually.of_forall
    intro n
    apply Eventually.of_forall
    intro w
    dsimp only [F]
    rw [norm_div, norm_div, norm_sub_rev]
    exact div_le_div_of_nonneg_right (norm_circularSmoothLpCutoffApprox_sub_le φ n w)
      (norm_nonneg _)
  have hpoint : ∀ᵐ w ∂(volume.restrict s),
      Tendsto (fun n : ℕ => F n w) atTop (𝓝 (0 : ℂ)) := by
    apply Eventually.of_forall
    intro w
    have heq : (fun n : ℕ => F n w) =ᶠ[atTop] fun _ => (0 : ℂ) := by
      filter_upwards [circularSmoothLpCutoffApprox_eventually_eq φ w] with n hn
      simp only [F, hn, sub_self, zero_div]
    exact tendsto_const_nhds.congr' heq.symm
  have htail := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict s) (F := F) (f := fun _ => (0 : ℂ))
    (fun w => ‖φ w / ((w - z) * (‖w - z‖ : ℂ))‖)
    hFm hbound hint.norm hpoint
  simp only [integral_zero] at htail
  have hscaled := htail.const_mul (1 / (2 * (Real.pi : ℂ)))
  simp only [mul_zero] at hscaled
  have hlim := (tendsto_const_nhds (x := radialCircularHilbertTransform φ z)).sub hscaled
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop ⌈‖z‖ + 1⌉₊] with n hn
  have hnlarge : ‖z‖ + 1 ≤ (n : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn.le)
  have hlocal (w : ℂ) (hw : ‖w - z‖ ≤ 1) :
      φ w = circularSmoothLpCutoffApprox φ n w := by
    symm
    apply circularSmoothLpCutoffApprox_eq
    calc
      ‖w‖ ≤ ‖w - z‖ + ‖z‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + ‖z‖ := by linarith only [hw]
      _ ≤ (n : ℝ) := by linarith
  have hlocalLim := tendsto_circularHilbertTruncation_of_local_compact hp hmem
    (contDiff_circularSmoothLpCutoffApprox hφ n)
    (hasCompactSupport_circularSmoothLpCutoffApprox φ n) z
    (by norm_num : (0 : ℝ) < 1) hlocal
  have heq := hlocalLim.limUnder_eq
  change radialCircularHilbertTransform φ z =
    circularHilbertTransform (circularSmoothLpCutoffApprox φ n) z +
      (1 / (2 * (Real.pi : ℂ))) * ∫ w in s, F n w at heq
  linear_combination heq

end LowDimensionalTopology.Geometry.Quasiconformal
