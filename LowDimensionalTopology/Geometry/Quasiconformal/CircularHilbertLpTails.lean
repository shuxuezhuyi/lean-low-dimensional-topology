/-
The truncated-kernel integrability API is reused from Wu Xiaobin's
Li-Zhong-QC-formalization, commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch02.S11_IntegralOperators
public import LowDimensionalTopology.Geometry.Quasiconformal.RealDirectionalHilbert

/-!
# Genuine circular-kernel tails for planar Lp functions

Outside a fixed positive radius the circular kernel has exactly the same
norm as the existing integrable squared Cauchy kernel. This applies to
noncompact functions and separates local principal values from ordinary
integrable tails.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Translate the literal radial truncation to the original integration variable. -/
theorem circularHilbertTruncation_eq_original_integral (φ : ℂ → ℂ) (z : ℂ) (r : ℝ) :
    circularHilbertTruncation φ z r =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ w in {w : ℂ | r < ‖w - z‖}, φ w / ((w - z) * (‖w - z‖ : ℂ)) := by
  have hemb : MeasurableEmbedding (fun w : ℂ => w + z) :=
    (Homeomorph.addRight z).isClosedEmbedding.measurableEmbedding
  have hpre : (fun w : ℂ => w + z) ⁻¹' {w : ℂ | r < ‖w - z‖} =
      {w : ℂ | r < ‖w‖} := by
    ext w
    simp only [mem_preimage, mem_ofPred_eq, add_sub_cancel_right]
  have ht := (measurePreserving_add_right volume z).setIntegral_preimage_emb hemb
    (fun w : ℂ => φ w / ((w - z) * (‖w - z‖ : ℂ)))
    {w : ℂ | r < ‖w - z‖}
  rw [hpre] at ht
  simpa only [circularHilbertTruncation, add_sub_cancel_right] using
    congrArg (fun a : ℂ => (1 / (2 * (Real.pi : ℂ))) * a) ht

/-- The actual circular tail kernel is integrable for every planar Lp
function with exponent greater than one, without a compact-support premise. -/
theorem integrableOn_circularHilbertKernel {p : ℝ} (hp : 1 < p) {φ : ℂ → ℂ}
    (hφ : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ)) (z : ℂ)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun w : ℂ => φ w / ((w - z) * (‖w - z‖ : ℂ)))
      {w : ℂ | r < ‖w - z‖} (volume : Measure ℂ) := by
  have hi := LiZhongQC.integrableOn_truncated_kernel hp hφ z hr
  have hm' : AEMeasurable
      (fun w : ℂ => φ w / ((w - z) * (‖w - z‖ : ℂ))) (volume : Measure ℂ) :=
    hφ.aestronglyMeasurable.aemeasurable.div
      (((measurable_id.sub_const z).mul
        (measurable_ofReal.comp (measurable_id.sub_const z).norm)).aemeasurable)
  have hm : AEStronglyMeasurable
      (fun w : ℂ => φ w / ((w - z) * (‖w - z‖ : ℂ))) (volume : Measure ℂ) :=
    hm'.aestronglyMeasurable
  refine Integrable.mono hi hm.restrict (Eventually.of_forall fun w => ?_)
  exact le_of_eq (by
    simp only [norm_div, norm_mul, Complex.norm_real, norm_norm, pow_two])

/-- A difference which vanishes in one closed neighborhood of the
pole contributes one ordinary tail integral at every smaller truncation. -/
theorem integral_circularHilbertKernel_sub_eq_tail {φ ψ : ℂ → ℂ}
    (z : ℂ) {r ε : ℝ} (hεr : ε < r)
    (hlocal : ∀ w : ℂ, ‖w - z‖ ≤ r → φ w = ψ w) :
    (∫ w in {w : ℂ | ε < ‖w - z‖},
      (φ w - ψ w) / ((w - z) * (‖w - z‖ : ℂ))) =
      ∫ w in {w : ℂ | r < ‖w - z‖},
        (φ w - ψ w) / ((w - z) * (‖w - z‖ : ℂ)) := by
  have hmeas : MeasurableSet {w : ℂ | ε < ‖w - z‖} :=
    measurableSet_lt measurable_const (measurable_id.sub_const z).norm
  have hsub : {w : ℂ | r < ‖w - z‖} ⊆ {w : ℂ | ε < ‖w - z‖} :=
    fun w hw => hεr.trans hw
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub
  intro w hw
  have hwle : ‖w - z‖ ≤ r := le_of_not_gt hw.2
  rw [hlocal w hwle, sub_self, zero_div]

/-- Subtracting two genuine positive-radius circular truncations is an
ordinary integral of their difference. -/
theorem circularHilbertTruncation_sub {p : ℝ} (hp : 1 < p) {φ ψ : ℂ → ℂ}
    (hφ : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ))
    (hψ : MemLp ψ (ENNReal.ofReal p) (volume : Measure ℂ))
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    circularHilbertTruncation (fun w => φ w - ψ w) z ε =
      circularHilbertTruncation φ z ε - circularHilbertTruncation ψ z ε := by
  rw [circularHilbertTruncation_eq_original_integral,
    circularHilbertTruncation_eq_original_integral,
    circularHilbertTruncation_eq_original_integral]
  simp_rw [sub_div]
  rw [integral_sub (integrableOn_circularHilbertKernel hp hφ z hε)
    (integrableOn_circularHilbertKernel hp hψ z hε), mul_sub]

end LowDimensionalTopology.Geometry.Quasiconformal
