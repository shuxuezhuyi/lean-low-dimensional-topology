module

public import LowDimensionalTopology.Geometry.Quasiconformal.CompactCanonicalDerivativeBounds

/-!
# Same-exponent Lp stability for the actual compact-cutoff canonical maps

For every prescribed p > 2, coefficients tending to zero in the genuine
L-infinity norm give convergence of the actual canonical Wirtinger derivative
to one in Lp on the unit disc. The contraction condition and the lower bound
on the normalizing value follow internally and eventually. This is the
compact-cutoff ingredient, not the full localization lemma for arbitrary
coefficients.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- The actual canonical compact-cutoff solutions have same-p derivative
convergence on the unit disc. No prescribed derivative, normalizing value,
or compact support assumption on an uncut original coefficient is used. -/
theorem canonicalCompact_derivative_tendsto_one {ι : Type*} {l : Filter ι}
    {p : ℝ} (hp : 2 < p) (μ : ι → MeasurableBeltramiBall)
    (hsupp : ∀ i, ∀ᵐ z ∂(volume : Measure ℂ), z ∉ ball 0 4 → (μ i).val z = 0)
    (hμ : Tendsto (fun i => ‖(μ i).val‖) l (𝓝 0)) :
    (∀ᶠ i in l, MemLp
      (fun z => dz (MeasurableBeltramiBall.normalizedSolution (μ i)) z - 1)
      (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1))) ∧
      Tendsto (fun i => (eLpNorm
        (fun z => dz (MeasurableBeltramiBall.normalizedSolution (μ i)) z - 1)
        (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1))).toReal) l (𝓝 0) := by
  obtain ⟨Kp, _, hbound⟩ := canonicalCompact_derivative_lp_bound hp
  let Cp := smoothHilbertNorm p
  let V := planarBallLpVolume p 4
  let B : ι → ℝ := fun i => V * ‖(μ i).val‖ / (1 - ‖(μ i).val‖ * Cp)
  let C := 2 * (Cp + planarBallLpVolume p 1 * Kp)
  have hk : Tendsto (fun i => ‖(μ i).val‖ * Cp) l (𝓝 0) := by
    simpa only [zero_mul] using hμ.mul_const Cp
  have hsmall : ∀ᶠ i in l, ‖(μ i).val‖ * Cp < 1 :=
    hk.eventually_lt_const zero_lt_one
  have hnum : Tendsto (fun i => V * ‖(μ i).val‖) l (𝓝 0) := by
    simpa only [mul_zero] using hμ.const_mul V
  have hden : Tendsto (fun i => 1 - ‖(μ i).val‖ * Cp) l (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hk
  have hB : Tendsto B l (𝓝 0) := by
    simpa only [B, Pi.div_def, zero_div] using hnum.div hden one_ne_zero
  have hnormal : ∀ᶠ i in l, Kp * B i ≤ 1 / 2 := by
    have h : Tendsto (fun i => Kp * B i) l (𝓝 0) := by
      simpa only [mul_zero] using hB.const_mul Kp
    exact h.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hest : ∀ᶠ i in l,
      MemLp (fun z => dz (MeasurableBeltramiBall.normalizedSolution (μ i)) z - 1)
          (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1)) ∧
        (eLpNorm (fun z => dz (MeasurableBeltramiBall.normalizedSolution (μ i)) z - 1)
          (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1))).toReal ≤ C * B i := by
    filter_upwards [hsmall, hnormal] with i hi hnorm
    exact hbound (μ i) (hsupp i) hi hnorm
  refine ⟨hest.mono (fun _ hi => hi.1), ?_⟩
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    (hest.mono (fun _ hi => hi.2))
  simpa only [mul_zero] using hB.const_mul C

end LowDimensionalTopology.Geometry.Quasiconformal
