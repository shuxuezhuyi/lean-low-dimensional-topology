module

public import LowDimensionalTopology.Geometry.Quasiconformal.CompactCanonicalNormalRepresentation
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Prescribed-exponent bounds on the actual compact-cutoff canonical derivative

The ball volume is literal planar volume. The affine normalizing factor is
obtained from the actual normalized solution, rather than supplied as data.
The same prescribed p and original singular-transform norm occur throughout.
The fixed-point estimates originate in Wu Xiaobin's Apache-2.0 LiZhongQC
formalization; see THIRD_PARTY_NOTICES.md.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- The exact finite-volume factor in the planar Lp norm of a constant. -/
def planarBallLpVolume (p r : ℝ) : ℝ :=
  (volume (ball (0 : ℂ) r) ^ (ENNReal.ofReal p).toReal⁻¹).toReal

theorem planarBallLpVolume_nonneg (p r : ℝ) : 0 ≤ planarBallLpVolume p r :=
  ENNReal.toReal_nonneg

/-- Essential support on the actual ball, not pointwise support of a privileged
representative, suffices for the exact coefficient Lp bound. -/
theorem compactCoefficient_lp_bound (p : ℝ) (μ : MeasurableBeltramiBall)
    (hsupp : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ ball 0 4 → μ.val z = 0) :
    (eLpNorm (μ.val : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal ≤
      planarBallLpVolume p 4 * ‖μ.val‖ := by
  have heq : (μ.val : ℂ → ℂ) =ᵐ[volume]
      (ball (0 : ℂ) 4).indicator (μ.val : ℂ → ℂ) := by
    filter_upwards [hsupp] with z hz
    by_cases hzin : z ∈ ball (0 : ℂ) 4
    · rw [indicator_of_mem hzin]
    · rw [indicator_of_notMem hzin, hz hzin]
  have hb := eLpNorm_le_of_ae_bound (p := ENNReal.ofReal p)
    (μ := (volume : Measure ℂ).restrict (ball 0 4))
    (Lp.aestronglyMeasurable μ.val).restrict
    (ae_restrict_of_ae (lpInfinity_norm_ae_le μ.val))
  rw [Measure.restrict_apply_univ] at hb
  rw [eLpNorm_congr_ae heq,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet]
  have hfinite : volume (ball (0 : ℂ) 4) ^ (ENNReal.ofReal p).toReal⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      measure_ball_lt_top.ne
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hfinite ENNReal.ofReal_ne_top) hb
  simpa only [planarBallLpVolume, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (norm_nonneg _)] using h

private theorem affineHilbert_lp_bound {p : ℝ} (hp : 2 < p)
    {ω : ℂ → ℂ} (hω : MemLp ω (ENNReal.ofReal p) (volume : Measure ℂ))
    {a : ℂ} (ha : a ≠ 0) :
    MemLp (fun z => (1 + hilbertH ω z) / a - 1) (ENNReal.ofReal p)
        (volume.restrict (ball (0 : ℂ) 1)) ∧
      (eLpNorm (fun z => (1 + hilbertH ω z) / a - 1) (ENNReal.ofReal p)
        (volume.restrict (ball (0 : ℂ) 1))).toReal ≤
        (smoothHilbertNorm p * (eLpNorm ω (ENNReal.ofReal p) volume).toReal +
          ‖a - 1‖ * planarBallLpVolume p 1) / ‖a‖ := by
  have hp1 : 1 < p := lt_trans one_lt_two hp
  have hp1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp1.le
  have hq0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  let m : Measure ℂ := volume.restrict (ball (0 : ℂ) 1)
  let : IsFiniteMeasure m := ⟨by
    dsimp only [m]
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hH := hilbertH_memLp hp1 hω
  have hHr : MemLp (hilbertH ω) (ENNReal.ofReal p) m := hH.restrict _
  have hc : MemLp (fun _ : ℂ => a - 1) (ENNReal.ofReal p) m := memLp_const _
  let v : ℂ → ℂ := fun z => hilbertH ω z - (a - 1)
  have hv : MemLp v (ENNReal.ofReal p) m := hHr.sub hc
  have heq : (fun z => (1 + hilbertH ω z) / a - 1) = a⁻¹ • v := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, v]
    field_simp [ha]
    ring
  have hconst : (eLpNorm (fun _ : ℂ => a - 1) (ENNReal.ofReal p) m).toReal =
      ‖a - 1‖ * planarBallLpVolume p 1 := by
    rw [eLpNorm_const' _ hq0 ENNReal.ofReal_ne_top, ← ofReal_norm,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    simp only [m, Measure.restrict_apply_univ, one_div, planarBallLpVolume]
  have htri := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hHr.eLpNorm_ne_top, hc.eLpNorm_ne_top⟩)
    (eLpNorm_sub_le (f := hilbertH ω) (g := fun _ : ℂ => a - 1) (μ := m) hp1e)
  rw [ENNReal.toReal_add hHr.eLpNorm_ne_top hc.eLpNorm_ne_top, hconst] at htri
  have hrestrict := ENNReal.toReal_mono hH.eLpNorm_ne_top
    (eLpNorm_mono_measure (p := ENNReal.ofReal p) (hilbertH ω)
      (Measure.restrict_le_self (s := ball (0 : ℂ) 1)))
  have hbound : (eLpNorm (hilbertH ω) (ENNReal.ofReal p) m).toReal ≤
      smoothHilbertNorm p * (eLpNorm ω (ENNReal.ofReal p) volume).toReal := by
    apply hrestrict.trans
    simpa only [smoothHilbertNorm_eq_hilbertNorm hp1] using eq11_16 hp1 hω
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hv.const_smul a⁻¹
  rw [heq, eLpNorm_const_smul, ← ofReal_norm, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (norm_nonneg _), norm_inv, div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg a))
  exact htri.trans (add_le_add hbound le_rfl)

/-- Quantitative control of the actual canonical derivative. The only extra
smallness here is the explicit scalar estimate ensuring the normalizing value
stays at least one half away from zero. It follows automatically as the
coefficient norm tends to zero. -/
theorem canonicalCompact_derivative_lp_bound {p : ℝ} (hp : 2 < p) :
    ∃ Kp : ℝ, 0 ≤ Kp ∧ ∀ μ : MeasurableBeltramiBall,
      (∀ᵐ z ∂(volume : Measure ℂ), z ∉ ball 0 4 → μ.val z = 0) →
      ‖μ.val‖ * smoothHilbertNorm p < 1 →
      Kp * (planarBallLpVolume p 4 * ‖μ.val‖ /
        (1 - ‖μ.val‖ * smoothHilbertNorm p)) ≤ 1 / 2 →
      MemLp (fun z => dz (MeasurableBeltramiBall.normalizedSolution μ) z - 1)
          (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1)) ∧
        (eLpNorm (fun z => dz (MeasurableBeltramiBall.normalizedSolution μ) z - 1)
          (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1))).toReal ≤
          2 * (smoothHilbertNorm p + planarBallLpVolume p 1 * Kp) *
            (planarBallLpVolume p 4 * ‖μ.val‖ /
              (1 - ‖μ.val‖ * smoothHilbertNorm p)) := by
  obtain ⟨Kp, hKp, hrep⟩ := canonicalCompact_normalRepresentation hp
  refine ⟨Kp, hKp, ?_⟩
  intro μ hsupp hsmall hnormal
  obtain ⟨ω, a, hω, hωbound, ha, hanorm, _, hdz⟩ := hrep μ hsupp hsmall
  let B := planarBallLpVolume p 4 * ‖μ.val‖ / (1 - ‖μ.val‖ * smoothHilbertNorm p)
  have hB0 : 0 ≤ B := div_nonneg
    (mul_nonneg (planarBallLpVolume_nonneg _ _) (norm_nonneg _)) (sub_pos.mpr hsmall).le
  have hW : (eLpNorm ω (ENNReal.ofReal p) volume).toReal ≤ B :=
    hωbound.trans (div_le_div_of_nonneg_right (compactCoefficient_lp_bound p μ hsupp)
      (sub_pos.mpr hsmall).le)
  have haone : ‖a - 1‖ ≤ 1 / 2 :=
    hanorm.trans ((mul_le_mul_of_nonneg_left hW hKp).trans hnormal)
  have haNorm : 1 / 2 ≤ ‖a‖ := by
    have h := norm_sub_le a (a - 1)
    rw [sub_sub_cancel, norm_one] at h
    linarith
  obtain ⟨hm, hb⟩ := affineHilbert_lp_bound hp hω ha
  have heq : (fun z => dz (MeasurableBeltramiBall.normalizedSolution μ) z - 1)
      =ᵐ[volume.restrict (ball (0 : ℂ) 1)] (fun z => (1 + hilbertH ω z) / a - 1) :=
    by
      filter_upwards [ae_restrict_of_ae hdz] with z hz
      exact congrArg (fun u : ℂ => u - 1) hz
  refine ⟨MemLp.ae_eq heq.symm hm, ?_⟩
  rw [eLpNorm_congr_ae heq]
  have hCp : 0 ≤ smoothHilbertNorm p := by
    rw [smoothHilbertNorm_eq_hilbertNorm (lt_trans one_lt_two hp)]
    exact hilbertNorm_nonneg p
  have hV := planarBallLpVolume_nonneg p 1
  apply hb.trans
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) haNorm)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hW hCp,
    mul_le_mul_of_nonneg_left hanorm hV,
    mul_le_mul_of_nonneg_left hW (mul_nonneg hV hKp),
    mul_le_mul_of_nonneg_left haNorm
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (add_nonneg hCp (mul_nonneg hV hKp))) hB0)]

end LowDimensionalTopology.Geometry.Quasiconformal
