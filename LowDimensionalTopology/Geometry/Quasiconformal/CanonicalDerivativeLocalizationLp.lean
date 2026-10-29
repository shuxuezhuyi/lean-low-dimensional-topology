module

public import LowDimensionalTopology.Geometry.Quasiconformal.CompactCanonicalDerivativeBounds

/-!
# Lp control of a localized derivative error

A genuine measurable derivative error bounded by twice a known Lp error and
a uniform scalar error has the corresponding exact finite-disc Lp bound.
The consumer is the actual canonical-map chain rule in the localization proof.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The actual finite-disc triangle bound for the derivative localization. -/
theorem canonical_derivative_error_lp_bound {p : ℝ} (hp : 2 < p)
    {u v : ℂ → ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : AEStronglyMeasurable u (volume.restrict (ball (0 : ℂ) 1)))
    (hv : MemLp v (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1)))
    (hbound : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), ‖u z‖ ≤ 2 * ‖v z‖ + δ) :
    MemLp u (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1)) ∧
      (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1))).toReal ≤
        2 * (eLpNorm v (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1))).toReal +
          δ * planarBallLpVolume p 1 := by
  let m : Measure ℂ := volume.restrict (ball (0 : ℂ) 1)
  let : IsFiniteMeasure m := ⟨by
    dsimp only [m]
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hq0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hc : MemLp (fun _ : ℂ => δ) (ENNReal.ofReal p) m := memLp_const _
  have hs : MemLp ((2 : ℝ) • fun z => ‖v z‖) (ENNReal.ofReal p) m :=
    hv.norm.const_smul _
  let w : ℂ → ℝ := (2 : ℝ) • (fun z => ‖v z‖) + fun _ => δ
  have hw : MemLp w (ENNReal.ofReal p) m := hs.add hc
  have hw0 : ∀ z, 0 ≤ w z := by
    intro z
    exact add_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) hδ
  have hle : ∀ᵐ z ∂m, ‖u z‖ ≤ ‖w z‖ := by
    filter_upwards [hbound] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 z)]
    simpa only [w, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hz
  have humem : MemLp u (ENNReal.ofReal p) m := hw.of_le hu hle
  refine ⟨humem, ?_⟩
  have hmono := ENNReal.toReal_mono hw.eLpNorm_ne_top (eLpNorm_mono_ae hu hle)
  have htri := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hs.eLpNorm_ne_top, hc.eLpNorm_ne_top⟩)
    (eLpNorm_add_le (f := (2 : ℝ) • fun z => ‖v z‖) (g := fun _ : ℂ => δ) (μ := m) hq1)
  rw [ENNReal.toReal_add hs.eLpNorm_ne_top hc.eLpNorm_ne_top] at htri
  have hsnorm : (eLpNorm ((2 : ℝ) • fun z => ‖v z‖) (ENNReal.ofReal p) m).toReal =
      2 * (eLpNorm v (ENNReal.ofReal p) m).toReal := by
    rw [eLpNorm_const_smul, eLpNorm_norm v hv.aestronglyMeasurable, ← ofReal_norm,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    norm_num [m]
  have hcnorm : (eLpNorm (fun _ : ℂ => δ) (ENNReal.ofReal p) m).toReal =
      δ * planarBallLpVolume p 1 := by
    rw [eLpNorm_const' _ hq0 ENNReal.ofReal_ne_top, ← ofReal_norm,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg hδ]
    simp only [m, Measure.restrict_apply_univ, one_div, planarBallLpVolume]
  exact hmono.trans (by simpa only [hsnorm, hcnorm] using htri)

end LowDimensionalTopology.Geometry.Quasiconformal
