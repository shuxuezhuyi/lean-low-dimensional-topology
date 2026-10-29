module

public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalLocalizedFactorDerivative
public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalDerivativeLocalizationLp
public import LowDimensionalTopology.Geometry.Quasiconformal.CompactCanonicalDerivativeStability

/-!
# Prescribed-exponent Lp continuity of the canonical Wirtinger derivative

The original coefficient is arbitrary in the genuine full-plane L-infinity
unit ball. A derived cutoff supplies its actual canonical inner map, while
its actual outer holomorphic factor has derivative uniformly tending to one.
The genuine classical chain rule combines these with the same-p compact-cutoff
estimate. No support, regularity, supplied factor or derivative assumption
is imposed on the original coefficient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

private theorem canonicalLocalizedFactor_dz_chain (μ : MeasurableBeltramiBall)
    (hH : DifferentiableOn ℂ (canonicalLocalizedFactor μ) (ball 0 2))
    (hmap : MapsTo (MeasurableBeltramiBall.normalizedSolution (canonicalBallFourCutoff μ))
      (ball 0 1) (closedBall 0 (3 / 2))) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)),
      dz (MeasurableBeltramiBall.normalizedSolution μ) z =
        deriv (canonicalLocalizedFactor μ)
          (MeasurableBeltramiBall.normalizedSolution (canonicalBallFourCutoff μ) z) *
            dz (MeasurableBeltramiBall.normalizedSolution (canonicalBallFourCutoff μ)) z := by
  let G := MeasurableBeltramiBall.normalizedSolution (canonicalBallFourCutoff μ)
  let H := canonicalLocalizedFactor μ
  have hfun : (MeasurableBeltramiBall.normalizedSolution μ : ℂ → ℂ) =
      (H : ℂ → ℂ) ∘ G := by
    funext z
    simp only [H, canonicalLocalizedFactor, G, Function.comp_apply,
      Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  have hdiff : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ G z := by
    simpa only [Measure.restrict_univ] using thm9_3_differentiable_ae
      (MeasurableBeltramiBall.normalizedSolution_spec (canonicalBallFourCutoff μ)).2.1
  filter_upwards [ae_restrict_of_ae hdiff, ae_restrict_mem measurableSet_ball] with z hz hzin
  have hGin : G z ∈ ball (0 : ℂ) 2 := by
    rw [mem_ball_zero_iff]
    have h := mem_closedBall_zero_iff.mp (hmap hzin)
    linarith
  have hcomplex : DifferentiableAt ℂ H (G z) :=
    (hH _ hGin).differentiableAt (isOpen_ball.mem_nhds hGin)
  rw [hfun, eq6_2_dz_comp hz (hcomplex.restrictScalars ℝ),
    dz_eq_deriv hcomplex, (cauchyRiemann_iff.mp hcomplex).2, zero_mul, add_zero]

/-- For every prescribed p > 2, the actual canonical derivative tends to one
in that same Lp on the unit disc as the arbitrary original coefficient tends
to zero in L-infinity. Compact support is only used for an internal cutoff. -/
theorem normalizedSolution_derivative_tendsto_one {ι : Type*} {l : Filter ι}
    {p : ℝ} (hp : 2 < p) (μ : ι → MeasurableBeltramiBall)
    (hμ : Tendsto (fun i => ‖(μ i).val‖) l (𝓝 0)) :
    (∀ᶠ i in l, MemLp
      (fun z => dz (MeasurableBeltramiBall.normalizedSolution (μ i)) z - 1)
      (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1))) ∧
      Tendsto (fun i => (eLpNorm
        (fun z => dz (MeasurableBeltramiBall.normalizedSolution (μ i)) z - 1)
        (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1))).toReal) l (𝓝 0) := by
  let ν := fun i => canonicalBallFourCutoff (μ i)
  have hν : Tendsto (fun i => ‖(ν i).val‖) l (𝓝 0) :=
    canonicalBallFourCutoff_norm_tendsto_zero μ hμ
  have hsupp : ∀ i, ∀ᵐ z ∂(volume : Measure ℂ), z ∉ ball 0 4 → (ν i).val z = 0 := by
    intro i
    filter_upwards [canonicalCoefficientCutoff_coe_ae (μ i) (ball 0 4) measurableSet_ball]
      with z hz
    intro hzin
    rw [hz, indicator_of_notMem hzin]
  obtain ⟨hGmem, hGlp⟩ := canonicalCompact_derivative_tendsto_one hp ν hsupp hν
  have hH := canonicalLocalizedFactor_eventually_differentiableOn_ball_two μ hμ
  have hmap := canonicalBallFourCutoff_eventually_maps_ball_one μ hμ
  have hder := canonicalLocalizedFactor_deriv_tendstoUniformlyOn μ hμ
  have hε : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l,
      MemLp (fun z => dz (MeasurableBeltramiBall.normalizedSolution (μ i)) z - 1)
          (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1)) ∧
        (eLpNorm (fun z => dz (MeasurableBeltramiBall.normalizedSolution (μ i)) z - 1)
          (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1))).toReal < ε := by
    intro ε hε
    let V := planarBallLpVolume p 1
    have hV : 0 ≤ V := planarBallLpVolume_nonneg _ _
    let δ := ε / (2 * (V + 1))
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hδV : δ * V < ε / 2 := by
      calc
        δ * V < δ * (V + 1) := mul_lt_mul_of_pos_left (lt_add_one V) hδ
        _ = ε / 2 := by
          dsimp only [δ]
          field_simp [ne_of_gt (by positivity : (0 : ℝ) < V + 1)]
    have houter := Metric.tendstoUniformlyOn_iff.mp hder (min 1 δ)
      (lt_min zero_lt_one hδ)
    have hinner := hGlp.eventually_lt_const (by linarith : (0 : ℝ) < ε / 4)
    filter_upwards [hH, hmap, hGmem, houter, hinner] with i hHi hmapi hGi hOi hIi
    have hchain := canonicalLocalizedFactor_dz_chain (μ i) hHi hmapi
    have hpoint : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)),
        ‖dz (MeasurableBeltramiBall.normalizedSolution (μ i)) z - 1‖ ≤
          2 * ‖dz (MeasurableBeltramiBall.normalizedSolution (ν i)) z - 1‖ + δ := by
      filter_upwards [hchain, ae_restrict_mem measurableSet_ball] with z hcz hz
      let a := deriv (canonicalLocalizedFactor (μ i))
        (MeasurableBeltramiBall.normalizedSolution (ν i) z)
      have ha : ‖a - 1‖ < min 1 δ := by
        simpa only [dist_eq_norm, norm_sub_rev] using hOi _ (hmapi hz)
      have haδ : ‖a - 1‖ ≤ δ := (ha.trans_le (min_le_right _ _)).le
      have haNorm : ‖a‖ ≤ 2 := by
        have ht := norm_add_le (a - 1) (1 : ℂ)
        rw [sub_add_cancel, norm_one] at ht
        linarith [ha.trans_le (min_le_left _ _)]
      rw [hcz]
      change ‖a * dz (MeasurableBeltramiBall.normalizedSolution (ν i)) z - 1‖ ≤
        2 * ‖dz (MeasurableBeltramiBall.normalizedSolution (ν i)) z - 1‖ + δ
      calc
        _ = ‖a * (dz (MeasurableBeltramiBall.normalizedSolution (ν i)) z - 1) +
            (a - 1)‖ := by congr 1; ring
        _ ≤ ‖a‖ * ‖dz (MeasurableBeltramiBall.normalizedSolution (ν i)) z - 1‖ + ‖a - 1‖ :=
          (norm_add_le _ _).trans_eq (by rw [norm_mul])
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_right haNorm (norm_nonneg _)) haδ
    have hmeas : AEStronglyMeasurable
        (fun z => dz (MeasurableBeltramiBall.normalizedSolution (μ i)) z - 1)
        (volume.restrict (ball (0 : ℂ) 1)) :=
      ((measurable_dz _).sub measurable_const).aestronglyMeasurable
    obtain ⟨hmem, hnorm⟩ := canonical_derivative_error_lp_bound hp hδ.le hmeas hGi hpoint
    refine ⟨hmem, hnorm.trans_lt ?_⟩
    change 2 * (eLpNorm (fun z => dz (MeasurableBeltramiBall.normalizedSolution (ν i)) z - 1)
      (ENNReal.ofReal p) (volume.restrict (ball (0 : ℂ) 1))).toReal + δ * V < ε
    linarith
  refine ⟨(hε 1 zero_lt_one).mono (fun _ hi => hi.1), Metric.tendsto_nhds.mpr ?_⟩
  intro ε hεpos
  filter_upwards [hε ε hεpos] with i hi
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] using hi.2

end LowDimensionalTopology.Geometry.Quasiconformal
