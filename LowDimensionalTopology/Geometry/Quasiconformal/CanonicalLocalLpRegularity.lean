module

public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalCoefficientLocalization
public import LowDimensionalTopology.Geometry.Quasiconformal.CompactCanonicalNormalRepresentation
public import LowDimensionalTopology.Geometry.Quasiconformal.QuasiconformalDistributional
public import LowDimensionalTopology.Geometry.Quasiconformal.PompeiuWeak
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Same-exponent local Lp data for every canonical normalized solution

The coefficient is arbitrary on the full plane. The only analytic smallness
is the original prescribed-p condition norm(mu) C_p < 1. An internal compact
cutoff and the actual holomorphic coordinate factor prove local membership
of both actual classical Wirtinger derivatives in that same Lp. Their genuine
weak identities are inherited from the actual quasiconformal map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- Every original full-plane canonical map has actual same-p local weak data;
compact support is imposed only on the internally constructed cutoff. -/
theorem normalizedSolution_sameExponent_localLp
    {p : ℝ} (hp : 2 < p) (μ : MeasurableBeltramiBall)
    (hsmall : ‖μ.val‖ * smoothHilbertNorm p < 1) :
    MemLp (dz (MeasurableBeltramiBall.normalizedSolution μ)) (ENNReal.ofReal p)
        (volume.restrict (closedBall (0 : ℂ) 3)) ∧
      MemLp (dzbar (MeasurableBeltramiBall.normalizedSolution μ)) (ENNReal.ofReal p)
        (volume.restrict (closedBall (0 : ℂ) 3)) ∧
      HasDistributionalWirtingerDerivatives (MeasurableBeltramiBall.normalizedSolution μ)
        (dz (MeasurableBeltramiBall.normalizedSolution μ))
        (dzbar (MeasurableBeltramiBall.normalizedSolution μ)) univ := by
  let ν := canonicalCoefficientCutoff μ (ball 0 4) measurableSet_ball
  let F := MeasurableBeltramiBall.normalizedSolution μ
  let G := MeasurableBeltramiBall.normalizedSolution ν
  let H := G.symm.trans F
  let m : Measure ℂ := volume.restrict (closedBall (0 : ℂ) 3)
  let : IsFiniteMeasure m := ⟨by
    dsimp only [m]
    rw [Measure.restrict_apply_univ]
    exact measure_closedBall_lt_top⟩
  have hp1 : 1 < p := lt_trans one_lt_two hp
  have hCp : 0 ≤ smoothHilbertNorm p := by
    rw [smoothHilbertNorm_eq_hilbertNorm hp1]
    exact hilbertNorm_nonneg p
  have hνsmall : ‖ν.val‖ * smoothHilbertNorm p < 1 :=
    (mul_le_mul_of_nonneg_right
      (canonicalCoefficientCutoff_norm_le μ _ measurableSet_ball) hCp).trans_lt hsmall
  have hsupp : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ ball 0 4 → ν.val z = 0 := by
    filter_upwards [canonicalCoefficientCutoff_coe_ae μ (ball 0 4) measurableSet_ball]
      with z hz
    intro hzin
    rw [hz, indicator_of_notMem hzin]
  obtain ⟨_, _, hrep⟩ := canonicalCompact_normalRepresentation hp
  obtain ⟨v, a, hv, _, _, _, _, hdzG⟩ := hrep ν hsupp hνsmall
  have hnum : MemLp (fun z : ℂ => 1 + hilbertH v z) (ENNReal.ofReal p) m :=
    (memLp_const (1 : ℂ)).add ((hilbertH_memLp hp1 hv).restrict _)
  have hquot : MemLp (fun z : ℂ => (1 + hilbertH v z) / a) (ENNReal.ofReal p) m := by
    simpa only [div_eq_mul_inv] using hnum.mul_const a⁻¹
  have hdzGr : (fun z => (1 + hilbertH v z) / a) =ᵐ[m] dz G := by
    filter_upwards [ae_restrict_of_ae hdzG] with z hz
    exact hz.symm
  have hGmem : MemLp (dz G) (ENNReal.ofReal p) m := MemLp.ae_eq hdzGr hquot
  have hH : DifferentiableOn ℂ H (G '' ball 0 4) :=
    (normalizedSolution_cutoff_conformal_factor μ (ball 0 4) isOpen_ball).1
  have hopen : IsOpen (G '' ball (0 : ℂ) 4) := G.isOpenMap _ isOpen_ball
  have hK : IsCompact (G '' closedBall (0 : ℂ) 3) :=
    (isCompact_closedBall _ _).image G.continuous
  have hsub : G '' closedBall (0 : ℂ) 3 ⊆ G '' ball 0 4 := by
    apply image_mono
    intro z hz
    rw [mem_ball_zero_iff]
    have hz' := mem_closedBall_zero_iff.mp hz
    linarith
  obtain ⟨M, _, hM⟩ :=
    (hK.image_of_continuousOn ((hH.deriv hopen).continuousOn.mono hsub)).isBounded.exists_pos_norm_le
  have hfun : (F : ℂ → ℂ) = (H : ℂ → ℂ) ∘ G := by
    funext z
    simp only [H, Function.comp_apply, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  have hdiffG : ∀ᵐ z ∂(volume : Measure ℂ), DifferentiableAt ℝ G z := by
    simpa only [Measure.restrict_univ] using thm9_3_differentiable_ae
      (MeasurableBeltramiBall.normalizedSolution_spec ν).2.1
  have hpoint : ∀ᵐ z ∂m, ‖dz F z‖ ≤ M * ‖dz G z‖ := by
    filter_upwards [ae_restrict_of_ae hdiffG, ae_restrict_mem measurableSet_closedBall] with z hz hzK
    have hGK : G z ∈ G '' closedBall (0 : ℂ) 3 := ⟨z, hzK, rfl⟩
    have hdH : DifferentiableAt ℂ H (G z) :=
      (hH _ (hsub hGK)).differentiableAt (hopen.mem_nhds (hsub hGK))
    have heq : dz F z = deriv H (G z) * dz G z := by
      rw [hfun, eq6_2_dz_comp hz (hdH.restrictScalars ℝ), dz_eq_deriv hdH,
        (cauchyRiemann_iff.mp hdH).2, zero_mul, add_zero]
    rw [heq, norm_mul]
    exact mul_le_mul_of_nonneg_right (hM _ ⟨G z, hGK, rfl⟩) (norm_nonneg _)
  have hFmem : MemLp (dz F) (ENNReal.ofReal p) m :=
    hGmem.of_le_mul (measurable_dz F).aestronglyMeasurable hpoint
  have hFqc := (MeasurableBeltramiBall.normalizedSolution_spec μ).2.1
  let K := (1 + ‖μ.val‖) / (1 - ‖μ.val‖)
  have hK0 : 0 ≤ K := le_trans zero_le_one hFqc.2.1
  have hineq : ∀ᵐ z ∂(volume : Measure ℂ),
      ‖dz F z‖ + ‖dzbar F z‖ ≤ K * (‖dz F z‖ - ‖dzbar F z‖) := by
    simpa only [Measure.restrict_univ] using geometric_quasiconformal_derivative_inequality hFqc
  have hbarle : ∀ᵐ z ∂m, ‖dzbar F z‖ ≤ K * ‖dz F z‖ := by
    filter_upwards [ae_restrict_of_ae hineq] with z hz
    nlinarith [norm_nonneg (dz F z), mul_nonneg hK0 (norm_nonneg (dzbar F z))]
  exact ⟨hFmem, hFmem.of_le_mul (measurable_dzbar F).aestronglyMeasurable hbarle,
    quasiconformal_distributional_wirtinger_derivatives hFqc⟩

/-- The first literal Cauchy area term and the actual boundary circle formula
hold for every original coefficient satisfying the prescribed-p condition.
This is the first ingredient of the two-area representation, not that whole
representation: no inverted-map integral is asserted here. -/
theorem normalizedSolution_pompeiu_sameExponent
    {p : ℝ} (hp : 2 < p) (μ : MeasurableBeltramiBall)
    (hsmall : ‖μ.val‖ * smoothHilbertNorm p < 1) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) :
    IntegrableOn (fun z => dzbar (MeasurableBeltramiBall.normalizedSolution μ) z / (z - ζ))
        (ball (0 : ℂ) 1) ∧
      MeasurableBeltramiBall.normalizedSolution μ ζ =
        (1 / (2 * Real.pi * I)) * (∮ z in C(0, 1),
          MeasurableBeltramiBall.normalizedSolution μ z / (z - ζ)) -
        (1 / Real.pi : ℂ) * ∫ z in ball (0 : ℂ) 1,
          dzbar (MeasurableBeltramiBall.normalizedSolution μ) z / (z - ζ) := by
  obtain ⟨hg, hh, _⟩ := normalizedSolution_sameExponent_localLp hp μ hsmall
  let F := MeasurableBeltramiBall.normalizedSolution μ
  have hloc : ∀ C ⊆ ball (0 : ℂ) 2, IsCompact C →
      MemLp (dz F) (ENNReal.ofReal p) (volume.restrict C) ∧
        MemLp (dzbar F) (ENNReal.ofReal p) (volume.restrict C) := by
    intro C hC _
    have hsub : C ⊆ closedBall (0 : ℂ) 3 := by
      intro z hz
      rw [mem_closedBall_zero_iff]
      have hz' := mem_ball_zero_iff.mp (hC hz)
      linarith
    exact ⟨hg.mono_measure (Measure.restrict_mono hsub le_rfl),
      hh.mono_measure (Measure.restrict_mono hsub le_rfl)⟩
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 2 := by
    intro z hz
    rw [mem_ball_zero_iff]
    have hz' := mem_closedBall_zero_iff.mp hz
    linarith
  have hw := quasiconformal_distributional_wirtinger_derivatives
    (nx_isKQC_restrict (MeasurableBeltramiBall.normalizedSolution_spec μ).2.1
      isOpen_ball (subset_univ (ball (0 : ℂ) 2)))
  exact ⟨pompeiu_area_integrable_of_local_memLp hp hsub
      (fun C hC hcompact => (hloc C hC hcompact).2),
    pompeiu_of_distributional_wirtinger isOpen_ball F.continuous.continuousOn hw hp hloc
      zero_lt_one hsub hζ⟩

end LowDimensionalTopology.Geometry.Quasiconformal
