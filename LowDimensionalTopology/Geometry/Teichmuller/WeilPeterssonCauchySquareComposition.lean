module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSourceKernels
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# The ordinary cross-half-plane Cauchy-square composition

This is the ordinary kernel integral used by the WP second-variation proof.
The already proved Cayley change of variables and circle mean-value formula
evaluate the same absolutely convergent integral. No PV, WP-variation formula,
fundamental-domain interchange or diagonal-trace premise is supplied.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology Metric
open scoped ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open LiZhongQC

private theorem unitDisk_integral_of_holomorphic {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (ball 0 1))
    (hc : ContinuousOn h (closedBall 0 1)) :
    ∫ q in ball (0 : ℂ) 1, h q = (Real.pi : ℂ) * h 0 := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hc
  have hpolar : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    have he : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
        fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I) := by
      funext p
      exact Complex.polarCoord_symm_apply p
    rw [he]
    fun_prop
  have hmaps (p : ℝ × ℝ) (hp : p ∈ Ioo 0 1 ×ˢ Ioo (-Real.pi) Real.pi) :
      Complex.polarCoord.symm p + 0 ∈ closedBall (0 : ℂ) 1 := by
    rw [add_zero, mem_closedBall, dist_zero_right,
      Complex.norm_polarCoord_symm, abs_of_pos hp.1.1]
    exact hp.1.2.le
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => (p.1 : ℂ) * h (Complex.polarCoord.symm p + 0))
      (Ioo 0 1 ×ˢ Ioo (-Real.pi) Real.pi) :=
    (Complex.continuous_ofReal.comp continuous_fst).continuousOn.mul
      (hc.comp (hpolar.add continuous_const).continuousOn hmaps)
  have hfin : volume (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) < ⊤ :=
    ((Metric.isBounded_Ioo 0 1).prod (Metric.isBounded_Ioo _ _)).measure_lt_top
  have hint : IntegrableOn
      (fun p : ℝ × ℝ => (p.1 : ℂ) * h (Complex.polarCoord.symm p + 0))
      (Ioo 0 1 ×ˢ Ioo (-Real.pi) Real.pi) := by
    refine Integrable.mono' (g := fun _ => M) (integrableOn_const hfin.ne)
      (hcont.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioo)) ?_
    refine ae_restrict_of_forall_mem (measurableSet_Ioo.prod measurableSet_Ioo) fun p hp => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp.1.1]
    simpa only [one_mul] using mul_le_mul hp.1.2.le
      (hM _ (hmaps p hp)) (norm_nonneg _) zero_le_one
  have hcircle (r : ℝ) (hr : r ∈ uIcc (0 : ℝ) 1) :
      ∫ θ in (0 : ℝ)..2 * Real.pi, h (circleMap 0 r θ) =
        (2 * Real.pi : ℂ) * h 0 := by
    rw [uIcc_of_le zero_le_one] at hr
    have hR : |r| ≤ 1 := by
      rw [abs_of_nonneg hr.1]
      exact hr.2
    have hm : Real.circleAverage h 0 r = h 0 :=
      (show DiffContOnCl ℂ h (ball 0 |r|) from
      ⟨hd.mono (ball_subset_ball hR),
        hc.mono (closure_ball_subset_closedBall.trans (closedBall_subset_closedBall hR))⟩).circleAverage
    rw [Real.circleAverage_def] at hm
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    calc
      _ = (2 * Real.pi : ℝ) • ((2 * Real.pi : ℝ)⁻¹ •
          ∫ θ in (0 : ℝ)..2 * Real.pi, h (circleMap 0 r θ)) :=
        (smul_inv_smul₀ hpi _).symm
      _ = (2 * Real.pi : ℝ) • h 0 := by rw [hm]
      _ = _ := by rw [Complex.real_smul]; push_cast; ring
  rw [setIntegral_ball_eq_polar' 0 zero_le_one hint]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_congr (fun r hr => by rw [hcircle r hr])]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    integral_id]
  norm_num
  ring

private def compositionDiskDenominator (u v q : ℂ) : ℂ :=
  u - conj v - (conj u - conj v) * q

private theorem compositionDiskDenominator_ne_zero (u v : ℍ) {q : ℂ}
    (hq : q ∈ closedBall (0 : ℂ) 1) :
    compositionDiskDenominator u v q ≠ 0 := by
  have hs : ‖conj (u : ℂ) - conj (v : ℂ)‖ ^ 2 < ‖(u : ℂ) - conj (v : ℂ)‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, conj_re, conj_im]
    have huv : 0 < (u : ℂ).im * (v : ℂ).im := by
      simpa only [UpperHalfPlane.coe_im] using mul_pos u.im_pos v.im_pos
    nlinarith [huv]
  have hn : ‖conj (u : ℂ) - conj (v : ℂ)‖ < ‖(u : ℂ) - conj (v : ℂ)‖ := by
    nlinarith [norm_nonneg (conj (u : ℂ) - conj (v : ℂ)),
      norm_nonneg ((u : ℂ) - conj (v : ℂ))]
  intro he
  have he' : (u : ℂ) - conj (v : ℂ) =
      (conj (u : ℂ) - conj (v : ℂ)) * q := sub_eq_zero.mp he
  have hq' : ‖q‖ ≤ 1 := mem_closedBall_zero_iff.mp hq
  have hle : ‖(u : ℂ) - conj (v : ℂ)‖ ≤ ‖conj (u : ℂ) - conj (v : ℂ)‖ := by
    rw [he', norm_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hq' (norm_nonneg (conj (u : ℂ) - conj (v : ℂ)))
  exact (not_le_of_gt hn) hle

private theorem cayley_composition_integrand (u v : ℍ) {q : ℂ}
    (hq : q ∈ ball (0 : ℂ) 1) :
    ‖deriv (b36_r_cay (conj (u : ℂ))) q‖ ^ 2 •
      (cauchySquare (conj (b36_r_cay (conj (u : ℂ)) q)) u *
        cauchySquare (b36_r_cay (conj (u : ℂ)) q) (conj (v : ℂ))) =
      -(1 / compositionDiskDenominator u v q ^ 2) := by
  have hq0 := b36_r_one_sub_ne hq
  have hq1 := b36_r_one_sub_conj_ne hq
  have hD := compositionDiskDenominator_ne_zero u v (ball_subset_closedBall hq)
  have hu : (u : ℂ) - conj (u : ℂ) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [sub_im, conj_im, zero_im] at hi
    have hpos : 0 < (u : ℂ).im := by
      simpa only [UpperHalfPlane.coe_im] using u.im_pos
    linarith
  have huneg : -(u : ℂ) + conj (u : ℂ) ≠ 0 := by
    rw [show -(u : ℂ) + conj (u : ℂ) = -((u : ℂ) - conj (u : ℂ)) by ring]
    exact neg_ne_zero.mpr hu
  have hleft : conj (b36_r_cay (conj (u : ℂ)) q) - u =
      (conj (u : ℂ) - u) / (1 - conj q) := by
    simp only [b36_r_cay, map_add, map_div₀, map_sub, map_one, Complex.conj_conj]
    field_simp [hq1]
    ring
  have hright : b36_r_cay (conj (u : ℂ)) q - conj (v : ℂ) =
      compositionDiskDenominator u v q / (1 - q) := by
    unfold b36_r_cay compositionDiskDenominator
    simp only [Complex.conj_conj]
    field_simp [hq0]
    ring
  rw [(b36_r_hasDerivAt _ hq0).deriv, Complex.conj_conj,
    Complex.real_smul]
  unfold cauchySquare
  rw [hleft, hright]
  push_cast
  rw [← Complex.mul_conj' (((u : ℂ) - conj (u : ℂ)) / (1 - q) ^ 2)]
  simp only [map_div₀, map_sub, map_pow, map_one, Complex.conj_conj]
  field_simp [hq0, hq1, hu, huneg, hD]
  ring_nf
  field_simp [huneg]; ring

/-- The actual ordinary cross-half-plane kernel composition, with absolute convergence
and the source's minus-pi normalization. Both poles stay in the opposite half-plane. -/
theorem cauchySquare_composition (u v : ℍ) :
    IntegrableOn (fun ζ : ℂ => cauchySquare (conj ζ) u *
      cauchySquare ζ (conj (v : ℂ))) upperHalf ∧
    (∫ ζ : ℂ in upperHalf, cauchySquare (conj ζ) u *
      cauchySquare ζ (conj (v : ℂ))) =
        -(Real.pi : ℂ) * cauchySquare u (conj (v : ℂ)) := by
  let h : ℂ → ℂ := fun q => 1 / compositionDiskDenominator u v q ^ 2
  have hd : DifferentiableOn ℂ h (ball 0 1) :=
    (differentiableOn_const _).div (by unfold compositionDiskDenominator; fun_prop)
      (fun q hq => pow_ne_zero 2
        (compositionDiskDenominator_ne_zero u v (ball_subset_closedBall hq)))
  have hc : ContinuousOn h (closedBall 0 1) :=
    continuousOn_const.div (by unfold compositionDiskDenominator; fun_prop)
      (fun q hq => pow_ne_zero 2 (compositionDiskDenominator_ne_zero u v hq))
  have hi : IntegrableOn h (ball (0 : ℂ) 1) :=
    (hc.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set ball_subset_closedBall
  have hu : conj (u : ℂ) ∈ lowerHalf := by
    change (conj (u : ℂ)).im < 0
    simpa only [conj_im, neg_lt_zero, UpperHalfPlane.coe_im] using u.im_pos
  have hchange := ahP_integral_image isOpen_ball (b36_r_differentiableOn (conj (u : ℂ)))
    (b36_r_injOn hu) (fun ζ : ℂ => cauchySquare (conj ζ) u *
      cauchySquare ζ (conj (v : ℂ)))
  have heq (q : ℂ) (hq : q ∈ ball (0 : ℂ) 1) := cayley_composition_integrand u v hq
  refine ⟨?_, ?_⟩
  · rw [← b36_r_image hu, ahP_integrableOn_image isOpen_ball
      (b36_r_differentiableOn (conj (u : ℂ))) (b36_r_injOn hu)]
    exact hi.neg.congr_fun (fun q hq => (heq q hq).symm) measurableSet_ball
  · rw [b36_r_image hu] at hchange
    rw [hchange, setIntegral_congr_fun measurableSet_ball heq, integral_neg,
      unitDisk_integral_of_holomorphic hd hc]
    simp only [h, compositionDiskDenominator, mul_zero, sub_zero, cauchySquare]
    ring

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
