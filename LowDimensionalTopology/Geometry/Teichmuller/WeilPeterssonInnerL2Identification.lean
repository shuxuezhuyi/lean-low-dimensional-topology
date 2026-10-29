module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonKernelL2Input
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# Identification of the actual inner principal value in L²

A compact smooth cutoff separates the local singularity from an L² remainder
that vanishes on a ball. The existing canonical Hilbert approximants identify
the remainder with its ordinary kernel integral there, using the L² norm of
the truncated inverse-square kernel. A countable cover joins these local
identities for the original harmonic input and its chosen representative.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology Metric
open scoped ComplexConjugate UpperHalfPlane Manifold ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open LiZhongQC GammaMeasurableBeltrami

private def truncatedHilbertKernel (ξ : ℂ) (δ : ℝ) (η : ℂ) : ℂ :=
  -(1 / (Real.pi : ℂ)) *
    {w : ℂ | δ < ‖w - ξ‖}.indicator (fun w => 1 / (w - ξ) ^ 2) η

private theorem truncatedHilbertKernel_memLp_two (ξ : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    MemLp (truncatedHilbertKernel ξ δ) 2 (volume : Measure ℂ) := by
  let S : Set ℂ := {η | δ < ‖η - ξ‖}
  have hS : MeasurableSet S :=
    measurableSet_lt measurable_const (measurable_id.sub_const ξ).norm
  have hm : Measurable (fun η : ℂ => (1 : ℂ) / (η - ξ) ^ 2) := by fun_prop
  have hraw : MemLp (fun η : ℂ => (1 : ℂ) / (η - ξ) ^ 2) 2 (volume.restrict S) := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable.restrict).2
    refine ⟨(hm.aemeasurable.restrict.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)]
    have he : (∫⁻ η in S, ENNReal.ofReal (‖(1 : ℂ) / (η - ξ) ^ 2‖ ^ 2)) =
        ∫⁻ η in S, ‖η - ξ‖ₑ ^ (-4 : ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict hS] with η hη
      have hn : 0 < ‖η - ξ‖ := hδ.trans hη
      change ENNReal.ofReal (‖(1 : ℂ) / (η - ξ) ^ 2‖ ^ 2) = ‖η - ξ‖ₑ ^ (-4 : ℝ)
      rw [norm_div, norm_one, norm_pow, ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      norm_num only [one_div, ENNReal.rpow_neg, ENNReal.rpow_ofNat]
      have hp : (‖η - ξ‖ₑ ^ 2) ^ 2 = ‖η - ξ‖ₑ ^ 4 :=
        (pow_mul ‖η - ξ‖ₑ 2 2).symm
      calc
        (‖η - ξ‖ₑ ^ 2)⁻¹ ^ 2 = ((‖η - ξ‖ₑ ^ 2) ^ 2)⁻¹ := by
          simpa only [ENNReal.rpow_ofNat] using
            ENNReal.inv_rpow (‖η - ξ‖ₑ ^ 2) (2 : ℝ)
        _ = (‖η - ξ‖ₑ ^ 4)⁻¹ := congrArg (fun v : ℝ≥0∞ => v⁻¹) hp
    rw [he, lintegral_compl_ball_sub_enorm_rpow_neg (by norm_num : (2 : ℝ) < 4) hδ ξ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hi := (memLp_indicator_iff_restrict hS.nullMeasurableSet).2 hraw
  exact hi.const_mul (-(1 / (Real.pi : ℂ)))

private theorem kernel_eq_truncated_of_gap {f : ℂ → ℂ} {ξ : ℂ} {δ : ℝ}
    (hzero : ∀ η, ‖η - ξ‖ ≤ δ → f η = 0) :
    (fun η => -(1 / (Real.pi : ℂ)) * f η / (η - ξ) ^ 2) =
      fun η => f η * truncatedHilbertKernel ξ δ η := by
  classical
  funext η
  unfold truncatedHilbertKernel
  by_cases hη : δ < ‖η - ξ‖
  · rw [indicator_of_mem (show η ∈ {w : ℂ | δ < ‖w - ξ‖} from hη)]
    ring
  · rw [indicator_of_notMem (show η ∉ {w : ℂ | δ < ‖w - ξ‖} from hη),
      hzero η (not_lt.mp hη)]
    simp

private theorem support_gap_of_zero_on_ball {f : ℂ → ℂ} {a ξ : ℂ} {r : ℝ}
    (hzero : ∀ w ∈ ball a (2 * r), f w = 0) (hξ : ξ ∈ ball a r) :
    ∀ η ∈ tsupport f, r ≤ ‖ξ - η‖ := by
  have hs : tsupport f ⊆ (ball a (2 * r))ᶜ :=
    closure_minimal (fun η hη hηball => hη (hzero η hηball)) isOpen_ball.isClosed_compl
  intro η hη
  have ha : 2 * r ≤ ‖η - a‖ := by
    simpa only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] using hs hη
  have hx : ‖ξ - a‖ < r := by simpa only [mem_ball, dist_eq_norm] using hξ
  have ht : ‖η - a‖ ≤ ‖η - ξ‖ + ‖ξ - a‖ := by
    simpa only [dist_eq_norm] using dist_triangle η ξ a
  rw [norm_sub_rev η ξ] at ht
  linarith

private theorem hilbertH_eq_integral_ae_on_ball_of_zero
    {f : ℂ → ℂ} (hf : MemLp f 2 (volume : Measure ℂ))
    (a : ℂ) {r : ℝ} (hr : 0 < r)
    (hzero : ∀ w ∈ ball a (2 * r), f w = 0) :
    ∀ᵐ ξ ∂(volume : Measure ℂ).restrict (ball a r),
      hilbertH f ξ = ∫ η : ℂ, -(1 / (Real.pi : ℂ)) * f η / (η - ξ) ^ 2 := by
  classical
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) := ofReal_two_eq ▸ hf
  have hbound : ∀ ψ : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
      HasCompactSupport ψ → eLpNorm (hilbertHSmooth ψ) (ENNReal.ofReal (2 : ℝ)) volume ≤
        ENNReal.ofReal (1 : ℝ) * eLpNorm ψ (ENNReal.ofReal (2 : ℝ)) volume := by
    intro ψ hψ hc
    rw [ofReal_two_eq, ENNReal.ofReal_one, one_mul]
    exact (i4_eLpNorm_eq hψ hc).le
  obtain ⟨_, _, himages⟩ := hilbertH_tendsto_of_smooth_bound one_lt_two hbound f hf'
  rw [ofReal_two_eq] at himages
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) himages).exists_seq_tendsto_ae
  have hfn (n : ℕ) : MemLp (hilbertHApprox f n) 2 (volume : Measure ℂ) :=
    (hilbertHApprox_contDiff (by norm_num : (1 : ℝ) ≤ 2) hf' n).continuous.memLp_of_hasCompactSupport
      (hilbertHApprox_hasCompactSupport f n)
  have hconv : Tendsto (fun n => eLpNorm (hilbertHApprox f n - f) 2 volume) atTop (𝓝 0) := by
    change Tendsto (fun n => eLpNorm (fun η => hilbertHApprox f n η - f η) 2 volume)
      atTop (𝓝 0)
    simpa only [ofReal_two_eq] using hilbertHApprox_tendsto (by norm_num : (1 : ℝ) ≤ 2) hf'
  have hreal : Tendsto (fun n => (eLpNorm (hilbertHApprox f n - f) 2 volume).toReal)
      atTop (𝓝 0) := (ENNReal.tendsto_toReal (by norm_num)).comp hconv
  have hsub (n : ℕ) : tsupport (hilbertHTrunc f n) ⊆ tsupport f := by
    apply closure_mono
    intro η hη
    simp only [Function.mem_support, hilbertHTrunc, indicator_apply] at hη ⊢
    split_ifs at hη with hmem
    · exact hη
    · exact (hη rfl).elim
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hae] with ξ hξlimit hξ
  have hgap := support_gap_of_zero_on_ball hzero hξ
  let δ : ℝ := r / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hk := truncatedHilbertKernel_memLp_two ξ hδ
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < r / 2 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds (by positivity))
  have hgapApprox : ∀ᶠ n : ℕ in atTop,
      ∀ η ∈ tsupport (hilbertHApprox f n), r / 2 ≤ ‖η - ξ‖ := by
    filter_upwards [hsmall] with n hn
    change closure (Function.support (hilbertHApprox f n)) ⊆
      {η : ℂ | r / 2 ≤ ‖η - ξ‖}
    apply closure_minimal ?_ (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
    intro η hη
    change r / 2 ≤ ‖η - ξ‖
    have hd := offsupp_dist_ge (fun w hw => hgap w (hsub n hw)) n η hη
    rw [norm_sub_rev ξ η] at hd
    exact le_of_lt ((show r / 2 < r - 1 / ((n : ℝ) + 1) by linarith).trans hd)
  have hz : ∀ η, ‖η - ξ‖ ≤ δ → f η = 0 := by
    intro η hη
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have h := hgap η hs
    rw [norm_sub_rev ξ η] at h
    dsimp [δ] at hη
    linarith
  have hform : ∀ᶠ n : ℕ in atTop,
      hilbertHSmooth (hilbertHApprox f n) ξ =
        ∫ η : ℂ, hilbertHApprox f n η * truncatedHilbertKernel ξ δ η := by
    filter_upwards [hgapApprox] with n hn
    rw [offsupp_hilbertHSmooth_eq_integral hn (by positivity : 0 < r / 2)]
    apply congrArg (fun g : ℂ → ℂ => ∫ η, g η)
    apply kernel_eq_truncated_of_gap
    intro η hη
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have h := hn η hs
    dsimp [δ] at hη
    linarith
  have hIntConv : Tendsto (fun n => ∫ η : ℂ,
      hilbertHApprox f n η * truncatedHilbertKernel ξ δ η) atTop
      (𝓝 (∫ η : ℂ, f η * truncatedHilbertKernel ξ δ η)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have hupper : Tendsto (fun n => (eLpNorm (hilbertHApprox f n - f) 2 volume).toReal *
        (eLpNorm (truncatedHilbertKernel ξ δ) 2 volume).toReal) atTop (𝓝 0) := by
      simpa only [zero_mul] using hreal.mul_const (eLpNorm (truncatedHilbertKernel ξ δ) 2 volume).toReal
    apply squeeze_zero (fun _ => norm_nonneg _) ?_ hupper
    intro n
    rw [← integral_sub
      (f := fun η : ℂ => hilbertHApprox f n η * truncatedHilbertKernel ξ δ η)
      (g := fun η : ℂ => f η * truncatedHilbertKernel ξ δ η)
      ((hfn n).integrable_mul hk) (hf.integrable_mul hk)]
    have he : (fun η => hilbertHApprox f n η * truncatedHilbertKernel ξ δ η -
        f η * truncatedHilbertKernel ξ δ η) =
        fun η => (hilbertHApprox f n - f) η * truncatedHilbertKernel ξ δ η := by
      funext η
      simp only [Pi.sub_apply, sub_mul]
    rw [he]
    exact cauchy_schwarz_L2 ((hfn n).sub hf) hk
  have hlimit := (hIntConv.congr' (Filter.EventuallyEq.symm hform)).comp hns.tendsto_atTop
  rw [kernel_eq_truncated_of_gap hz]
  exact tendsto_nhds_unique hξlimit hlimit

private theorem constant_truncation_of_zero_on_ball (f : ℂ → ℂ) (ξ : ℂ)
    {s : ℝ} (hs : 0 < s) (hf : ∀ η ∈ ball ξ s, f η = 0) :
    Tendsto (fun t : ℝ => -(1 / (Real.pi : ℂ)) *
      ∫ η in {η : ℂ | t < ‖η - ξ‖}, f η / (η - ξ) ^ 2)
      (𝓝[>] 0) (𝓝 (-(1 / (Real.pi : ℂ)) * ∫ η, f η / (η - ξ) ^ 2)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hs] with t ht
  congr 1
  have he := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (f := fun η => f η / (η - ξ) ^ 2) (μ := (volume : Measure ℂ))
    MeasurableSet.univ (subset_univ {η : ℂ | t < ‖η - ξ‖}) (fun η hη => by
      have hn : ‖η - ξ‖ ≤ t := not_lt.mp hη.2
      rw [hf η (by rw [mem_ball, dist_eq_norm]; exact hn.trans_lt ht.2), zero_div])
  simpa only [setIntegral_univ] using he

theorem hilbertHSmooth_eq_hilbertH_ae_upper (f : ℂ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℂ))
    (hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f upperHalf) :
    hilbertHSmooth f =ᵐ[(volume : Measure ℂ).restrict upperHalf] hilbertH f := by
  have hlocal (a : ℍ) : hilbertHSmooth f =ᵐ[volume.restrict (ball (a : ℂ) (a.im / 8))]
      hilbertH f := by
    let b : ContDiffBump (a : ℂ) := ⟨a.im / 4, a.im / 2, by positivity, by linarith [a.im_pos]⟩
    let ψ : ℂ → ℂ := fun η => (b η : ℂ) * f η
    have hupper : closedBall (a : ℂ) (a.im / 2) ⊆ upperHalf := by
      intro η hη
      have hn : ‖η - a‖ ≤ a.im / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hη
      have hi : a.im - η.im ≤ ‖η - a‖ := by
        calc
          a.im - η.im = -(η - a).im := by simp only [sub_im, UpperHalfPlane.coe_im]; ring
          _ ≤ |(η - a).im| := neg_le_abs _
          _ ≤ ‖η - a‖ := Complex.abs_im_le_norm _
      change 0 < η.im
      linarith [a.im_pos]
    have hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun η : ℂ => (b η : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp b.contDiff
    have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
      rw [contDiff_iff_contDiffAt]
      intro η
      by_cases hη : η ∈ tsupport b
      · exact hb.contDiffAt.mul (hd.contDiffAt (isOpen_upperHalf.mem_nhds
          (hupper (by simpa only [b.tsupport_eq] using hη))))
      · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport (b : ℂ → ℝ)).isOpen_compl.mem_nhds hη] with w hw
        change (b w : ℂ) * f w = 0
        rw [image_eq_zero_of_notMem_tsupport hw, Complex.ofReal_zero, zero_mul]
    have hψc : HasCompactSupport ψ :=
      (b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) rfl).mul_right
    have hψ2 : MemLp ψ 2 (volume : Measure ℂ) := hψ.continuous.memLp_of_hasCompactSupport hψc
    let d : ℂ → ℂ := f - ψ
    have hd2 : MemLp d 2 (volume : Measure ℂ) := hf.sub hψ2
    have hzero : ∀ η ∈ ball (a : ℂ) (2 * (a.im / 8)), d η = 0 := by
      intro η hη
      have he : 2 * (a.im / 8) = a.im / 4 := by ring
      rw [he] at hη
      have hone := b.one_of_mem_closedBall (ball_subset_closedBall hη)
      simp only [d, Pi.sub_apply, ψ, hone, Complex.ofReal_one, one_mul, sub_self]
    have hdEq := hilbertH_eq_integral_ae_on_ball_of_zero hd2 (a : ℂ) (by positivity) hzero
    filter_upwards [hdEq, ae_restrict_of_ae (hilbertH_sub_ae hf hψ2),
      ae_restrict_of_ae (hilbertH_eq_ae_smooth hψ hψc),
      self_mem_ae_restrict (measurableSet_ball : MeasurableSet (ball (a : ℂ) (a.im / 8)))]
      with ξ hdξ hsubξ hψξ hξ
    have hgap := support_gap_of_zero_on_ball hzero hξ
    have hdlim := constant_truncation_of_zero_on_ball d ξ (by positivity : 0 < a.im / 8)
      (fun η hη => by
        apply image_eq_zero_of_notMem_tsupport
        intro hs
        have h := hgap η hs
        rw [norm_sub_rev ξ η] at h
        exact (not_lt.mpr h) (by simpa only [mem_ball, dist_eq_norm] using hη))
    have hψlim := tendsto_truncated_cauchyT_dz (hψ.of_le (by simp)) hψc ξ
    rw [← (i1_hilbertH_eq_cauchyT_dz hψ hψc).1] at hψlim
    have hInt (u : ℂ → ℂ) (hu : MemLp u 2 (volume : Measure ℂ)) (t : ℝ) (ht : 0 < t) :=
      integrableOn_truncated_kernel (p := 2) (by norm_num)
        (by simpa only [ofReal_two_eq] using hu) ξ ht
    have hlim : Tendsto (fun t : ℝ => -(1 / (Real.pi : ℂ)) *
        ∫ η in {η : ℂ | t < ‖η - ξ‖}, f η / (η - ξ) ^ 2)
        (𝓝[>] 0) (𝓝 (hilbertHSmooth ψ ξ +
          -(1 / (Real.pi : ℂ)) * ∫ η, d η / (η - ξ) ^ 2)) := by
      refine (hψlim.add hdlim).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      change -(1 / (Real.pi : ℂ)) * (∫ η in {η : ℂ | t < ‖η - ξ‖}, ψ η / (η - ξ) ^ 2) +
        -(1 / (Real.pi : ℂ)) * (∫ η in {η : ℂ | t < ‖η - ξ‖}, d η / (η - ξ) ^ 2) =
        -(1 / (Real.pi : ℂ)) *
        (∫ η in {η : ℂ | t < ‖η - ξ‖}, f η / (η - ξ) ^ 2)
      rw [← mul_add, ← integral_add (hInt ψ hψ2 t ht) (hInt d hd2 t ht)]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun η => by dsimp only [d, Pi.sub_apply]; ring
    have hi : (∫ η : ℂ, -(1 / (Real.pi : ℂ)) * d η / (η - ξ) ^ 2) =
        -(1 / (Real.pi : ℂ)) * ∫ η : ℂ, d η / (η - ξ) ^ 2 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun η => by ring
    rw [hi] at hdξ
    have hv : hilbertHSmooth f ξ = hilbertHSmooth ψ ξ +
        -(1 / (Real.pi : ℂ)) * ∫ η, d η / (η - ξ) ^ 2 := hlim.limUnder_eq
    rw [hv, ← hψξ, ← hdξ]
    change hilbertH f ξ - hilbertH ψ ξ = hilbertH d ξ at hsubξ
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hsubξ).symm
  obtain ⟨c, hc⟩ := (HereditarilyLindelofSpace.isLindelof upperHalf).indexed_countable_subcover
    (fun a : ℍ => ball (a : ℂ) (a.im / 8)) (fun _ => isOpen_ball) (by
      intro ξ hξ
      exact mem_iUnion.2 ⟨⟨ξ, hξ⟩, mem_ball_self (by positivity)⟩)
  apply ae_restrict_of_ae_restrict_of_subset hc
  exact (ae_restrict_iUnion_iff (fun n => ball (c n : ℂ) ((c n).im / 8))
    (fun ξ => hilbertHSmooth f ξ = hilbertH f ξ)).2 (fun n => hlocal (c n))

private theorem innerInput_congr_ae {μ ν : ℍ → ℂ}
    (h : μ =ᵐ[flatArea] ν) (z : ℍ) :
    innerInput μ z =ᵐ[volume] innerInput ν z := by
  apply ae_of_ae_restrict_of_ae_restrict_compl upperHalf
  · rw [← map_flat_coe, UpperHalfPlane.measurableEmbedding_coe.ae_map_iff]
    filter_upwards [h] with η hη
    simp only [innerInput, upperExtension, hη]
  · apply ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet.compl
    intro η hη
    simp only [innerInput, upperExtension, show ¬0 < η.im from hη, dite_false]

open Surfaces QuadraticBergman

/-- The actual chosen harmonic inner input has its literal principal value
equal to the existing L² Hilbert representative almost everywhere on H. -/
theorem innerInput_ofQuadratic_hilbertHSmooth_eq_hilbertH_ae
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    hilbertHSmooth
      (innerInput (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z)
      =ᵐ[(volume : Measure ℂ).restrict upperHalf]
    hilbertH
      (innerInput (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let a : Ambient := (NativeHarmonicBeltrami.ofQuadratic R p hp q).val
  let f : ℂ → ℂ := innerInput (NativeHarmonicBeltrami.coefficient R p q) z
  have hae : innerInput (fun η => a η) z =ᵐ[volume] f :=
    innerInput_congr_ae (ae_hyperbolic_iff.mp
      (NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp q)) z
  have hf : MemLp f 2 (volume : Measure ℂ) :=
    (memLp_congr_ae hae).mp (innerInput_memLp_two a z)
  have hQ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uniformizedQuadratic R p q) upperHalf :=
    ((utm_liftQD_differentiableOn q.property hp).contDiffOn isOpen_upperHalf).restrict_scalars ℝ
  have him : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun η : ℂ => (η.im : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff
  have hk : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun η : ℂ => cauchySquare η (conj (z : ℂ))) upperHalf := by
    have hden : DifferentiableOn ℂ
        (fun η : ℂ => (η - conj (z : ℂ)) ^ 2) upperHalf :=
      (differentiableOn_id.sub (differentiableOn_const (conj (z : ℂ)))).pow 2
    have hne : ∀ η ∈ upperHalf, (η - conj (z : ℂ)) ^ 2 ≠ 0 := by
      intro η hη
      apply pow_ne_zero 2
      intro he
      have hi := congrArg Complex.im he
      simp only [sub_im, conj_im, zero_im] at hi
      have hz : 0 < (z : ℂ).im := by simpa only [UpperHalfPlane.coe_im] using z.im_pos
      linarith [hz, show 0 < η.im from hη]
    have hhol : DifferentiableOn ℂ
        (fun η : ℂ => cauchySquare η (conj (z : ℂ))) upperHalf := by
      change DifferentiableOn ℂ (fun η : ℂ => (1 : ℂ) / (η - conj (z : ℂ)) ^ 2) upperHalf
      exact (differentiableOn_const (1 : ℂ)).div hden hne
    exact (hhol.contDiffOn isOpen_upperHalf).restrict_scalars ℝ
  have hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f upperHalf := by
    apply (((him.pow 2).contDiffOn.mul
      (Complex.conjCLE.contDiff.comp_contDiffOn hQ)).mul hk).congr
    intro η hη
    change innerInput (NativeHarmonicBeltrami.coefficient R p q) z η = _
    dsimp only [innerInput, upperExtension]
    rw [dite_eq_left (show 0 < η.im from hη), NativeHarmonicBeltrami.coefficient_eq_uniformized]
    rfl
  rw [hilbertHSmooth_congr_ae hae, hilbertH_congr_ae hae]
  exact hilbertHSmooth_eq_hilbertH_ae_upper f hf hd

/-- Multiplying the original harmonic inner principal value by an actual
L-infinity class and extending by zero gives the same outer input in L². -/
theorem outerInput_ofQuadratic_memLp_two
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (b : GammaMeasurableBeltrami.Ambient)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    MemLp
      (outerInput (fun ξ => b ξ)
        (fun η => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z)
      2 (volume : Measure ℂ) := by
  let a : Ambient := (NativeHarmonicBeltrami.ofQuadratic R p hp q).val
  let H : ℂ → ℂ := hilbertH (innerInput (fun η => a η) z)
  have hH : MemLp H 2 (volume : Measure ℂ) := (hilbertH_memLp_two (innerInput_memLp_two a z)).1
  have hb := planeRepresentative_isBeltramiCoeff b
  have hm : AEStronglyMeasurable (fun ξ => planeRepresentative b ξ * H ξ)
      (volume.restrict upperHalf) := hb.1.mul hH.aestronglyMeasurable.restrict
  have hbound : MemLp (fun ξ => planeRepresentative b ξ * H ξ) 2
      (volume.restrict upperHalf) := by
    refine ((hH.restrict upperHalf).norm.const_mul ‖b‖).mono' hm ?_
    filter_upwards [hb.2] with ξ hξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
  have hi := (memLp_indicator_iff_restrict isOpen_upperHalf.measurableSet.nullMeasurableSet).2 hbound
  refine (memLp_congr_ae ?_).mp hi
  have he := innerInput_ofQuadratic_hilbertHSmooth_eq_hilbertH_ae R hp q z
  change hilbertHSmooth (innerInput (fun η => a η) z)
    =ᵐ[(volume : Measure ℂ).restrict upperHalf] H at he
  apply ae_of_ae_restrict_of_ae_restrict_compl upperHalf
  · filter_upwards [he, self_mem_ae_restrict isOpen_upperHalf.measurableSet] with ξ hξ hmem
    change upperHalf.indicator (fun ξ => planeRepresentative b ξ * H ξ) ξ =
      outerInput (fun ξ => b ξ) (fun η => a η) z ξ
    simp only [indicator_of_mem hmem, outerInput, upperExtension, planeRepresentative,
      dite_eq_left hmem, dite_eq_left (show 0 < ξ.im from hmem)]
    rw [← hξ]
  · apply ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet.compl
    intro ξ hξ
    simp only [indicator_of_notMem hξ, outerInput, upperExtension,
      show ¬0 < ξ.im from hξ, dite_false]

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
