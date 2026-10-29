module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicPassiveCauchyData
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicPassiveL2Input
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicPassiveRegularL2Input
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonInnerL2Identification
public import LowDimensionalTopology.Unproved.Quasiconformal.ConformalCauchyCommutator
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# The actual first kernel variation and its radial limit

Finite first spatial jets and the ordinary normalized resolvent identify
the actual active kernel derivative. Its regularized singular identity
receives the independent fixed-map Cauchy commutator input explicitly.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory Topology Metric
open scoped ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC

section PlaneInput

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

theorem actual_passive_weighted_input_spatial_smooth
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (canonicalPassiveWeightedKernelInput R p q z t) upperHalf := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨ε, hε, hdata⟩ := actual_passive_conformal_data R p hp q
  refine ⟨ε, hε, ?_⟩
  intro t ht
  let F := canonicalBiparameterFamily R p q 0 t
  obtain ⟨hqc, hhol⟩ := hdata t (mem_ball_zero_iff.mpr ht)
  have hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F upperHalf :=
    (hhol.contDiffOn isOpen_upperHalf).restrict_scalars ℝ
  have hD : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv F) upperHalf :=
    ((hhol.deriv isOpen_upperHalf).contDiffOn isOpen_upperHalf).restrict_scalars ℝ
  have hQ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (QuadraticBergman.uniformizedQuadratic R p q) upperHalf :=
    ((utm_liftQD_differentiableOn q.property hp).contDiffOn isOpen_upperHalf).restrict_scalars ℝ
  have him : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => (w.im : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff
  have hμ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (harmonicPlane R p q) upperHalf :=
    (him.pow 2).contDiffOn.mul (Complex.conjCLE.contDiff.comp_contDiffOn hQ)
  have hden : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : ℂ => (F w - F (conj (z : ℂ))) ^ 2) upperHalf :=
    (hF.sub contDiffOn_const).pow 2
  have hne (w : ℂ) (hw : w ∈ upperHalf) : (F w - F (conj (z : ℂ))) ^ 2 ≠ 0 := by
    apply pow_ne_zero 2
    apply sub_ne_zero.mpr
    intro he
    have hwz : w = conj (z : ℂ) := hqc.1.2.2.1.2.1 (mem_univ _) (mem_univ _) he
    have hi := congrArg Complex.im hwz
    simp only [conj_im, UpperHalfPlane.coe_im] at hi
    linarith [show 0 < w.im from hw, z.im_pos]
  have hformula (w : ℂ) (hw : w ∈ upperHalf) :
      canonicalPassiveWeightedKernelInput R p q z t w =
        harmonicPlane R p q w * deriv F w / (F w - F (conj (z : ℂ))) ^ 2 := by
    simp only [canonicalPassiveWeightedKernelInput, WeilPetersson.SourceKernel.upperExtension,
      dite_eq_left (show 0 < w.im from hw)]
    change harmonicPlane R p q w * dz F w / (F w - F (conj (z : ℂ))) ^ 2 = _
    rw [dz_eq_deriv (hhol.differentiableAt (isOpen_upperHalf.mem_nhds hw))]
  apply ((hμ.mul hD).mul (hden.fun_inv hne)).congr
  intro w hw
  rw [hformula w hw]
  simp only [div_eq_mul_inv]

theorem actual_passive_weighted_input_radial_eq_hilbert_ae
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
      hilbertHSmooth (canonicalPassiveWeightedKernelInput R p q z t)
        =ᵐ[(volume : Measure ℂ).restrict upperHalf]
      hilbertH (canonicalPassiveWeightedKernelInput R p q z t) := by
  obtain ⟨ε₁, _, hε₁, _, hLp⟩ := canonicalPassiveWeightedKernelInput_uniform_memLp_two R p hp q z
  obtain ⟨ε₂, hε₂, hsmooth⟩ := actual_passive_weighted_input_spatial_smooth R p hp q z
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro t ht
  exact WeilPetersson.SourceKernel.hilbertHSmooth_eq_hilbertH_ae_upper
    (canonicalPassiveWeightedKernelInput R p q z t)
    (hLp t (ht.trans_le (min_le_left _ _))).1
    (hsmooth t (ht.trans_le (min_le_right _ _)))

theorem actual_passive_normalized_fixed_domain_potential
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → ∀ ξ : ℍ,
      let f := canonicalPassiveWeightedKernelInput R p q z t
      let a : ℂ := conj (z : ℂ)
      let P := fun v : ℂ => -(1 / Real.pi : ℂ) *
        ∫ w : ℂ, f w * (1 / (w - v) - 1 / (w - a))
      Integrable (fun w : ℂ => f w * (1 / (w - ξ) - 1 / (w - a))) volume ∧
        DifferentiableAt ℝ P (ξ : ℂ) ∧ dz P ξ = hilbertHSmooth f ξ ∧
        Tendsto (fun r : ℝ => -(1 / Real.pi : ℂ) *
          ∫ w in {w : ℂ | r < ‖w - ξ‖}, f w / (w - ξ) ^ 2)
          (𝓝[>] 0) (𝓝 (hilbertHSmooth f ξ)) := by
  obtain ⟨εL, _, hεL, _, hLp⟩ :=
    canonicalPassiveWeightedKernelInput_uniform_memLp_two R p hp q z
  obtain ⟨εS, hεS, hsmooth⟩ := actual_passive_weighted_input_spatial_smooth R p hp q z
  refine ⟨min εL εS, lt_min hεL hεS, ?_⟩
  intro t ht
  let f := canonicalPassiveWeightedKernelInput R p q z t
  let a : ℂ := conj (z : ℂ)
  let e : ℂ → ℂ := fun w => f w / (w - a)
  have hL : MemLp f 2 (volume : Measure ℂ) := (hLp t (ht.trans_le (min_le_left _ _))).1
  have hS : ContDiffOn ℝ 1 f upperHalf :=
    (hsmooth t (ht.trans_le (min_le_right _ _))).of_le (by simp)
  have hzero (w : ℂ) (hw : w ∉ upperHalf) : f w = 0 := by
    simp only [f, canonicalPassiveWeightedKernelInput, WeilPetersson.SourceKernel.upperExtension,
      dite_eq_right (show ¬0 < w.im from hw)]
  have ha : 0 < -a.im := by
    simpa only [a, conj_im, UpperHalfPlane.coe_im, neg_neg] using z.im_pos
  have hgap (w : ℂ) (hw : w ∈ upperHalf) : -a.im ≤ ‖w - a‖ := by
    calc
      -a.im ≤ w.im - a.im := by linarith [show 0 < w.im from hw]
      _ ≤ |(w - a).im| := by rw [sub_im]; exact le_abs_self _
      _ ≤ ‖w - a‖ := Complex.abs_im_le_norm _
  have hem : AEStronglyMeasurable e volume :=
    hL.aestronglyMeasurable.div₀ (measurable_id.sub measurable_const).aestronglyMeasurable
  have heLp : MemLp e 2 (volume : Measure ℂ) := by
    apply (hL.norm.const_mul (1 / -a.im)).mono' hem
    apply Eventually.of_forall
    intro w
    by_cases hw : w ∈ upperHalf
    · change ‖f w / (w - a)‖ ≤ 1 / -a.im * ‖f w‖
      rw [norm_div]
      calc
        ‖f w‖ / ‖w - a‖ ≤ ‖f w‖ / -a.im :=
          div_le_div_of_nonneg_left (norm_nonneg _) ha (hgap w hw)
        _ = _ := by ring
    · simp only [e, hzero w hw, zero_div, norm_zero, mul_zero, le_refl]
  have heC1 : ContDiffOn ℝ 1 e upperHalf := by
    have hden : ContDiffOn ℝ 1 (fun w : ℂ => w - a) upperHalf :=
      (contDiff_id.sub contDiff_const).contDiffOn
    have hne (w : ℂ) (hw : w ∈ upperHalf) : w - a ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      have hnorm := hgap w hw
      rw [h, sub_self, norm_zero] at hnorm
      linarith
    apply (hS.mul (hden.fun_inv hne)).congr
    intro w _hw
    simp only [e, div_eq_mul_inv]
  have haSquare : Integrable (fun w : ℂ => f w / (w - a) ^ 2) volume := by
    have hi := integrableOn_truncated_kernel (p := 2) (by norm_num)
      (by simpa using hL) a (show 0 < -a.im / 2 by positivity)
    apply hi.integrable_of_forall_notMem_eq_zero
    intro w hw
    have hnot : w ∉ upperHalf := by
      intro hwH
      have hnorm : ‖w - a‖ ≤ -a.im / 2 := le_of_not_gt hw
      linarith [hgap w hwH]
    rw [hzero w hnot, zero_div]
  have heValue (v : ℂ) (hv : v ∈ upperHalf) :
      Integrable (fun w : ℂ => e w / (w - v)) volume := by
    let r := v.im / 2
    have hr : 0 < r := by dsimp only [r]; linarith [show 0 < v.im from hv]
    have hsub : closedBall v r ⊆ upperHalf := by
      intro w hw
      have hn : ‖w - v‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hw
      have hi : v.im - w.im ≤ ‖w - v‖ := by
        calc
          v.im - w.im = -(w - v).im := by rw [sub_im]; ring
          _ ≤ |(w - v).im| := neg_le_abs _
          _ ≤ ‖w - v‖ := Complex.abs_im_le_norm _
      change 0 < w.im
      dsimp only [r] at hn
      linarith [show 0 < v.im from hv]
    obtain ⟨M, hM⟩ := (isCompact_closedBall v r).exists_bound_of_continuousOn
      (heC1.continuousOn.mono hsub)
    have hnear : IntegrableOn (fun w : ℂ => e w / (w - v)) (ball v r) := by
      have hker : IntegrableOn (fun w : ℂ => 1 / (w - v)) (ball v r) := by
        apply integrableOn_cauchy_kernel_of_subset (R := ‖v‖ + r) (by positivity) ?_ v
        intro w hw
        rw [mem_closedBall, dist_zero_right]
        have hnorm := norm_add_le (w - v) v
        rw [sub_add_cancel] at hnorm
        exact hnorm.trans (by
          have hn : ‖w - v‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
          linarith)
      apply (hker.norm.const_mul (max M 0)).mono'
        (hem.div₀ (measurable_id.sub measurable_const).aestronglyMeasurable).restrict
      apply ae_restrict_of_forall_mem isOpen_ball.measurableSet
      intro w hw
      have hb := hM w (ball_subset_closedBall hw)
      change ‖e w / (w - v)‖ ≤ max M 0 * ‖(1 : ℂ) / (w - v)‖
      rw [norm_div (e w) (w - v), norm_div (1 : ℂ) (w - v), norm_one]
      calc
        ‖e w‖ / ‖w - v‖ ≤ max M 0 / ‖w - v‖ :=
          div_le_div_of_nonneg_right (hb.trans (le_max_left _ _)) (norm_nonneg _)
        _ = _ := by ring
    have hvSquare : IntegrableOn (fun w : ℂ => f w / (w - v) ^ 2) (ball v r)ᶜ := by
      apply (integrableOn_truncated_kernel (p := 2) (by norm_num)
        (by simpa using hL) v (show 0 < r / 2 by positivity)).mono_set
      intro w hw
      have hn : r ≤ ‖w - v‖ := by
        simpa only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] using hw
      change r / 2 < ‖w - v‖
      linarith
    have hfar : IntegrableOn (fun w : ℂ => e w / (w - v)) (ball v r)ᶜ := by
      apply ((haSquare.norm.integrableOn.add hvSquare.norm).div_const 2).mono'
        (hem.div₀ (measurable_id.sub measurable_const).aestronglyMeasurable).restrict
      apply ae_restrict_of_forall_mem isOpen_ball.measurableSet.compl
      intro w hw
      change ‖e w / (w - v)‖ ≤
        (‖f w / (w - a) ^ 2‖ + ‖f w / (w - v) ^ 2‖) / 2
      by_cases hwH : w ∈ upperHalf
      · have hA : 0 < ‖w - a‖ := ha.trans_le (hgap w hwH)
        have hB : 0 < ‖w - v‖ := hr.trans_le (by
          simpa only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] using hw)
        have hAM : 1 / (‖w - a‖ * ‖w - v‖) ≤
            (1 / ‖w - a‖ ^ 2 + 1 / ‖w - v‖ ^ 2) / 2 := by
          have h := div_le_div_iff₀ (a := (1 : ℝ))
            (c := ‖w - a‖ ^ 2 + ‖w - v‖ ^ 2) (mul_pos hA hB)
            (show 0 < 2 * ‖w - a‖ ^ 2 * ‖w - v‖ ^ 2 by positivity)
          have hraw : 1 / (‖w - a‖ * ‖w - v‖) ≤
              (‖w - a‖ ^ 2 + ‖w - v‖ ^ 2) /
                (2 * ‖w - a‖ ^ 2 * ‖w - v‖ ^ 2) := h.mpr (by
            nlinarith [mul_nonneg (mul_nonneg hA.le hB.le)
              (sq_nonneg (‖w - a‖ - ‖w - v‖))])
          calc
            _ ≤ (‖w - a‖ ^ 2 + ‖w - v‖ ^ 2) /
                (2 * ‖w - a‖ ^ 2 * ‖w - v‖ ^ 2) := hraw
            _ = _ := by
              field_simp [ne_of_gt hA, ne_of_gt hB]
              ring
        simp only [e, norm_div, norm_pow]
        calc
          ‖f w‖ / ‖w - a‖ / ‖w - v‖ =
              ‖f w‖ * (1 / (‖w - a‖ * ‖w - v‖)) := by ring
          _ ≤ ‖f w‖ * ((1 / ‖w - a‖ ^ 2 + 1 / ‖w - v‖ ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left hAM (norm_nonneg _)
          _ = _ := by ring
      · simp only [e, hzero w hwH, zero_div, norm_zero, add_zero, le_refl]
    exact (integrableOn_univ.mp ((hnear.union hfar).mono_set (by simp)))
  intro ξ
  dsimp only
  let P : ℂ → ℂ := fun v => -(1 / Real.pi : ℂ) *
    ∫ w : ℂ, f w * (1 / (w - v) - 1 / (w - a))
  have hfactor (w : ℂ) : f w = (w - a) * e w := by
    by_cases hwa : w = a
    · subst w
      have hn : a ∉ upperHalf := by change ¬0 < a.im; linarith
      simp only [e, hzero a hn, sub_self, zero_div, mul_zero]
    · dsimp only [e]
      field_simp [sub_ne_zero.mpr hwa]
  have hnormalized (v : ℂ) (hv : v ∈ upperHalf) :
      Integrable (fun w : ℂ => f w * (1 / (w - v) - 1 / (w - a))) volume ∧
        P v = (v - a) * cauchyT e v := by
    have heq : (fun w : ℂ => f w * (1 / (w - v) - 1 / (w - a))) =ᵐ[volume]
        fun w : ℂ => (v - a) * (e w / (w - v)) := by
      filter_upwards [volume.ae_ne a, volume.ae_ne v] with w hwa hwv
      dsimp only [e]
      field_simp [sub_ne_zero.mpr hwa, sub_ne_zero.mpr hwv]
      ring
    refine ⟨((heValue v hv).const_mul (v - a)).congr heq.symm, ?_⟩
    dsimp only [P, cauchyT]
    rw [integral_congr_ae heq, integral_const_mul]
    ring
  obtain ⟨heDiff, heDz, heRadial⟩ := localized_cauchy_dz_and_radial e heLp heC1 heValue ξ
  have hlinear : HasDerivAt (fun v : ℂ => v - a) 1 (ξ : ℂ) :=
    (hasDerivAt_id (ξ : ℂ)).sub_const a
  have hPeq : P =ᶠ[𝓝 (ξ : ℂ)] fun v : ℂ => (v - a) * cauchyT e v := by
    filter_upwards [isOpen_upperHalf.mem_nhds ξ.im_pos] with v hv
    exact (hnormalized v hv).2
  have hPDiff : DifferentiableAt ℝ P (ξ : ℂ) :=
    ((hlinear.differentiableAt.restrictScalars ℝ).mul heDiff).congr_of_eventuallyEq hPeq
  have hPDz : dz P ξ = ((ξ : ℂ) - a) * hilbertHSmooth e ξ + cauchyT e ξ := by
    rw [dz, hPeq.fderiv_eq (𝕜 := ℝ)]
    change dz (fun v : ℂ => (v - a) * cauchyT e v) ξ = _
    rw [dz_mul (hlinear.differentiableAt.restrictScalars ℝ) heDiff,
      heDz, dz_eq_deriv hlinear.differentiableAt, hlinear.deriv, mul_one]
  have heTrunc : Tendsto (fun r : ℝ => -(1 / Real.pi : ℂ) *
      ∫ w in {w : ℂ | r < ‖w - ξ‖}, e w / (w - ξ)) (𝓝[>] 0) (𝓝 (cauchyT e ξ)) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure ℂ))
      (F := fun r : ℝ => {w : ℂ | r < ‖w - ξ‖}.indicator (fun w => e w / (w - ξ)))
      (f := fun w : ℂ => e w / (w - ξ)) (fun w => ‖e w / (w - ξ)‖)
      (Eventually.of_forall fun r => (heValue ξ ξ.im_pos).aestronglyMeasurable.indicator
        (measurableSet_lt measurable_const (measurable_id.sub_const (ξ : ℂ)).norm))
      (Eventually.of_forall fun r => Eventually.of_forall fun w => by
        by_cases hw : r < ‖w - ξ‖
        · exact (congrArg norm (indicator_of_mem
            (show w ∈ {w : ℂ | r < ‖w - ξ‖} from hw)
            (fun w : ℂ => e w / (w - ξ)))).le
        · rw [indicator_of_notMem (show w ∉ {w : ℂ | r < ‖w - ξ‖} from hw), norm_zero]
          exact norm_nonneg _)
      (heValue ξ ξ.im_pos).norm (by
        filter_upwards [volume.ae_ne (ξ : ℂ)] with w hw
        have hn : 0 < ‖w - ξ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw)
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioo_mem_nhdsGT hn] with r hr
        exact (indicator_of_mem (show w ∈ {w : ℂ | r < ‖w - ξ‖} from hr.2)
          (fun w : ℂ => e w / (w - ξ))).symm)
    have heq (r : ℝ) :
        (∫ w : ℂ, {w : ℂ | r < ‖w - ξ‖}.indicator (fun w => e w / (w - ξ)) w) =
          ∫ w in {w : ℂ | r < ‖w - ξ‖}, e w / (w - ξ) :=
      integral_indicator (measurableSet_lt measurable_const (measurable_id.sub_const (ξ : ℂ)).norm)
    simpa only [heq, cauchyT] using hh.const_mul (-(1 / Real.pi : ℂ))
  have hRadial : Tendsto (fun r : ℝ => -(1 / Real.pi : ℂ) *
      ∫ w in {w : ℂ | r < ‖w - ξ‖}, f w / (w - ξ) ^ 2) (𝓝[>] 0)
      (𝓝 (((ξ : ℂ) - a) * hilbertHSmooth e ξ + cauchyT e ξ)) := by
    apply ((heRadial.const_mul ((ξ : ℂ) - a)).add heTrunc).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have heInt := integrableOn_truncated_kernel (p := 2) (by norm_num)
      (by simpa using heLp) (ξ : ℂ) hr
    have hInt : (∫ w in {w : ℂ | r < ‖w - ξ‖}, f w / (w - ξ) ^ 2) =
        ((ξ : ℂ) - a) * (∫ w in {w : ℂ | r < ‖w - ξ‖}, e w / (w - ξ) ^ 2) +
          ∫ w in {w : ℂ | r < ‖w - ξ‖}, e w / (w - ξ) := by
      rw [← integral_const_mul, ← integral_add (heInt.const_mul ((ξ : ℂ) - a))
        (heValue ξ ξ.im_pos).integrableOn]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const
        (measurable_id.sub_const (ξ : ℂ)).norm)] with w hw
      have hwξ : w - ξ ≠ 0 := norm_pos_iff.mp (hr.trans hw)
      rw [hfactor w]
      field_simp [hwξ]
      ring
    rw [hInt]
    ring
  have hH : hilbertHSmooth f ξ = ((ξ : ℂ) - a) * hilbertHSmooth e ξ + cauchyT e ξ :=
    hRadial.limUnder_eq
  refine ⟨(hnormalized ξ ξ.im_pos).1, hPDiff, hPDz.trans hH.symm, ?_⟩
  exact hH.symm ▸ hRadial

end PlaneInput

section Kernel

universe w
variable {Y : Type w} [TopologicalSpace Y] (S : ClosedRiemannSurface Y) (pS : ℍ → Y)

private theorem line_parameter_derivative_exchange
    {F D : ℂ → ℝ → ℂ} {V : ℝ → ℂ} {r ρ C : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ)
    (hspatial : ∀ s ∈ ball (0 : ℂ) r, ∀ u ∈ ball (0 : ℝ) ρ,
      HasDerivAt (F s) (D s u) u)
    (hholo : ∀ u ∈ ball (0 : ℝ) ρ,
      DifferentiableOn ℂ (fun s => D s u) (ball 0 r))
    (hbound : ∀ u ∈ ball (0 : ℝ) ρ, ∀ s ∈ ball (0 : ℂ) r, ‖D s u‖ ≤ C)
    (hpoint : ∀ u ∈ ball (0 : ℝ) ρ, HasDerivAt (fun s : ℂ => F s u) (V u) 0) :
    HasDerivAt V (deriv (fun s : ℂ => D s 0) 0) 0 := by
  let Q : ℂ → ℝ → ℂ := fun s u => (F s u - F 0 u) / s
  let Q' : ℂ → ℝ → ℂ := fun s u => (D s u - D 0 u) / s
  let V' : ℝ → ℂ := fun u => deriv (fun s : ℂ => D s u) 0
  have hQ' : TendstoUniformlyOn Q' V' (𝓝[≠] (0 : ℂ)) (ball (0 : ℝ) ρ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun s : ℂ => 8 * C / r ^ 2 * ‖s‖)
        (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      simpa only [norm_zero, mul_zero] using
        ((continuous_norm.tendsto (0 : ℂ)).const_mul (8 * C / r ^ 2)).mono_left
          nhdsWithin_le_nhds
    filter_upwards [hlim.eventually (gt_mem_nhds hε), self_mem_nhdsWithin,
      nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (by positivity : 0 < r / 2))]
      with s hsε hsne hs u hu
    have hs0 : s ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hsne
    have hsmall : ‖s‖ < r / 2 := mem_ball_zero_iff.mp hs
    rw [dist_eq_norm, norm_sub_rev]
    have hest : ‖Q' s u - V' u‖ ≤ 8 * C / r ^ 2 * ‖s‖ := by
      simpa only [Q', V', zero_add] using
        bB_h0_diffQuot_le hr (hholo u hu) (hbound u hu) hs0 hsmall
    exact hest.trans_lt hsε
  have hQ : ∀ᶠ s : ℂ in 𝓝[≠] (0 : ℂ), ∀ u ∈ ball (0 : ℝ) ρ,
      HasDerivAt (Q s) (Q' s u) u := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hr)] with s hs u hu
    exact ((hspatial s hs u hu).sub
      (hspatial 0 (mem_ball_self hr) u hu)).div_const s
  have hpoint' : ∀ u ∈ ball (0 : ℝ) ρ,
      Tendsto (fun s : ℂ => Q s u) (𝓝[≠] 0) (𝓝 (V u)) := by
    intro u hu
    simpa only [Q, zero_add, div_eq_mul_inv, smul_eq_mul, mul_comm] using
      (hpoint u hu).tendsto_slope_zero
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_ball hQ' hQ hpoint' (mem_ball_self hρ)

/-- The ordinary target Cauchy integral for the actual passive deformation has
the original radial Hilbert term and an absolutely integrable regular correction,
conditional on the independent conformal Cauchy commutator differentiation. -/
theorem actual_passive_pulled_potential_dz_of_commutator
    (hcomm : LowDimensionalTopology.Unproved.Quasiconformal.ConformalCauchyCommutatorDifferentiation)
    {Γ : Subgroup Deck}
    (hp : let := S.toRiemannAtlas.toChartedSpace; IsUniformization Γ pS)
    (q : HolomorphicQuadraticDifferential S.toRiemannAtlas) (z x : ℍ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
      let F := canonicalBiparameterFamily S pS q 0 t
      let b := F (conj (z : ℂ))
      let β := ahT_dot (fun y : ℂ => if y.im < 0 then 0 else harmonicPlane S pS q y)
        (harmonicBiparameterCoefficient S pS q 0 t) F
      let f := canonicalPassiveWeightedKernelInput S pS q z t
      let R := canonicalPassiveRegularKernelInput S pS q x t
      let U := fun v : ℂ => cauchyT (fun y => β y / (y - b) ^ 2) (F v)
      Integrable (fun y : ℂ => f y * R y) volume ∧
        DifferentiableAt ℝ U (x : ℂ) ∧
        dz U x = hilbertHSmooth f x - (1 / Real.pi : ℂ) * ∫ y : ℂ, f y * R y := by
  obtain ⟨εL, _, hεL, _, hLp⟩ :=
    canonicalPassiveWeightedKernelInput_uniform_memLp_two S pS hp q z
  obtain ⟨εS, hεS, hsmooth⟩ := actual_passive_weighted_input_spatial_smooth S pS hp q z
  obtain ⟨εF, hεF, hdata⟩ := actual_passive_conformal_data S pS hp q
  obtain ⟨εV, hεV, hpull⟩ := actual_passive_weighted_cauchy_pullback S pS hp q z
  obtain ⟨εR, _, hεR, _, hregular⟩ := canonicalPassiveRegularKernelInput_uniform_memLp_two S pS hp q x
  obtain ⟨εN, hεN, hnormalized⟩ := actual_passive_normalized_fixed_domain_potential S pS hp q z
  let ε := min εL (min εS (min εF (min εV (min εR εN))))
  have hε : 0 < ε := lt_min hεL (lt_min hεS (lt_min hεF (lt_min hεV (lt_min hεR hεN))))
  refine ⟨ε, hε, ?_⟩
  intro t ht
  dsimp only
  have htL : ‖t‖ < εL := ht.trans_le (min_le_left _ _)
  have htS : ‖t‖ < εS := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htF : ‖t‖ < εF := ht.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htV : ‖t‖ < εV := ht.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have htR : ‖t‖ < εR := ht.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have htN : ‖t‖ < εN := ht.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  let F := canonicalBiparameterFamily S pS q 0 t
  let a : ℂ := conj (z : ℂ)
  let b := F a
  let β := ahT_dot (fun y : ℂ => if y.im < 0 then 0 else harmonicPlane S pS q y)
    (harmonicBiparameterCoefficient S pS q 0 t) F
  let f := canonicalPassiveWeightedKernelInput S pS q z t
  let R := canonicalPassiveRegularKernelInput S pS q x t
  let U : ℂ → ℂ := fun v => cauchyT (fun y => β y / (y - b) ^ 2) (F v)
  let V : ℂ → ℂ := fun v => -(1 / Real.pi : ℂ) *
    ∫ y : ℂ in upperHalf, f y * deriv F y / (F y - F v)
  let P : ℂ → ℂ := fun v => -(1 / Real.pi : ℂ) *
    ∫ y : ℂ, f y * (1 / (y - v) - 1 / (y - a))
  obtain ⟨hqc, hhol⟩ := hdata t (mem_ball_zero_iff.mpr htF)
  have hL : MemLp f 2 (volume : Measure ℂ) := (hLp t htL).1
  have hS : ContDiffOn ℝ 1 f upperHalf := (hsmooth t htS).of_le (by simp)
  have hzero (y : ℂ) (hy : y ∉ upperHalf) : f y = 0 := by
    simp only [f, canonicalPassiveWeightedKernelInput, WeilPetersson.SourceKernel.upperExtension,
      dite_eq_right (show ¬0 < y.im from hy)]
  have ha : a ∈ lowerHalf := by
    change a.im < 0
    simpa only [a, conj_im, UpperHalfPlane.coe_im] using neg_lt_zero.mpr z.im_pos
  have hf (y : ℂ) (hy : y ∈ upperHalf) :
      f y = harmonicPlane S pS q y * deriv F y / (F y - b) ^ 2 := by
    simp only [f, canonicalPassiveWeightedKernelInput, WeilPetersson.SourceKernel.upperExtension,
      dite_eq_left (show 0 < y.im from hy)]
    change harmonicPlane S pS q y * dz F y / (F y - b) ^ 2 = _
    rw [dz_eq_deriv (hhol.differentiableAt (isOpen_upperHalf.mem_nhds hy))]
  have hweight (v y : ℂ) (hy : y ∈ upperHalf) :
      f y * deriv F y / (F y - F v) = harmonicPlane S pS q y * deriv F y ^ 2 /
        ((F y - b) ^ 2 * (F y - F v)) := by
    rw [hf y hy]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hVi (ξ : ℍ) : IntegrableOn
      (fun y : ℂ => f y * deriv F y / (F y - F ξ)) upperHalf :=
    (hpull t htV (F ξ)).1.congr_fun (fun y hy => (hweight ξ y hy).symm)
      isOpen_upperHalf.measurableSet
  have hVU (ξ : ℍ) : V ξ = U ξ := by
    have he := (hpull t htV (F ξ)).2
    change _ = cauchyT (fun y => β y / (y - b) ^ 2) (F ξ)
    exact (congrArg (fun c : ℂ => -(1 / Real.pi : ℂ) * c)
      (setIntegral_congr_fun isOpen_upperHalf.measurableSet (hweight ξ))).trans he.symm
  let R₀ : ℂ → ℂ := upperHalf.indicator (fun y : ℂ =>
    deriv F x * deriv F y / (F x - F y) ^ 2 - 1 / ((x : ℂ) - y) ^ 2)
  have hR₀ : R₀ = R := by
    funext y
    by_cases hy : y ∈ upperHalf
    · simp only [R₀, R, canonicalPassiveRegularKernelInput, indicator_of_mem hy]
      rw [dz_eq_deriv (hhol.differentiableAt (isOpen_upperHalf.mem_nhds x.im_pos)),
        dz_eq_deriv (hhol.differentiableAt (isOpen_upperHalf.mem_nhds hy))]
    · simp only [R₀, R, canonicalPassiveRegularKernelInput, indicator_of_notMem hy]
  have hR : MemLp R 2 (volume : Measure ℂ) := (hregular t htR).1
  have hRi : Integrable (fun y : ℂ => f y * R y) volume := hL.integrable_mul hR
  have hNi (ξ : ℍ) : Integrable
      (fun y : ℂ => f y * (1 / (y - ξ) - 1 / (y - a))) volume :=
    (hnormalized t htN ξ).1
  have hB := hcomm F f a hqc hhol ha hL hS hzero hNi hVi x (by
    change MemLp R₀ 2 (volume : Measure ℂ)
    rw [hR₀]
    exact hR)
  change DifferentiableAt ℝ (fun v : ℂ => V v - P v) (x : ℂ) ∧
    dz (fun v : ℂ => V v - P v) x = -(1 / Real.pi : ℂ) *
      ∫ y : ℂ in upperHalf, f y *
        (deriv F x * deriv F y / (F x - F y) ^ 2 - 1 / ((x : ℂ) - y) ^ 2) at hB
  have hPDiff : DifferentiableAt ℝ P (x : ℂ) := (hnormalized t htN x).2.1
  have hPDz : dz P x = hilbertHSmooth f x := (hnormalized t htN x).2.2.1
  have hVDiff : DifferentiableAt ℝ V (x : ℂ) := by
    apply (hB.1.add hPDiff).congr_of_eventuallyEq
    exact Eventually.of_forall (fun v => by change V v = (V v - P v) + P v; ring)
  have hCorr : (∫ y : ℂ in upperHalf, f y *
      (deriv F x * deriv F y / (F x - F y) ^ 2 - 1 / ((x : ℂ) - y) ^ 2)) =
      ∫ y : ℂ, f y * R y := by
    calc
      _ = ∫ y : ℂ in upperHalf, f y * R₀ y :=
        setIntegral_congr_fun isOpen_upperHalf.measurableSet (fun y hy => by
          simp only [R₀, indicator_of_mem hy])
      _ = ∫ y : ℂ, f y * R₀ y :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
          simp only [R₀, indicator_of_notMem hy, mul_zero])
      _ = _ := by rw [hR₀]
  have hVDz : dz V x = hilbertHSmooth f x - (1 / Real.pi : ℂ) * ∫ y : ℂ, f y * R y := by
    calc
      dz V x = dz (fun v : ℂ => V v - P v) x + dz P x := by
        rw [dz_sub_pointwise hVDiff hPDiff]
        ring
      _ = _ := by rw [hB.2, hPDz, hCorr]; ring
  have heq : U =ᶠ[𝓝 (x : ℂ)] V := by
    filter_upwards [isOpen_upperHalf.mem_nhds x.im_pos] with v hv
    exact (hVU (⟨v, hv⟩ : ℍ)).symm
  refine ⟨hRi, hVDiff.congr_of_eventuallyEq heq, ?_⟩
  unfold dz at hVDz ⊢
  rw [heq.fderiv_eq (𝕜 := ℝ)]
  exact hVDz

private theorem actual_active_first_spatial_local_direction_bound
    {Γ : Subgroup Deck}
    (hp : let := S.toRiemannAtlas.toChartedSpace; IsUniformization Γ pS)
    (q : HolomorphicQuadraticDifferential S.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → ∀ z ∈ upperHalf ∪ lowerHalf,
      ∃ δ ρ C : ℝ, 0 < δ ∧ δ ≤ ε ∧ 0 < ρ ∧ 0 ≤ C ∧
        ball z ρ ⊆ upperHalf ∪ lowerHalf ∧
        ∀ s : ℂ, ‖s‖ < δ → ∀ w ∈ ball z ρ, ∀ v : ℂ, ‖v‖ = 1 →
          ‖fderiv ℝ (canonicalBiparameterFamily S pS q s t) w v‖ ≤ C := by
  obtain ⟨ε, hε, hC1, hreflect, hlocal, _⟩ :=
    canonicalBiparameterFamily_spatial_c1_compact_control S pS hp q
  refine ⟨ε, hε, ?_⟩
  intro t ht z hz
  rcases hz with hz | hz
  · obtain ⟨r, C, hr, hC, _, hrH, hbound⟩ := hlocal 0 (mem_ball_self hε) z hz
    refine ⟨min r ε, r, C, lt_min hr hε, min_le_right _ _, hr, hC,
      fun w hw => Or.inl (hrH hw), ?_⟩
    intro s hs w hw v hv
    calc
      ‖fderiv ℝ (canonicalBiparameterFamily S pS q s t) w v‖ ≤
          ‖fderiv ℝ (canonicalBiparameterFamily S pS q s t) w‖ * ‖v‖ :=
        (fderiv ℝ (canonicalBiparameterFamily S pS q s t) w).le_opNorm v
      _ ≤ C := by
        rw [hv, mul_one]
        exact hbound s (mem_ball_zero_iff.mpr (hs.trans_le (min_le_left _ _)))
          t (mem_ball_zero_iff.mpr ht) w hw
  · have hcz : conj z ∈ upperHalf := by
      change 0 < (conj z).im
      simpa only [conj_im, neg_pos] using (show z.im < 0 from hz)
    have hct : conj t ∈ ball (0 : ℂ) ε := by
      simpa only [mem_ball_zero_iff, norm_conj] using ht
    obtain ⟨r, C, hr, hC, _, hrH, hbound⟩ := hlocal (conj t) hct (conj z) hcz
    have hconjball (w : ℂ) (hw : w ∈ ball z r) : conj w ∈ ball (conj z) r := by
      simpa only [mem_ball, dist_eq_norm, ← map_sub, norm_conj] using hw
    have hlower (w : ℂ) (hw : w ∈ ball z r) : w ∈ lowerHalf := by
      have h := hrH (hconjball w hw)
      change 0 < (conj w).im at h
      change w.im < 0
      simpa only [conj_im, neg_pos] using h
    refine ⟨ε, r, C, hε, le_rfl, hr, hC, fun w hw => Or.inr (hlower w hw), ?_⟩
    intro s hs w hw v hv
    let F := canonicalBiparameterFamily S pS q s t
    let G := canonicalBiparameterFamily S pS q (conj t) (conj s)
    have hF : DifferentiableAt ℝ F w :=
      (hC1 s t hs ht).differentiableOn_one.differentiableAt
        ((isOpen_upperHalf.union isOpen_lowerHalf).mem_nhds (Or.inr (hlower w hw)))
    have hG : DifferentiableAt ℝ G (conj w) :=
      (hC1 (conj t) (conj s) (by simpa only [norm_conj] using ht)
        (by simpa only [norm_conj] using hs)).differentiableOn_one.differentiableAt
          ((isOpen_upperHalf.union isOpen_lowerHalf).mem_nhds
            (Or.inl (hrH (hconjball w hw))))
    have hJ : dz F w = conj (dz G (conj w)) ∧
        dzbar F w = conj (dzbar G (conj w)) := by
      rw [show F = fun y : ℂ => conj (G (conj y)) from hreflect s t hs ht]
      exact (abR_x_dz_dzbar_conj hG).2
    have hD : fderiv ℝ F w v = conj (fderiv ℝ G (conj w) (conj v)) := by
      rw [fderiv_eq_dz_dzbar hF v, fderiv_eq_dz_dzbar hG (conj v), hJ.1, hJ.2]
      simp only [map_add, map_mul, Complex.conj_conj]
    change ‖fderiv ℝ F w v‖ ≤ C
    rw [hD, norm_conj]
    calc
      ‖fderiv ℝ G (conj w) (conj v)‖ ≤ ‖fderiv ℝ G (conj w)‖ * ‖conj v‖ :=
        (fderiv ℝ G (conj w)).le_opNorm (conj v)
      _ ≤ C := by
        rw [norm_conj, hv, mul_one]
        exact hbound (conj t) (mem_ball_self hr) (conj s)
          (by simpa only [mem_ball_zero_iff, norm_conj] using hs) (conj w) (hconjball w hw)

private theorem actual_active_directional_variation_at_passive
    {Γ : Subgroup Deck}
    (hp : let := S.toRiemannAtlas.toChartedSpace; IsUniformization Γ pS)
    (q : HolomorphicQuadraticDifferential S.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → ∀ z ∈ upperHalf ∪ lowerHalf,
      let F := canonicalBiparameterFamily S pS q 0 t
      let β := ahT_dot (fun y : ℂ => if y.im < 0 then 0 else harmonicPlane S pS q y)
        (harmonicBiparameterCoefficient S pS q 0 t) F
      ∀ v : ℂ, ‖v‖ = 1 →
        HasDerivAt (fun u : ℝ => ahVar β (F (z + u • v)))
          (deriv (fun s : ℂ => fderiv ℝ (canonicalBiparameterFamily S pS q s t) z v) 0) 0 := by
  obtain ⟨εB, hεB, hlocal⟩ := actual_active_first_spatial_local_direction_bound S pS hp q
  obtain ⟨εP, hεP, hC1, hfirst, _, _⟩ :=
    canonicalBiparameterFamily_first_spatial_parameter_control S pS hp q
  obtain ⟨εV, hεV, hpoint⟩ := actual_point_parameter_variation_at_passive S pS hp q
  let ε := min εB (min εP εV)
  have hε : 0 < ε := lt_min hεB (lt_min hεP hεV)
  refine ⟨ε, hε, ?_⟩
  intro t ht z hz
  dsimp only
  intro v hv
  have htB : ‖t‖ < εB := ht.trans_le (min_le_left _ _)
  have htP : ‖t‖ < εP := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htV : ‖t‖ < εV := ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨δ, ρ, C, hδ, _, hρ, _, hρU, hbound⟩ := hlocal t htB z hz
  let σ := min δ εP
  have hσ : 0 < σ := lt_min hδ hεP
  let A : ℂ → ℝ → ℂ := fun s u => canonicalBiparameterFamily S pS q s t (z + u • v)
  let D : ℂ → ℝ → ℂ := fun s u =>
    fderiv ℝ (canonicalBiparameterFamily S pS q s t) (z + u • v) v
  let F := canonicalBiparameterFamily S pS q 0 t
  let β := ahT_dot (fun y : ℂ => if y.im < 0 then 0 else harmonicPlane S pS q y)
    (harmonicBiparameterCoefficient S pS q 0 t) F
  have hw (u : ℝ) (hu : u ∈ ball (0 : ℝ) ρ) : z + u • v ∈ ball z ρ := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv,
      mul_one, sub_zero] using hu
  have hspatial (s : ℂ) (hs : s ∈ ball (0 : ℂ) σ) (u : ℝ) (hu : u ∈ ball (0 : ℝ) ρ) :
      DifferentiableAt ℝ (canonicalBiparameterFamily S pS q s t) (z + u • v) :=
    (hC1 s t ((mem_ball_zero_iff.mp hs).trans_le (min_le_right _ _)) htP).differentiableOn_one.differentiableAt
        ((isOpen_upperHalf.union isOpen_lowerHalf).mem_nhds (hρU (hw u hu)))
  have hline (u : ℝ) : HasDerivAt (fun a : ℝ => z + a • v) v u := by
    change HasFDerivAtFilter (fun a : ℝ => z + a • v)
      (ContinuousLinearMap.toSpanSingleton ℝ v) (𝓝 u ×ˢ pure u)
    apply HasFDerivAtFilter.of_isLittleOTVS
    exact (Asymptotics.IsLittleOTVS.zero _ _).congr_left (fun a => by
      simp only [ContinuousLinearMap.toSpanSingleton_apply, add_sub_add_left_eq_sub,
        sub_smul, sub_self, Pi.zero_apply])
  have hAs (s : ℂ) (hs : s ∈ ball (0 : ℂ) σ) (u : ℝ) (hu : u ∈ ball (0 : ℝ) ρ) :
      HasDerivAt (A s) (D s u) u :=
    (hspatial s hs u hu).hasFDerivAt.comp_hasDerivAt u (hline u)
  have hDholo (u : ℝ) (hu : u ∈ ball (0 : ℝ) ρ) :
      DifferentiableOn ℂ (fun s => D s u) (ball 0 σ) := by
    obtain ⟨h₁, h₂⟩ := hfirst t htP (z + u • v) (hρU (hw u hu))
    apply (((h₁.mul_const v).add (h₂.mul_const (conj v))).mono
      (ball_subset_ball (min_le_right _ _))).congr
    intro s hs
    exact fderiv_eq_dz_dzbar (hspatial s hs u hu) v
  have hDnorm (u : ℝ) (hu : u ∈ ball (0 : ℝ) ρ) (s : ℂ) (hs : s ∈ ball (0 : ℂ) σ) :
      ‖D s u‖ ≤ C :=
    hbound s ((mem_ball_zero_iff.mp hs).trans_le (min_le_left _ _))
      (z + u • v) (hw u hu) v hv
  have hApoint (u : ℝ) (_hu : u ∈ ball (0 : ℝ) ρ) :
      HasDerivAt (fun s : ℂ => A s u) (ahVar β (F (z + u • v))) 0 :=
    hpoint t htV (z + u • v)
  simpa only [A, D, F, β, zero_smul, add_zero] using
    line_parameter_derivative_exchange hσ hρ hAs hDholo hDnorm hApoint

private theorem actual_active_first_jet_variation_at_passive
    {Γ : Subgroup Deck}
    (hp : let := S.toRiemannAtlas.toChartedSpace; IsUniformization Γ pS)
    (q : HolomorphicQuadraticDifferential S.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → ∀ z ∈ upperHalf ∪ lowerHalf,
      let F := canonicalBiparameterFamily S pS q 0 t
      let β := ahT_dot (fun y : ℂ => if y.im < 0 then 0 else harmonicPlane S pS q y)
        (harmonicBiparameterCoefficient S pS q 0 t) F
      DifferentiableAt ℝ (fun y : ℂ => ahVar β (F y)) z →
        HasDerivAt (fun s : ℂ => dz (canonicalBiparameterFamily S pS q s t) z)
          (dz (fun y : ℂ => ahVar β (F y)) z) 0 := by
  obtain ⟨εD, hεD, hdir⟩ := actual_active_directional_variation_at_passive S pS hp q
  obtain ⟨εP, hεP, hC1, hfirst, _, _⟩ :=
    canonicalBiparameterFamily_first_spatial_parameter_control S pS hp q
  let ε := min εD εP
  have hε : 0 < ε := lt_min hεD hεP
  refine ⟨ε, hε, ?_⟩
  intro t ht z hz
  dsimp only
  intro hV
  let F := canonicalBiparameterFamily S pS q 0 t
  let β := ahT_dot (fun y : ℂ => if y.im < 0 then 0 else harmonicPlane S pS q y)
    (harmonicBiparameterCoefficient S pS q 0 t) F
  let V : ℂ → ℂ := fun y => ahVar β (F y)
  have htD : ‖t‖ < εD := ht.trans_le (min_le_left _ _)
  have htP : ‖t‖ < εP := ht.trans_le (min_le_right _ _)
  have he (v : ℂ) (hv : ‖v‖ = 1) :
      deriv (fun s : ℂ => fderiv ℝ (canonicalBiparameterFamily S pS q s t) z v) 0 =
        fderiv ℝ V z v := by
    have h₁ := hdir t htD z hz v hv
    have hline : HasDerivAt (fun u : ℝ => z + u • v) v 0 := by
      change HasFDerivAtFilter (fun u : ℝ => z + u • v)
        (ContinuousLinearMap.toSpanSingleton ℝ v) (𝓝 (0 : ℝ) ×ˢ pure 0)
      apply HasFDerivAtFilter.of_isLittleOTVS
      exact (Asymptotics.IsLittleOTVS.zero _ _).congr_left (fun u => by
        simp only [ContinuousLinearMap.toSpanSingleton_apply, add_sub_add_left_eq_sub,
          sub_smul, sub_self, Pi.zero_apply])
    have h₂ : HasDerivAt (fun u : ℝ => V (z + u • v)) (fderiv ℝ V z v) 0 := by
      have hV' : HasFDerivAt V (fderiv ℝ V z) (z + (0 : ℝ) • v) := by
        simpa only [zero_smul, add_zero] using
          (show DifferentiableAt ℝ V z from hV).hasFDerivAt
      simpa only [Function.comp_def, zero_smul, add_zero] using
        hV'.comp_hasDerivAt (0 : ℝ) hline
    exact h₁.unique h₂
  have hD (v : ℂ) (hv : ‖v‖ = 1) :
      HasDerivAt (fun s : ℂ => fderiv ℝ (canonicalBiparameterFamily S pS q s t) z v)
        (fderiv ℝ V z v) 0 := by
    obtain ⟨h₁, h₂⟩ := hfirst t htP z hz
    have hd : DifferentiableOn ℂ
        (fun s => dz (canonicalBiparameterFamily S pS q s t) z * v +
          dzbar (canonicalBiparameterFamily S pS q s t) z * conj v) (ball 0 εP) :=
      (h₁.mul_const v).add (h₂.mul_const (conj v))
    have hf : DifferentiableAt ℂ
        (fun s => fderiv ℝ (canonicalBiparameterFamily S pS q s t) z v) 0 := by
      apply (hd.congr (fun s hs => ?_)).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self hεP))
      exact fderiv_eq_dz_dzbar
        ((hC1 s t (mem_ball_zero_iff.mp hs) htP).differentiableOn_one.differentiableAt
          ((isOpen_upperHalf.union isOpen_lowerHalf).mem_nhds hz)) v
    exact hf.hasDerivAt.congr_deriv (he v hv)
  have h := ((hD 1 (by simp)).sub ((hD Complex.I (by simp)).const_mul Complex.I)).div_const 2
  exact h

private theorem dz_add_at {f g : ℂ → ℂ} {x : ℂ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dz (fun y : ℂ => f y + g y) x = dz f x + dz g x := by
  simp only [dz, fderiv_fun_add hf hg, add_apply]
  ring

/-- The actual normalized kernel has its first active parameter derivative
given by the original radial principal value and an ordinary regular correction.
The sole analytic input is the independent fixed-map Cauchy commutator statement.
The coefficient at the lower point is its actual real Wirtinger derivative. -/
theorem canonicalBiparameterKernel_active_first_variation_of_commutator
    (hcomm : LowDimensionalTopology.Unproved.Quasiconformal.ConformalCauchyCommutatorDifferentiation)
    {Γ : Subgroup Deck}
    (hp : let := S.toRiemannAtlas.toChartedSpace; IsUniformization Γ pS)
    (q : HolomorphicQuadraticDifferential S.toRiemannAtlas) (z x : ℍ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
      let F := canonicalBiparameterFamily S pS q 0 t
      let a : ℂ := conj (z : ℂ)
      let f := canonicalPassiveWeightedKernelInput S pS q z t
      let R := canonicalPassiveRegularKernelInput S pS q x t
      Integrable (fun y : ℂ => f y * R y) volume ∧
        Tendsto (fun r : ℝ => -(1 / Real.pi : ℂ) *
          ∫ y in {y : ℂ | r < ‖y - x‖}, f y / (y - x) ^ 2)
          (𝓝[>] 0) (𝓝 (hilbertHSmooth f x)) ∧
        HasDerivAt (fun s : ℂ =>
          dz (canonicalBiparameterFamily S pS q s t) x *
            dz (canonicalBiparameterFamily S pS q s t) a /
            (canonicalBiparameterFamily S pS q s t x -
              canonicalBiparameterFamily S pS q s t a) ^ 2)
          (dz F a * (hilbertHSmooth f x -
            (1 / Real.pi : ℂ) * ∫ y : ℂ, f y * R y)) 0 := by
  obtain ⟨εU, hεU, hUdata⟩ := actual_passive_pulled_potential_dz_of_commutator S pS hcomm hp q z x
  obtain ⟨εN, hεN, hnormalized⟩ := actual_passive_normalized_resolvent S pS hp q z
  obtain ⟨εJ, hεJ, hjet⟩ := actual_active_first_jet_variation_at_passive S pS hp q
  obtain ⟨εV, hεV, hpoint⟩ := actual_point_parameter_variation_at_passive S pS hp q
  obtain ⟨εS, hεS, hC1, _, _, _⟩ :=
    canonicalBiparameterFamily_spatial_c1_compact_control S pS hp q
  obtain ⟨εG, d₀, hεG, hd₀, hgap⟩ := actual_passive_pole_image_gap S pS hp q z
  obtain ⟨εT, hεT, hradial⟩ := actual_passive_normalized_fixed_domain_potential S pS hp q z
  let δ := min εU (min εN (min εJ (min εV (min εS εG))))
  have hδ : 0 < δ := lt_min hεU (lt_min hεN (lt_min hεJ (lt_min hεV (lt_min hεS hεG))))
  refine ⟨min δ εT, lt_min hδ hεT, ?_⟩
  intro t ht
  dsimp only
  have htδ : ‖t‖ < δ := ht.trans_le (min_le_left _ _)
  have htT : ‖t‖ < εT := ht.trans_le (min_le_right _ _)
  have htU : ‖t‖ < εU := htδ.trans_le (min_le_left _ _)
  have htN : ‖t‖ < εN := htδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htJ : ‖t‖ < εJ := htδ.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htV : ‖t‖ < εV := htδ.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have htS : ‖t‖ < εS := htδ.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have htG : ‖t‖ < εG := htδ.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  let F := canonicalBiparameterFamily S pS q 0 t
  let a : ℂ := conj (z : ℂ)
  let b := F a
  let β := ahT_dot (fun y : ℂ => if y.im < 0 then 0 else harmonicPlane S pS q y)
    (harmonicBiparameterCoefficient S pS q 0 t) F
  let V : ℂ → ℂ := fun y => ahVar β (F y)
  let U : ℂ → ℂ := fun y => cauchyT (fun w => β w / (w - b) ^ 2) (F y)
  let f := canonicalPassiveWeightedKernelInput S pS q z t
  let R := canonicalPassiveRegularKernelInput S pS q x t
  let G : ℂ → ℂ := fun y => F y - b
  have ha : a ∈ lowerHalf := by
    change a.im < 0
    simpa only [a, conj_im, UpperHalfPlane.coe_im] using neg_lt_zero.mpr z.im_pos
  have hFx : DifferentiableAt ℝ F (x : ℂ) :=
    (hC1 0 t (by simpa only [norm_zero] using hεS) htS).differentiableOn_one.differentiableAt
      ((isOpen_upperHalf.union isOpen_lowerHalf).mem_nhds (Or.inl x.im_pos))
  have hFa : DifferentiableAt ℝ F a :=
    (hC1 0 t (by simpa only [norm_zero] using hεS) htS).differentiableOn_one.differentiableAt
      ((isOpen_upperHalf.union isOpen_lowerHalf).mem_nhds (Or.inr ha))
  have hGx : DifferentiableAt ℝ G (x : ℂ) := hFx.sub_const b
  have hne : F x - b ≠ 0 :=
    norm_pos_iff.mp (hd₀.trans_le (hgap t htG x x.im_pos))
  have hu := hUdata t htU
  change Integrable (fun y : ℂ => f y * R y) volume ∧
    DifferentiableAt ℝ U (x : ℂ) ∧
    dz U x = hilbertHSmooth f x - (1 / Real.pi : ℂ) * ∫ y : ℂ, f y * R y at hu
  obtain ⟨hRi, hUDiff, hUDz⟩ := hu
  obtain ⟨d, hd, hquot⟩ := hnormalized t htN
  have hVa : V a = ahVar β b := rfl
  have hrep (y : ℂ) : V y = V a + G y * d + G y ^ 2 * U y := by
    by_cases hy : F y = b
    · calc
        V y = V a := by change ahVar β (F y) = ahVar β b; rw [hy]
        _ = _ := by
          simp only [G, hy, sub_self, zero_mul, zero_pow two_ne_zero, add_zero]
    · have he := (div_eq_iff (pow_ne_zero 2 (sub_ne_zero.mpr hy))).mp (hquot (F y) hy)
      change V y - ahVar β b - G y * d = U y * G y ^ 2 at he
      rw [← hVa] at he
      calc
        V y = (V y - V a - G y * d) + V a + G y * d := by ring
        _ = _ := by rw [he]; ring
  have hVDiff : DifferentiableAt ℝ V (x : ℂ) :=
    (((differentiableAt_const (V a)).add (hGx.mul_const d)).add
      ((hGx.pow 2).mul hUDiff)).congr_of_eventuallyEq (Eventually.of_forall hrep)
  have hVaDiff : DifferentiableAt ℝ V a := by
    simpa only [V, Function.comp_def] using
      (hd.differentiableAt.restrictScalars ℝ).comp a hFa
  have hVaDz : dz V a = d * dz F a := by
    calc
      dz V a = deriv (ahVar β) b * dz F a := (eq6_5 hFa hd.differentiableAt).1
      _ = _ := by rw [hd.deriv]
  have hGDz : dz G x = dz F x := by simp only [G, dz, fderiv_sub_const]
  have hG2Dz : dz (fun y : ℂ => G y ^ 2) x = 2 * G x * dz F x := by
    have heq : (fun y : ℂ => G y ^ 2) = fun y => G y * G y := by funext y; ring
    rw [heq, dz_mul hGx hGx, hGDz]
    ring
  have hCd : dz (fun _ : ℂ => d) x = 0 := by simp only [dz, fderiv_const_apply, zero_apply]; ring
  have hCv : dz (fun _ : ℂ => V a) x = 0 := by simp only [dz, fderiv_const_apply, zero_apply]; ring
  have hPoly : dz V x = dz F x * d + 2 * G x * dz F x * U x + G x ^ 2 * dz U x := by
    have heq : V = fun y : ℂ => V a + G y * d + G y ^ 2 * U y := funext hrep
    rw [heq, dz_add_at (f := fun y : ℂ => V a + G y * d)
      (g := fun y : ℂ => G y ^ 2 * U y)
      ((differentiableAt_const (V a)).add (hGx.mul_const d)) ((hGx.pow 2).mul hUDiff),
      dz_add_at (f := fun _ : ℂ => V a) (g := fun y : ℂ => G y * d)
        (differentiableAt_const (V a)) (hGx.mul_const d),
      dz_mul (u := G) (v := fun _ : ℂ => d) hGx (differentiableAt_const d),
      dz_mul (u := fun y : ℂ => G y ^ 2) (v := U) (hGx.pow 2) hUDiff,
      hCd, hCv, hGDz, hG2Dz]
    ring
  have hJx := hjet t htJ (x : ℂ) (Or.inl x.im_pos) hVDiff
  have hJa := hjet t htJ a (Or.inr ha) hVaDiff
  have hPx := hpoint t htV (x : ℂ)
  have hPa := hpoint t htV a
  have hK := (hJx.fun_mul hJa).fun_div ((hPx.fun_sub hPa).pow 2) (pow_ne_zero 2 hne)
  refine ⟨hRi, (hradial t htT x).2.2.2, hK.congr_deriv ?_⟩
  norm_num only [Pi.pow_apply, pow_one]
  change ((dz V x * dz F a + dz F x * dz V a) * (F x - b) ^ 2 -
      dz F x * dz F a * (2 * (F x - b) * (V x - V a))) / ((F x - b) ^ 2) ^ 2 =
    dz F a * (hilbertHSmooth f x - (1 / Real.pi : ℂ) * ∫ y : ℂ, f y * R y)
  rw [← hUDz, hVaDz, hPoly, hrep (x : ℂ)]
  dsimp only [G]
  field_simp [hne]
  ring

open WeilPetersson

end Kernel

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
