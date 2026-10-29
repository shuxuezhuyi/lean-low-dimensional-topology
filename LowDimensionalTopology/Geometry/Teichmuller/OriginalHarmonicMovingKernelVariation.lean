module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonInnerPrincipalValue
public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalHarmonicFirstJets
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The actual moving Cauchy kernel and its principal-value derivative

The normalized first variation has a divided difference whose lower-point
derivative is an ordinary weighted Cauchy transform. The upper-point
derivative is taken through a local smooth cutoff and its separated tail.
The singular square kernel is retained as its actual radial principal value.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory Topology Metric
open scoped ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC

private theorem normalized_resolvent_identity {z a w : ℂ}
    (hza : z ≠ a) (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (hwz : w ≠ z) (hwa : w ≠ a) :
    (ahKer z w - ahKer a w - (z - a) *
        (1 / (w - a) ^ 2 - 1 / (w * (w - 1)))) / (z - a) ^ 2 =
      1 / ((w - a) ^ 2 * (w - z)) := by
  unfold ahKer
  field_simp [sub_ne_zero.mpr hza, sub_ne_zero.mpr hw1,
    sub_ne_zero.mpr hwz, sub_ne_zero.mpr hwa, hw0]
  ring

private theorem normalized_resolvent_integral
    {μ : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hμ : IsBeltramiCoeff μ upperHalf M)
    {a : ℂ} (ha : a ∈ lowerHalf) {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun w : ℂ => μ w / ((w - a) ^ 2 * (w - z))) upperHalf ∧
      -(1 / Real.pi : ℂ) *
          (∫ w : ℂ in upperHalf, μ w / ((w - a) ^ 2 * (w - z))) =
        (normalizedCauchyTOn upperHalf μ z - normalizedCauchyTOn upperHalf μ a -
          (z - a) * deriv (normalizedCauchyTOn upperHalf μ) a) / (z - a) ^ 2 := by
  have hza : z ≠ a := by
    intro h
    have hz' : 0 ≤ z.im := hz
    have ha' : a.im < 0 := ha
    rw [h] at hz'
    linarith
  let A : ℂ → ℂ := fun w => μ w * ahKer z w
  let B : ℂ → ℂ := fun w => μ w * ahKer a w
  let C : ℂ → ℂ := fun w => μ w *
    (1 / (w - a) ^ 2 - 1 / (w * (w - 1)))
  have hA : IntegrableOn A upperHalf :=
    (ah_ker_integrable z).integrableOn.bdd_mul hμ.1 hμ.2
  have hB : IntegrableOn B upperHalf :=
    (ah_ker_integrable a).integrableOn.bdd_mul hμ.1 hμ.2
  have hC : IntegrableOn C upperHalf := (b36_p_hasDerivAt_N hM hμ.1 hμ.2 ha).1
  have he : (fun w : ℂ => (A w - B w - (z - a) * C w) / (z - a) ^ 2) =ᵐ[
      volume.restrict upperHalf] fun w => μ w / ((w - a) ^ 2 * (w - z)) := by
    filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet,
      ae_restrict_of_ae (volume.ae_ne z)] with w hw hwz
    have hw0 : w ≠ 0 := by
      intro h
      have hw' : 0 < w.im := hw
      rw [h, Complex.zero_im] at hw'
      exact lt_irrefl (0 : ℝ) hw'
    have hw1 : w ≠ 1 := by
      intro h
      have hw' : 0 < w.im := hw
      rw [h, Complex.one_im] at hw'
      exact lt_irrefl 0 hw'
    have hwa : w ≠ a := by
      intro h
      have hw' : 0 < w.im := hw
      have ha' : a.im < 0 := ha
      rw [h] at hw'
      linarith
    have hrat := normalized_resolvent_identity hza hw0 hw1 hwz hwa
    dsimp only [A, B, C]
    calc
      _ = μ w * ((ahKer z w - ahKer a w - (z - a) *
          (1 / (w - a) ^ 2 - 1 / (w * (w - 1)))) / (z - a) ^ 2) := by ring
      _ = _ := by rw [hrat]; ring
  have hweighted : IntegrableOn
      (fun w : ℂ => μ w / ((w - a) ^ 2 * (w - z))) upperHalf :=
    ((hA.sub hB).sub (hC.const_mul (z - a))).div_const ((z - a) ^ 2) |>.congr he
  refine ⟨hweighted, ?_⟩
  have hV : HasDerivAt (normalizedCauchyTOn upperHalf μ)
      (-(1 / Real.pi : ℂ) * ∫ w : ℂ in upperHalf, C w) a := by
    rw [b36_p_normalizedCauchyT_eq]
    exact ((b36_p_hasDerivAt_N hM hμ.1 hμ.2 ha).2).const_mul (-(1 / Real.pi : ℂ))
  rw [hV.deriv]
  simp only [b36_p_normalizedCauchyT_eq]
  rw [← integral_congr_ae he, integral_div]
  have hAB : IntegrableOn (fun w : ℂ => A w - B w) upperHalf := hA.sub' hB
  rw [integral_sub hAB (hC.const_mul (z - a)), integral_sub hA hB,
    integral_const_mul]
  dsimp only [A, B, C]
  ring

private theorem cauchy_tail_hasDerivAt
    {d : ℂ → ℂ} (hm : AEStronglyMeasurable d (volume : Measure ℂ))
    {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hzero : ∀ w : ℂ, ‖w - z‖ ≤ 2 * r → d w = 0)
    (hvalue : Integrable (fun w : ℂ => d w / (w - z)) volume)
    (hsquare : Integrable (fun w : ℂ => d w / (w - z) ^ 2) volume) :
    HasDerivAt (cauchyT d)
      (-(1 / Real.pi : ℂ) * ∫ w : ℂ, d w / (w - z) ^ 2) z := by
  have hsep (w b : ℂ) (hw : d w ≠ 0) (hb : b ∈ ball z r) :
      0 < ‖w - b‖ ∧ ‖w - z‖ ≤ 2 * ‖w - b‖ := by
    have hwfar : 2 * r < ‖w - z‖ := by
      by_contra h
      exact hw (hzero w (le_of_not_gt h))
    have hbnear : ‖b - z‖ < r := by simpa only [mem_ball, dist_eq_norm] using hb
    have htri : ‖w - z‖ ≤ ‖w - b‖ + ‖b - z‖ := norm_sub_le_norm_sub_add_norm_sub w b z
    constructor <;> linarith
  have hd (w b : ℂ) (hb : b ∈ ball z r) :
      HasDerivAt (fun a : ℂ => d w / (w - a)) (d w / (w - b) ^ 2) b := by
    by_cases hw : d w = 0
    · simpa only [hw, zero_div] using (hasDerivAt_const b (0 : ℂ))
    · have hne : w - b ≠ 0 := norm_pos_iff.mp (hsep w b hw hb).1
      convert (((hasDerivAt_id b).const_sub w).inv hne).const_mul (d w) using 1 <;>
        simp only [neg_neg, div_eq_mul_inv, one_mul, Pi.inv_apply, id_eq]
  have hbound (w b : ℂ) (hb : b ∈ ball z r) :
      ‖d w / (w - b) ^ 2‖ ≤ 4 * ‖d w / (w - z) ^ 2‖ := by
    by_cases hw : d w = 0
    · simp only [hw, zero_div, norm_zero, mul_zero, le_refl]
    · obtain ⟨hpos, hdist⟩ := hsep w b hw hb
      have hzpos : 0 < ‖w - z‖ := by
        by_contra h
        apply hw
        exact hzero w (le_trans (le_of_not_gt h) (by positivity))
      have hsq : ‖w - z‖ ^ 2 ≤ 4 * ‖w - b‖ ^ 2 := by nlinarith [norm_nonneg (w - z)]
      simp only [norm_div, norm_pow]
      calc
        ‖d w‖ / ‖w - b‖ ^ 2 ≤ ‖d w‖ / (‖w - z‖ ^ 2 / 4) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by linarith [hsq])
        _ = 4 * (‖d w‖ / ‖w - z‖ ^ 2) := by
          rw [div_div_eq_mul_div]
          ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℂ))
    (F := fun b w : ℂ => d w / (w - b))
    (F' := fun b w : ℂ => d w / (w - b) ^ 2)
    (bound := fun w : ℂ => 4 * ‖d w / (w - z) ^ 2‖)
    (ball_mem_nhds z hr)
    (Eventually.of_forall fun b => hm.div₀
      (by fun_prop : Measurable fun w : ℂ => w - b).aestronglyMeasurable)
    hvalue
    (hm.div₀ (by fun_prop : Measurable fun w : ℂ => (w - z) ^ 2).aestronglyMeasurable)
    (Eventually.of_forall fun w b hb => hbound w b hb)
    (hsquare.norm.const_mul 4)
    (Eventually.of_forall fun w b hb => hd w b hb)
  unfold cauchyT
  exact h.2.const_mul (-(1 / Real.pi : ℂ))

private theorem localized_cauchy_dz
    (f : ℂ → ℂ) (hLp : MemLp f 2 (volume : Measure ℂ))
    (hC1 : ContDiffOn ℝ 1 f upperHalf)
    (hvalue : ∀ z ∈ upperHalf, Integrable (fun w : ℂ => f w / (w - z)) volume)
    (ξ : ℍ) :
    DifferentiableAt ℝ (cauchyT f) (ξ : ℂ) ∧
      dz (cauchyT f) ξ = hilbertHSmooth f ξ := by
  let b : ContDiffBump (ξ : ℂ) :=
    ⟨ξ.im / 4, ξ.im / 2, by positivity, by linarith [ξ.im_pos]⟩
  let ψ : ℂ → ℂ := fun w => (b w : ℂ) * f w
  have hsub : closedBall (ξ : ℂ) (ξ.im / 2) ⊆ upperHalf := by
    intro w hw
    have hn : ‖w - ξ‖ ≤ ξ.im / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hi : ξ.im - w.im ≤ ‖w - ξ‖ := by
      calc
        ξ.im - w.im = -(w - ξ).im := by simp only [sub_im, UpperHalfPlane.coe_im]; ring
        _ ≤ |(w - ξ).im| := neg_le_abs _
        _ ≤ ‖w - ξ‖ := Complex.abs_im_le_norm _
    change 0 < w.im
    linarith [ξ.im_pos]
  have hb : ContDiff ℝ 1 (fun w : ℂ => (b w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hψ : ContDiff ℝ 1 ψ := by
    rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : w ∈ tsupport b
    · have hwU : w ∈ upperHalf := hsub (by simpa only [b.tsupport_eq] using hw)
      exact hb.contDiffAt.mul (hC1.contDiffAt (isOpen_upperHalf.mem_nhds hwU))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (b : ℂ → ℝ)).isOpen_compl.mem_nhds hw] with w' hw'
      change (b w' : ℂ) * f w' = 0
      rw [image_eq_zero_of_notMem_tsupport hw', Complex.ofReal_zero, zero_mul]
  have hcψ : HasCompactSupport ψ :=
    (b.hasCompactSupport.comp_left (g := fun a : ℝ => (a : ℂ)) rfl).mul_right
  have hψLp : MemLp ψ 2 (volume : Measure ℂ) :=
    hψ.continuous.memLp_of_hasCompactSupport hcψ
  have hψvalue (z : ℂ) : Integrable (fun w : ℂ => ψ w / (w - z)) volume := by
    obtain ⟨S, hS⟩ := hcψ.isCompact.isBounded.subset_closedBall (0 : ℂ)
    apply integrable_cauchyT_kernel (p := 3) (by norm_num)
      (show 0 < max S 1 by positivity)
      (hψ.continuous.memLp_of_hasCompactSupport hcψ)
    intro w hw
    apply image_eq_zero_of_notMem_tsupport
    intro hws
    have hn := hS hws
    have hn' : ‖w‖ ≤ S := by simpa only [mem_closedBall, dist_zero_right] using hn
    exact not_lt_of_ge (hn'.trans (le_max_left _ _)) hw
  let d : ℂ → ℂ := f - ψ
  have hdLp : MemLp d 2 (volume : Measure ℂ) := hLp.sub hψLp
  have hzero (w : ℂ) (hw : ‖w - ξ‖ ≤ ξ.im / 4) : d w = 0 := by
    have hone := b.one_of_mem_closedBall (by simpa only [mem_closedBall, dist_eq_norm] using hw)
    simp only [d, Pi.sub_apply, ψ, hone, Complex.ofReal_one, one_mul, sub_self]
  have hdvalue (z : ℂ) (hz : z ∈ upperHalf) :
      Integrable (fun w : ℂ => d w / (w - z)) volume := by
    apply ((hvalue z hz).sub (hψvalue z)).congr
    exact Eventually.of_forall fun w => by dsimp only [d, Pi.sub_apply]; rw [sub_div]
  have hdsquare : Integrable (fun w : ℂ => d w / (w - ξ) ^ 2) volume := by
    have hi := integrableOn_truncated_kernel (p := 2) (by norm_num)
      (by simpa using hdLp) (ξ : ℂ) (by positivity : 0 < ξ.im / 4)
    apply hi.integrable_of_forall_notMem_eq_zero
    intro w hw
    rw [hzero w (le_of_not_gt hw), zero_div]
  have hd : HasDerivAt (cauchyT d)
      (-(1 / Real.pi : ℂ) * ∫ w : ℂ, d w / (w - ξ) ^ 2) (ξ : ℂ) := by
    apply cauchy_tail_hasDerivAt hdLp.aestronglyMeasurable (by positivity : 0 < ξ.im / 8)
      (fun w hw => hzero w (by linarith)) (hdvalue ξ ξ.im_pos) hdsquare
  have heq : cauchyT f =ᶠ[𝓝 (ξ : ℂ)] fun z => cauchyT ψ z + cauchyT d z := by
    filter_upwards [isOpen_upperHalf.mem_nhds ξ.im_pos] with z hz
    unfold cauchyT
    rw [← mul_add, ← integral_add (hψvalue z) (hdvalue z hz)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by dsimp only [d, Pi.sub_apply]; ring
  have hψdiff : DifferentiableAt ℝ (cauchyT ψ) (ξ : ℂ) :=
    (contDiff_cauchyT hψ hcψ).differentiable one_ne_zero _
  have hddiff : DifferentiableAt ℝ (cauchyT d) (ξ : ℂ) := hd.differentiableAt.restrictScalars ℝ
  refine ⟨(hψdiff.add hddiff).congr_of_eventuallyEq heq, ?_⟩
  have hdzsum : dz (cauchyT f) ξ = dz (cauchyT ψ) ξ + dz (cauchyT d) ξ := by
    have hfd := heq.fderiv_eq (𝕜 := ℝ)
    have hadd := (hψdiff.hasFDerivAt.add hddiff.hasFDerivAt).fderiv
    have hsumfun : cauchyT ψ + cauchyT d =
        (fun z : ℂ => cauchyT ψ z + cauchyT d z) := by
      funext z
      simp only [Pi.add_apply]
    rw [hsumfun] at hadd
    simp only [dz, hfd, hadd, add_apply]
    ring
  have hψlim := tendsto_truncated_cauchyT_dz hψ hcψ (ξ : ℂ)
  have hdlim : Tendsto
      (fun r : ℝ => -(1 / Real.pi : ℂ) *
        ∫ w in {w : ℂ | r < ‖w - ξ‖}, d w / (w - ξ) ^ 2)
      (𝓝[>] 0) (𝓝 (-(1 / Real.pi : ℂ) * ∫ w : ℂ, d w / (w - ξ) ^ 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by positivity : 0 < ξ.im / 4)] with r hr
    congr 1
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    rw [hzero w ((le_of_not_gt hw).trans hr.2.le), zero_div]
  have hlim : Tendsto
      (fun r : ℝ => -(1 / Real.pi : ℂ) *
        ∫ w in {w : ℂ | r < ‖w - ξ‖}, f w / (w - ξ) ^ 2)
      (𝓝[>] 0) (𝓝 (cauchyT (dz ψ) ξ +
        -(1 / Real.pi : ℂ) * ∫ w : ℂ, d w / (w - ξ) ^ 2)) := by
    apply (hψlim.add hdlim).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hψint := integrableOn_truncated_kernel (p := 2) (by norm_num)
      (by simpa using hψLp) (ξ : ℂ) hr
    have hdint := integrableOn_truncated_kernel (p := 2) (by norm_num)
      (by simpa using hdLp) (ξ : ℂ) hr
    rw [← mul_add, ← integral_add hψint hdint]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by dsimp only [d, Pi.sub_apply]; ring
  have hH : hilbertHSmooth f ξ = cauchyT (dz ψ) ξ +
      -(1 / Real.pi : ℂ) * ∫ w : ℂ, d w / (w - ξ) ^ 2 := hlim.limUnder_eq
  rw [hH, hdzsum, dz_cauchyT hψ hcψ,
    dz_eq_deriv hd.differentiableAt, hd.deriv]

open WeilPetersson QuadraticBergman

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

private theorem actual_weighted_cauchy_representation
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) (ξ : ℂ) (hξ : 0 ≤ ξ.im) :
    let μ := harmonicPlane R p q
    let V := normalizedCauchyTOn upperHalf μ
    let f := SourceKernel.innerInput (NativeHarmonicBeltrami.coefficient R p q) z
    Integrable (fun w : ℂ => f w / (w - ξ)) volume ∧
      cauchyT f ξ =
        (V ξ - V (conj (z : ℂ)) -
          ((ξ : ℂ) - conj (z : ℂ)) * deriv V (conj (z : ℂ))) /
            ((ξ : ℂ) - conj (z : ℂ)) ^ 2 := by
  dsimp only
  let M : ℝ := ‖(NativeHarmonicBeltrami.ofQuadratic R p hp q).val‖
  have hM : 0 ≤ M := norm_nonneg _
  have hμ : IsBeltramiCoeff (harmonicPlane R p q) upperHalf M := by
    have hb := planeRepresentative_isBeltramiCoeff
      (NativeHarmonicBeltrami.ofQuadratic R p hp q).val
    have hae : planeRepresentative (NativeHarmonicBeltrami.ofQuadratic R p hp q).val =ᵐ[
        volume.restrict upperHalf] harmonicPlane R p q :=
      NativeHarmonicBeltrami.planeRepresentative_ofQuadratic_ae R p hp q
    refine ⟨hb.1.congr hae, ?_⟩
    filter_upwards [hae, hb.2] with w hw hbound
    rwa [← hw]
  have ha : conj (z : ℂ) ∈ lowerHalf := by
    change (conj (z : ℂ)).im < 0
    simpa only [conj_im, UpperHalfPlane.coe_im] using neg_lt_zero.mpr z.im_pos
  obtain ⟨hint, heq⟩ := normalized_resolvent_integral hM hμ ha hξ
  have hfun : (fun w : ℂ =>
      SourceKernel.innerInput (NativeHarmonicBeltrami.coefficient R p q) z w / (w - ξ)) =
      upperHalf.indicator (fun w : ℂ => harmonicPlane R p q w /
        ((w - conj (z : ℂ)) ^ 2 * (w - ξ))) := by
    funext w
    by_cases hw : 0 < w.im
    · have hcoeff : NativeHarmonicBeltrami.coefficient R p q ⟨w, hw⟩ =
          harmonicPlane R p q w :=
        (harmonicPlane_eq_coefficient R p q ⟨w, hw⟩).symm
      simp only [SourceKernel.innerInput, SourceKernel.upperExtension, hw, dite_true,
        indicator_of_mem (show w ∈ upperHalf from hw), SourceKernel.cauchySquare,
        hcoeff, div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    · simp only [SourceKernel.innerInput, SourceKernel.upperExtension, hw, dite_false,
        zero_div, indicator_of_notMem (show w ∉ upperHalf from hw)]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hint.integrable_indicator isOpen_upperHalf.measurableSet
  · unfold cauchyT
    rw [hfun, integral_indicator isOpen_upperHalf.measurableSet]
    exact heq

private theorem actual_inner_input_ae
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) :
    SourceKernel.innerInput
        (fun w : ℍ => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val w) z =ᵐ[volume]
      SourceKernel.innerInput (NativeHarmonicBeltrami.coefficient R p q) z := by
  let b : Ambient := (NativeHarmonicBeltrami.ofQuadratic R p hp q).val
  let f : ℂ → ℂ := SourceKernel.innerInput (NativeHarmonicBeltrami.coefficient R p q) z
  have hcoeff : (fun w : ℍ => b w) =ᵐ[flatArea] NativeHarmonicBeltrami.coefficient R p q :=
    ae_hyperbolic_iff.mp (NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp q)
  have hae : SourceKernel.innerInput (fun w : ℍ => b w) z =ᵐ[volume] f := by
    apply ae_of_ae_restrict_of_ae_restrict_compl upperHalf
    · rw [← map_flat_coe, UpperHalfPlane.measurableEmbedding_coe.ae_map_iff]
      filter_upwards [hcoeff] with w hw
      dsimp only [f, SourceKernel.innerInput, SourceKernel.upperExtension]
      simpa only [dite_eq_left w.coe_im_pos] using
        congrArg (fun v : ℂ => v * SourceKernel.cauchySquare w (conj (z : ℂ))) hw
    · apply ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet.compl
      intro w hw
      simp only [f, SourceKernel.innerInput, SourceKernel.upperExtension,
        show ¬0 < w.im from hw, dite_false]
  exact hae

private theorem actual_weighted_cauchy_dz
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z ξ : ℍ) :
    let f := SourceKernel.innerInput (NativeHarmonicBeltrami.coefficient R p q) z
    DifferentiableAt ℝ (cauchyT f) (ξ : ℂ) ∧
      dz (cauchyT f) ξ = hilbertHSmooth f ξ := by
  dsimp only
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let b : Ambient := (NativeHarmonicBeltrami.ofQuadratic R p hp q).val
  let f : ℂ → ℂ := SourceKernel.innerInput (NativeHarmonicBeltrami.coefficient R p q) z
  have hae := actual_inner_input_ae R p hp q z
  have hLp : MemLp f 2 (volume : Measure ℂ) :=
    (memLp_congr_ae hae).mp (SourceKernel.innerInput_memLp_two b z)
  have hQ : ContDiffOn ℝ 1 (uniformizedQuadratic R p q) upperHalf :=
    ((LiZhongQC.utm_liftQD_differentiableOn q.property hp).contDiffOn
      isOpen_upperHalf).restrict_scalars ℝ
  have him : ContDiff ℝ 1 (fun w : ℂ => (w.im : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff
  have hden : ContDiffOn ℝ 1 (fun w : ℂ => (w - conj (z : ℂ)) ^ 2) upperHalf :=
    (contDiff_id.sub contDiff_const).pow 2 |>.contDiffOn
  have hne (w : ℂ) (hw : w ∈ upperHalf) : (w - conj (z : ℂ)) ^ 2 ≠ 0 := by
    apply pow_ne_zero 2
    intro he
    have hi := congrArg Complex.im he
    simp only [sub_im, conj_im, zero_im, UpperHalfPlane.coe_im] at hi
    linarith [show 0 < w.im from hw, z.im_pos]
  have hnum : ContDiffOn ℝ 1 (fun w : ℂ =>
      (w.im : ℂ) ^ 2 * conj (uniformizedQuadratic R p q w)) upperHalf :=
    (him.pow 2).contDiffOn.mul (Complex.conjCLE.contDiff.comp_contDiffOn hQ)
  have hC1 : ContDiffOn ℝ 1 f upperHalf := by
    apply (hnum.mul (hden.fun_inv hne)).congr
    intro w hw
    dsimp only [f, SourceKernel.innerInput, SourceKernel.upperExtension]
    rw [dite_eq_left (show 0 < w.im from hw),
      NativeHarmonicBeltrami.coefficient_eq_uniformized]
    simp only [SourceKernel.cauchySquare, UpperHalfPlane.im, div_eq_mul_inv, one_mul]
  exact localized_cauchy_dz f hLp hC1 (fun w hw =>
    (actual_weighted_cauchy_representation R p hp q z w hw.le).1) ξ

/-- The actual chosen quadratic harmonic input has a genuine real
spatial derivative for its ordinary Cauchy transform, equal in the z slot
to the same radial principal-value Hilbert transform. -/
theorem harmonicInnerInput_cauchyT_dz
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z ξ : ℍ) :
    let f := SourceKernel.innerInput
      (fun w : ℍ => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val w) z
    Integrable (fun w : ℂ => f w / (w - ξ)) (volume : Measure ℂ) ∧
      DifferentiableAt ℝ (cauchyT f) (ξ : ℂ) ∧
        dz (cauchyT f) ξ = hilbertHSmooth f ξ := by
  dsimp only
  have hae := actual_inner_input_ae R p hp q z
  have hT := cauchyT_congr_ae hae
  have hH := hilbertHSmooth_congr_ae hae
  obtain ⟨hd, he⟩ := actual_weighted_cauchy_dz R p hp q z ξ
  have hi := (actual_weighted_cauchy_representation R p hp q z (ξ : ℂ) ξ.im_pos.le).1
  refine ⟨?_, ?_, ?_⟩
  · apply hi.congr
    filter_upwards [hae] with w hw
    rw [hw]
  · rw [hT]
    exact hd
  · rw [hT, hH]
    exact he

/-- At every real pole the same actual weighted input has an absolutely
integrable first Cauchy kernel, including the poles used by a real Mobius
change of variables. -/
theorem harmonicInnerInput_cauchy_boundary_integrable
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (z : ℍ) (r : ℝ) :
    Integrable (fun w : ℂ => SourceKernel.innerInput
      (fun η : ℍ => (NativeHarmonicBeltrami.ofQuadratic R p hp q).val η) z w / (w - r))
      (volume : Measure ℂ) := by
  have hae := actual_inner_input_ae R p hp q z
  have hi := (actual_weighted_cauchy_representation R p hp q z (r : ℂ)
    (by simp only [ofReal_im, le_refl])).1
  apply hi.congr
  filter_upwards [hae] with w hw
  rw [hw]

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
