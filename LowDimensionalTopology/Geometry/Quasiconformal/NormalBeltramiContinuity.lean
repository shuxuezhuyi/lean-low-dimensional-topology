/-
The actual fixed-point Lp stability and bounded-support Cauchy-transform
stability used below are due to Wu Xiaobin, Li-Zhong-QC-formalization,
fixed commit 1c0d5473c020b66ed5106331a38a61536760b9b2. The external source
and THIRD_PARTY_NOTICES.md retain the Apache-2.0 attribution.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiSolution
public import Mathlib.Tactic.Linarith

/-!
# Global stability of actual normal Beltrami solutions

Coefficients are actual L-infinity classes with a common bounded essential
support. Almost-everywhere convergence implies the same bound and essential
support for the limit. Indicator representatives are used only inside proofs.
The actual normal solutions converge uniformly on the whole plane, and
their genuine holomorphic weak derivatives converge in the original Lp.
The normalized potential remains the Cauchy transform minus its value at zero.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Metric MeasureTheory Filter Topology
open scoped ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

private theorem compactEssentialSupport_of_ae_bounded_support {μ : ℂ → ℂ} {R : ℝ}
    (hsupp : ∀ᵐ z ∂(volume : Measure ℂ), R < ‖z‖ → μ z = 0) :
    HasCompactEssentialSupport μ := by
  refine ⟨closedBall (0 : ℂ) R, isCompact_closedBall _ _, ?_⟩
  filter_upwards [hsupp] with z hz
  intro hzK
  apply hz
  simpa only [mem_closedBall_zero_iff, not_le] using hzK

private theorem bounded_support_indicator_ae {μ : ℂ → ℂ} {R : ℝ}
    (hsupp : ∀ᵐ z ∂(volume : Measure ℂ), R < ‖z‖ → μ z = 0) :
    (closedBall (0 : ℂ) R).indicator μ =ᵐ[volume] μ := by
  filter_upwards [hsupp] with z hz
  by_cases hzK : z ∈ closedBall (0 : ℂ) R
  · exact indicator_of_mem hzK μ
  · rw [indicator_of_notMem hzK, hz (by
      simpa only [mem_closedBall_zero_iff, not_le] using hzK)]

private theorem bounded_support_indicator_vanish (μ : ℂ → ℂ) (R : ℝ) (z : ℂ)
    (hz : R < ‖z‖) : (closedBall (0 : ℂ) R).indicator μ z = 0 :=
  indicator_of_notMem (by simpa only [mem_closedBall_zero_iff, not_le] using hz) μ

private theorem normalPotential_eq_cauchyT_sub_of_fixedPoint
    {μ ω : ℂ → ℂ} {p R : ℝ} (hp : 2 < p)
    (hω : MemLp ω (ENNReal.ofReal p) (volume : Measure ℂ))
    (hsupp : ∀ z, R < ‖z‖ → μ z = 0)
    (hfixed : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) :
    normalizedCauchyPotential ω = fun z => cauchyT ω z - cauchyT ω 0 := by
  let S : ℝ := max R 1
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsuppS : ∀ z, S < ‖z‖ → μ z = 0 :=
    fun z hz => hsupp z (lt_of_le_of_lt (le_max_left _ _) hz)
  let v : ℂ → ℂ := (closedBall (0 : ℂ) S).indicator ω
  have hae : ω =ᵐ[volume] v := t2_omega_ae_eq_indicator hsuppS hfixed
  have hv : MemLp v (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hω.indicator measurableSet_closedBall.nullMeasurableSet
  have hvzero : ∀ z, S < ‖z‖ → v z = 0 := bounded_support_indicator_vanish ω S
  rw [normalizedCauchyPotential_congr_ae hae, cauchyT_congr_ae hae]
  funext z
  have hiz := integrable_cauchyT_kernel hp hS hv hvzero z
  have hi0 := integrable_cauchyT_kernel hp hS hv hvzero 0
  have hint : (fun ζ => v ζ * (1 / (ζ - z) - 1 / ζ)) =
      fun ζ => v ζ / (ζ - z) - v ζ / (ζ - (0 : ℂ)) := by
    funext ζ
    simp only [mul_sub, mul_one_div, sub_zero]
  unfold normalizedCauchyPotential cauchyT
  rw [hint, integral_sub hiz hi0]
  ring

/-- For an actual Lp fixed point with bounded coefficient support, the
normalized potential is the actual Cauchy transform minus its value at zero. -/
theorem normalizedCauchyPotential_eq_cauchyT_sub_of_fixedPoint
    {μ ω : ℂ → ℂ} {p R : ℝ} (hp : 2 < p)
    (hω : MemLp ω (ENNReal.ofReal p) (volume : Measure ℂ))
    (hsupp : ∀ z, R < ‖z‖ → μ z = 0)
    (hfixed : ω =ᵐ[volume] fun z => μ z * hilbertH ω z + μ z) :
    normalizedCauchyPotential ω = fun z => cauchyT ω z - cauchyT ω 0 :=
  normalPotential_eq_cauchyT_sub_of_fixedPoint hp hω hsupp hfixed

private theorem weak_holomorphic_derivative_eq_of_normalPotential
    {f g h ω : ℂ → ℂ} {p : ℝ} (hp : 2 < p)
    (hω : MemLp ω (ENNReal.ofReal p) (volume : Measure ℂ))
    (hw : HasDistributionalWirtingerDerivatives f g h univ)
    (hrepr : f = fun z => z + normalizedCauchyPotential ω z) :
    g =ᵐ[volume] (fun z => 1 + hilbertH ω z) := by
  have hpot := normalizedCauchyPotential_distributional hp hω
  have hdiff : HasDistributionalWirtingerDerivatives
      (fun z => f z - normalizedCauchyPotential ω z)
      (fun z => g z - hilbertH ω z) (fun z => h z - ω z) univ := hw.sub_univ hpot
  have hidfun : (fun z => f z - normalizedCauchyPotential ω z) = fun z => z := by
    funext z
    rw [hrepr]
    dsimp only
    exact add_sub_cancel_right z _
  rw [hidfun] at hdiff
  have hid := c1_hasDistributionalWirtingerDerivatives_univ
    (f := fun z : ℂ => z) contDiff_id
  have hg := (distributionalWirtinger_derivatives_unique_univ hdiff hid).1
  filter_upwards [hg] with z hz
  have hidz : dz (fun z : ℂ => z) z = 1 := by
    rw [dz_eq_deriv (hasDerivAt_id' z).differentiableAt]
    exact (hasDerivAt_id' z).deriv
  exact sub_eq_iff_eq_add.mp (hz.trans hidz)

/-- Uniformly essentially bounded coefficients with one common bounded
essential support and an a.e. limit give globally uniform convergence of the
actual normal solutions and global Lp convergence of every actual holomorphic
weak derivative witness, at the same originally specified exponent. -/
theorem normalLpSolution_tendsto_of_ae_bounded_support
    {μn : ℕ → MeasurableBeltramiSpace} {μ : MeasurableBeltramiSpace}
    {fn gn hn : ℕ → ℂ → ℂ} {f g h : ℂ → ℂ} {k p R : ℝ}
    (hk : k ∈ Ico (0 : ℝ) 1) (hp : 2 < p)
    (hsmall : k * smoothHilbertNorm p < 1) (hμnk : ∀ n, ‖μn n‖ ≤ k)
    (hsuppn : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ), R < ‖z‖ → (μn n : ℂ → ℂ) z = 0)
    (hlim : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => (μn n : ℂ → ℂ) z) atTop (𝓝 ((μ : ℂ → ℂ) z)))
    (hfn : ∀ n, IsNormalLpSolution (μn n : ℂ → ℂ) (fn n) p)
    (hf : IsNormalLpSolution (μ : ℂ → ℂ) f p)
    (hwn : ∀ n, HasDistributionalWirtingerDerivatives (fn n) (gn n) (hn n) univ)
    (hw : HasDistributionalWirtingerDerivatives f g h univ) :
    TendstoUniformly fn f atTop ∧
      Tendsto (fun n => eLpNorm (fun z => gn n z - g z) (ENNReal.ofReal p) volume)
        atTop (𝓝 0) ∧
      Tendsto (fun n => (eLpNorm (fun z => gn n z - g z) (ENNReal.ofReal p) volume).toReal)
        atTop (𝓝 0) := by
  have hp1 : 1 < p := lt_trans one_lt_two hp
  have hkp : k * hilbertNorm p < 1 := by
    simpa only [smoothHilbertNorm_eq_hilbertNorm hp1] using hsmall
  have hμn : ∀ n, IsBeltramiCoeff (μn n : ℂ → ℂ) univ k := by
    intro n
    refine ⟨(MeasurableBeltramiSpace.isBeltramiCoeff (μn n)).1, ?_⟩
    filter_upwards [(MeasurableBeltramiSpace.isBeltramiCoeff (μn n)).2] with z hz
    exact hz.trans (hμnk n)
  have hboundAll : ∀ᵐ z ∂(volume : Measure ℂ), ∀ n, ‖(μn n : ℂ → ℂ) z‖ ≤ k := by
    apply ae_all_iff.mpr
    intro n
    simpa only [Measure.restrict_univ] using (hμn n).2
  have hμbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖(μ : ℂ → ℂ) z‖ ≤ k := by
    filter_upwards [hlim, hboundAll] with z hz hzn
    exact le_of_tendsto' hz.norm hzn
  have hμ : IsBeltramiCoeff (μ : ℂ → ℂ) univ k := by
    simpa only [IsBeltramiCoeff, Measure.restrict_univ] using
      And.intro (Lp.aestronglyMeasurable μ) hμbound
  have hsupp : ∀ᵐ z ∂(volume : Measure ℂ), R < ‖z‖ → (μ : ℂ → ℂ) z = 0 := by
    filter_upwards [hlim, ae_all_iff.mpr hsuppn] with z hz hzn
    intro hzR
    have hzero : (fun n => (μn n : ℂ → ℂ) z) = fun _ => (0 : ℂ) :=
      funext fun n => hzn n hzR
    have hz0 : Tendsto (fun n => (μn n : ℂ → ℂ) z) atTop (𝓝 (0 : ℂ)) := by
      rw [hzero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hz hz0
  have hμnLp : ∀ n, MemLp (μn n : ℂ → ℂ) (ENNReal.ofReal p) volume := fun n =>
    measurableBeltrami_memLp_of_compactEssentialSupport (μn n)
      (compactEssentialSupport_of_ae_bounded_support (hsuppn n)) _
  have hμLp : MemLp (μ : ℂ → ℂ) (ENNReal.ofReal p) volume :=
    measurableBeltrami_memLp_of_compactEssentialSupport μ
      (compactEssentialSupport_of_ae_bounded_support hsupp) _
  choose ωn hωn hfixedn hreprn using
    fun n => normalLpSolution_representation hp (hμn n) (hμnLp n) (hfn n)
  obtain ⟨ω, hω, hfixed, hrepr⟩ := normalLpSolution_representation hp hμ hμLp hf
  let νn : ℕ → ℂ → ℂ := fun n => (closedBall (0 : ℂ) R).indicator (μn n : ℂ → ℂ)
  let ν : ℂ → ℂ := (closedBall (0 : ℂ) R).indicator (μ : ℂ → ℂ)
  have hνn : ∀ n, νn n =ᵐ[volume] (μn n : ℂ → ℂ) :=
    fun n => bounded_support_indicator_ae (hsuppn n)
  have hν : ν =ᵐ[volume] (μ : ℂ → ℂ) := bounded_support_indicator_ae hsupp
  have hνnCoeff : ∀ n, IsBeltramiCoeff (νn n) univ k :=
    fun n => (planar_isBeltramiCoeff_congr_ae (hνn n)).mpr (hμn n)
  have hνCoeff : IsBeltramiCoeff ν univ k :=
    (planar_isBeltramiCoeff_congr_ae hν).mpr hμ
  have hνnSupp : ∀ n z, R < ‖z‖ → νn n z = 0 :=
    fun n => bounded_support_indicator_vanish (μn n : ℂ → ℂ) R
  have hνSupp : ∀ z, R < ‖z‖ → ν z = 0 :=
    bounded_support_indicator_vanish (μ : ℂ → ℂ) R
  have hνlim : ∀ᵐ z ∂(volume : Measure ℂ), Tendsto (fun n => νn n z) atTop (𝓝 (ν z)) := by
    filter_upwards [hlim] with z hz
    by_cases hzK : z ∈ closedBall (0 : ℂ) R
    · simpa only [νn, ν, indicator_of_mem hzK] using hz
    · simpa only [νn, ν, indicator_of_notMem hzK] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  have hνnFixed : ∀ n, ωn n =ᵐ[volume] fun z => νn n z * hilbertH (ωn n) z + νn n z := by
    intro n
    filter_upwards [hfixedn n, hνn n] with z hz hνz
    simpa only [hνz] using hz
  have hνFixed : ω =ᵐ[volume] fun z => ν z * hilbertH ω z + ν z := by
    filter_upwards [hfixed, hν] with z hz hνz
    simpa only [hνz] using hz
  have hstable := eq12_1_solution_tendsto hk.1 hp hkp hνnCoeff hνCoeff
    hνnSupp hνSupp hνlim hωn hνnFixed hω hνFixed
  have hTstable := eq12_1_solution_tendsto_cauchyT hk.1 hp hkp hνnCoeff hνCoeff
    hνnSupp hνSupp hνlim hωn hνnFixed hω hνFixed
  have hPn : ∀ n, normalizedCauchyPotential (ωn n) =
      fun z => cauchyT (ωn n) z - cauchyT (ωn n) 0 :=
    fun n => normalPotential_eq_cauchyT_sub_of_fixedPoint hp (hωn n) (hνnSupp n) (hνnFixed n)
  have hP : normalizedCauchyPotential ω = fun z => cauchyT ω z - cauchyT ω 0 :=
    normalPotential_eq_cauchyT_sub_of_fixedPoint hp hω hνSupp hνFixed
  have huniform : TendstoUniformly fn f atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp hTstable) (ε / 2) (half_pos hε)] with n hn
    intro z
    have heq : fn n z - f z =
        (cauchyT (ωn n) z - cauchyT ω z) - (cauchyT (ωn n) 0 - cauchyT ω 0) := by
      rw [hreprn n, hrepr, hPn n, hP]
      dsimp only
      ring
    have hz := hn z
    have h0 := hn 0
    rw [dist_eq_norm, norm_sub_rev] at hz h0 ⊢
    rw [heq]
    exact lt_of_le_of_lt (norm_sub_le _ _) (by linarith)
  have hgn : ∀ n, gn n =ᵐ[volume] (fun z => 1 + hilbertH (ωn n) z) :=
    fun n => weak_holomorphic_derivative_eq_of_normalPotential hp (hωn n) (hwn n) (hreprn n)
  have hg : g =ᵐ[volume] (fun z => 1 + hilbertH ω z) :=
    weak_holomorphic_derivative_eq_of_normalPotential hp hω hw hrepr
  obtain ⟨A, -, hA⟩ := zygmund_calderon hp1
  have hnormBound (n : ℕ) : eLpNorm (fun z => gn n z - g z) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (smoothHilbertNorm p) * eLpNorm (ωn n - ω) (ENNReal.ofReal p) volume := by
    have hHsub := hilbertH_sub_ae_of_smooth_bound hp1 hA (hωn n) hω
    have hfun : (fun z => ωn n z - ω z) = ωn n - ω := by
      funext z
      exact (Pi.sub_apply (ωn n) ω z).symm
    rw [hfun] at hHsub
    have hae : (fun z => gn n z - g z) =ᵐ[volume] hilbertH (ωn n - ω) := by
      filter_upwards [hgn n, hg, hHsub] with z hgnz hgz hHz
      rw [hgnz, hgz, hHz]
      ring
    rw [eLpNorm_congr_ae hae, smoothHilbertNorm_eq_hilbertNorm hp1]
    exact eq11_16_eLpNorm hp1 ((hωn n).sub hω)
  have hupper : Tendsto (fun n => ENNReal.ofReal (smoothHilbertNorm p) *
      eLpNorm (ωn n - ω) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hstable (Or.inr ENNReal.ofReal_ne_top)
  have hderivative : Tendsto
      (fun n => eLpNorm (fun z => gn n z - g z) (ENNReal.ofReal p) volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall hnormBound)
  refine ⟨huniform, hderivative, ?_⟩
  have hreal := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hderivative
  simpa only [Function.comp_def, ENNReal.toReal_zero] using hreal

end LowDimensionalTopology.Geometry.Quasiconformal
