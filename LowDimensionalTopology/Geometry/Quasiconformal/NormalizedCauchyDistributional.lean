/-
Released under Apache 2.0 license as described in the file LICENSE.
The smooth compact approximants and their Hilbert-transform convergence are due
to Wu Xiaobin, Li-Zhong-QC-formalization commit
1c0d5473c020b66ed5106331a38a61536760b9b2. The fixed source retains attribution.
-/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.NormalizedCauchyLp
public import LowDimensionalTopology.Geometry.Quasiconformal.QuasiconformalWeakDerivatives
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Distributional derivatives of the actual normalized Cauchy potential

Actual smooth compact approximants converge in Lp. The normalized potentials
converge locally uniformly by their common difference-kernel bound, and the
smooth Hilbert transforms converge in Lp to the actual Hilbert transform.
Integration by parts against genuine compact smooth tests then passes to the
limit. No existence of generalized derivatives or test-function identity is
assumed in the final theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Subtraction of Lp inputs commutes with the actual normalized integral. -/
theorem normalizedCauchyPotential_sub_input {p : ℝ} (hp : 2 < p)
    {h g : ℂ → ℂ} (hh : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    (hg : MemLp g (ENNReal.ofReal p) (volume : Measure ℂ))
    (z : ℂ) :
    normalizedCauchyPotential (fun ζ => h ζ - g ζ) z =
      normalizedCauchyPotential h z - normalizedCauchyPotential g z := by
  have hi := normalizedCauchyPotential_integrand_integrable_of_memLp hp hh z
  have hj := normalizedCauchyPotential_integrand_integrable_of_memLp hp hg z
  unfold normalizedCauchyPotential
  have heq : (fun ζ => (h ζ - g ζ) * (1 / (ζ - z) - 1 / ζ)) =
      fun ζ => h ζ * (1 / (ζ - z) - 1 / ζ) - g ζ * (1 / (ζ - z) - 1 / ζ) := by
    funext ζ
    ring
  rw [heq, integral_sub hi hj, mul_sub]

private theorem normalizedCauchyPotential_dist_eq_sub_input
    {p : ℝ} (hp : 2 < p) {u v : ℂ → ℂ}
    (hu : MemLp u (ENNReal.ofReal p) (volume : Measure ℂ))
    (hv : MemLp v (ENNReal.ofReal p) (volume : Measure ℂ)) (z : ℂ) :
    dist (normalizedCauchyPotential v z) (normalizedCauchyPotential u z) =
      ‖normalizedCauchyPotential (fun ζ => u ζ - v ζ) z‖ := by
  calc dist (normalizedCauchyPotential v z) (normalizedCauchyPotential u z)
      = ‖normalizedCauchyPotential u z - normalizedCauchyPotential v z‖ := by
        rw [dist_comm, dist_eq_norm]
    _ = ‖normalizedCauchyPotential (fun ζ => u ζ - v ζ) z‖ :=
      congrArg norm (normalizedCauchyPotential_sub_input hp hu hv z).symm

private theorem normalizedCauchyPotential_uniform_bound_on_ball
    {p : ℝ} (hp : 2 < p) {R : ℝ} (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℂ → ℂ, MemLp u (ENNReal.ofReal p) (volume : Measure ℂ) →
      ∀ z : ℂ, ‖z‖ ≤ R → ‖normalizedCauchyPotential u z‖ ≤
        B * (eLpNorm u (ENNReal.ofReal p) (volume : Measure ℂ)).toReal := by
  obtain ⟨M, hM, hbound⟩ := normalizedCauchyPotential_holder_bound hp
  have hα : 0 ≤ (p - 2) / p :=
    div_nonneg (sub_nonneg.mpr hp.le) (lt_trans zero_lt_two hp).le
  refine ⟨M * R ^ ((p - 2) / p), mul_nonneg hM (Real.rpow_nonneg hR _), ?_⟩
  intro u hu z hz
  have hsingle : ‖normalizedCauchyPotential u z‖ ≤
      M * (eLpNorm u (ENNReal.ofReal p) (volume : Measure ℂ)).toReal * ‖z‖ ^ ((p - 2) / p) := by
    simpa only [normalizedCauchyPotential_zero, sub_zero] using hbound u hu z 0
  calc ‖normalizedCauchyPotential u z‖
      ≤ M * (eLpNorm u (ENNReal.ofReal p) (volume : Measure ℂ)).toReal *
          ‖z‖ ^ ((p - 2) / p) := hsingle
    _ ≤ M * (eLpNorm u (ENNReal.ofReal p) (volume : Measure ℂ)).toReal * R ^ ((p - 2) / p) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg z) hz hα)
        (mul_nonneg hM ENNReal.toReal_nonneg)
    _ = (M * R ^ ((p - 2) / p)) * (eLpNorm u (ENNReal.ofReal p) (volume : Measure ℂ)).toReal :=
      mul_right_comm M (eLpNorm u (ENNReal.ofReal p) (volume : Measure ℂ)).toReal
        (R ^ ((p - 2) / p))

private theorem tendsto_eLpNorm_toReal_zero {p : ℝ≥0∞} {fn : ℕ → ℂ → ℂ}
    (hfn : ∀ n, MemLp (fn n) p (volume : Measure ℂ))
    (hconv : Tendsto (fun n => eLpNorm (fn n) p (volume : Measure ℂ)) atTop (𝓝 0)) :
    Tendsto (fun n => (eLpNorm (fn n) p (volume : Measure ℂ)).toReal) atTop (𝓝 0) :=
  (ENNReal.tendsto_toReal_zero_iff (fun n => (hfn n).eLpNorm_ne_top)).2 hconv

/-- Lp convergence of inputs gives locally uniform convergence of the genuine
normalized potentials, without any support hypothesis on the inputs. -/
theorem normalizedCauchyPotential_tendstoLocallyUniformly {p : ℝ} (hp : 2 < p)
    {hn : ℕ → ℂ → ℂ} {h : ℂ → ℂ} (hhn : ∀ n, MemLp (hn n) (ENNReal.ofReal p) (volume : Measure ℂ))
    (hh : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    (hconv : Tendsto (fun n => eLpNorm (fun z => hn n z - h z) (ENNReal.ofReal p)
      (volume : Measure ℂ))
      atTop (𝓝 0)) :
    TendstoLocallyUniformly (fun n => normalizedCauchyPotential (hn n))
      (normalizedCauchyPotential h) atTop := by
  have hsub (n : ℕ) := MemLp.ae_eq (f := hn n - h) (g := fun z => hn n z - h z)
    (Eventually.of_forall fun z => Pi.sub_apply (hn n) h z) ((hhn n).sub hh)
  have hnconv := tendsto_eLpNorm_toReal_zero hsub hconv
  apply (tendstoLocallyUniformly_iff_forall_isCompact
    (F := fun n => normalizedCauchyPotential (hn n))
    (f := normalizedCauchyPotential h) (p := atTop)).2
  intro K hK
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨B, -, hB⟩ := normalizedCauchyPotential_uniform_bound_on_ball hp hR.le
  have hlim : Tendsto (fun n => B *
      (eLpNorm (fun z => hn n z - h z) (ENNReal.ofReal p) (volume : Measure ℂ)).toReal)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hnconv.const_mul B
  apply (Metric.tendstoUniformlyOn_iff
    (F := fun n => normalizedCauchyPotential (hn n))
    (f := normalizedCauchyPotential h) (p := atTop) (s := K)).2
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hnε
  intro z hz
  calc dist (normalizedCauchyPotential h z) (normalizedCauchyPotential (hn n) z)
      = ‖normalizedCauchyPotential (fun w => hn n w - h w) z‖ :=
        normalizedCauchyPotential_dist_eq_sub_input hp (hhn n) hh z
    _ ≤ B * (eLpNorm (fun w => hn n w - h w) (ENNReal.ofReal p) (volume : Measure ℂ)).toReal :=
      hB (fun w => hn n w - h w) (hsub n) z (hKR z hz)
    _ < ε := hnε

private theorem memLp_two_restrict_compact {p : ℝ} (hp : 2 < p)
    {h : ℂ → ℂ} (hh : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    {K : Set ℂ} (hK : IsCompact K) :
    MemLp h 2 (volume.restrict K) := by
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  apply (hh.restrict K).mono_exponent
  simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp.le

private theorem tendsto_eLpNorm_two_restrict_compact {p : ℝ} (hp : 2 < p)
    {hn : ℕ → ℂ → ℂ} (hhn : ∀ n, MemLp (hn n) (ENNReal.ofReal p) (volume : Measure ℂ))
    (hconv : Tendsto (fun n => eLpNorm (hn n) (ENNReal.ofReal p) (volume : Measure ℂ)) atTop (𝓝 0))
    {K : Set ℂ} (hK : IsCompact K) :
    Tendsto (fun n => eLpNorm (hn n) 2 (volume.restrict K)) atTop (𝓝 0) := by
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hpq : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp.le
  have hr : 0 ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (by linarith : 0 ≤ p)]
    have hp0 : 0 < p := by linarith
    rw [sub_nonneg, div_le_div_iff₀ hp0 (by norm_num : (0 : ℝ) < 2)]
    linarith
  let B : ℝ≥0∞ := (volume.restrict K) univ ^
    (1 / (2 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal)
  have hB : B ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr (measure_ne_top _ _)
  have hlim : Tendsto (fun n => eLpNorm (hn n) (ENNReal.ofReal p) (volume : Measure ℂ) * B)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hconv (Or.inr hB)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) (fun n => ?_)
  exact (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq
    (hhn n).aestronglyMeasurable.restrict).trans
      (mul_le_mul' (eLpNorm_mono_measure (hn n) Measure.restrict_le_self) le_rfl)

private theorem integral_mul_tendsto_uniform_compact
    {fn : ℕ → ℂ → ℂ} {f b : ℂ → ℂ} (hfn : ∀ n, Continuous (fn n))
    (hf : Continuous f) (hb : Continuous b) (hbc : HasCompactSupport b)
    (hconv : TendstoLocallyUniformly fn f atTop) :
    Tendsto (fun n => ∫ z, fn n z * b z) atTop (𝓝 (∫ z, f z * b z)) := by
  let K := tsupport b
  have hK : IsCompact K := hbc.isCompact
  have hrestrict (a : ℂ → ℂ) : (∫ z in K, a z * b z) = ∫ z, a z * b z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have hlim := LiZhongQC.sp_tendsto_integral_mul_of_uniform
    (hb.continuousOn.integrableOn_compact hK)
    (fun n => ((hfn n).mul hb).continuousOn.integrableOn_compact hK)
    ((hf.mul hb).continuousOn.integrableOn_compact hK)
    ((tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) K hK)
  simpa only [hrestrict] using hlim

private theorem integral_mul_tendsto_Lp_compact {p : ℝ} (hp : 2 < p)
    {gn : ℕ → ℂ → ℂ} {g b : ℂ → ℂ} (hgn : ∀ n, MemLp (gn n) (ENNReal.ofReal p) (volume : Measure ℂ))
    (hg : MemLp g (ENNReal.ofReal p) (volume : Measure ℂ))
    (hb : Continuous b) (hbc : HasCompactSupport b)
    (hconv : Tendsto (fun n => eLpNorm (fun z => gn n z - g z) (ENNReal.ofReal p)
      (volume : Measure ℂ))
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, b z * gn n z) atTop (𝓝 (∫ z, b z * g z)) := by
  let K := tsupport b
  have hK : IsCompact K := hbc.isCompact
  have hrestrict (a : ℂ → ℂ) : (∫ z in K, a z * b z) = ∫ z, a z * b z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have hlim := LiZhongQC.sp_tendsto_integral_mul_of_L2
    (fun n => memLp_two_restrict_compact hp (hgn n) hK)
    (memLp_two_restrict_compact hp hg hK)
    ((hb.memLp_of_hasCompactSupport (μ := volume) hbc).restrict K)
    (tendsto_eLpNorm_two_restrict_compact hp (fun n => (hgn n).sub hg) hconv hK)
  simpa only [hrestrict, mul_comm] using hlim

private theorem continuous_c1_direction {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) (e : ℂ) :
    Continuous (fun z => fderiv ℝ f z e) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

private theorem integral_mul_half_combination {u f g : ℂ → ℂ}
    (hf : Integrable (fun z => u z * f z)) (hg : Integrable (fun z => u z * g z)) (a : ℂ) :
    (∫ z, u z * ((f z + a * g z) / 2)) =
      ((∫ z, u z * f z) + a * ∫ z, u z * g z) / 2 := by
  have heq : (fun z => u z * ((f z + a * g z) / 2)) =
      fun z => (u z * f z + a * (u z * g z)) / 2 := by funext z; ring
  rw [heq, integral_div, integral_add hf (hg.const_mul a), integral_const_mul]

private theorem c1_wirtinger_ibp {f ψ : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ z, f z * LiZhongQC.dz ψ z) = -∫ z, ψ z * LiZhongQC.dz f z ∧
      (∫ z, f z * LiZhongQC.dzbar ψ z) = -∫ z, ψ z * LiZhongQC.dzbar f z := by
  have hleft (e : ℂ) : Integrable (fun z => f z * fderiv ℝ ψ z e) :=
    (hf.continuous.mul (continuous_c1_direction hψ e)).integrable_of_hasCompactSupport
      (LiZhongQC.sp_hasCompactSupport_fderiv hcψ e).mul_left
  have hright (e : ℂ) : Integrable (fun z => ψ z * fderiv ℝ f z e) :=
    (hψ.continuous.mul (continuous_c1_direction hf e)).integrable_of_hasCompactSupport
      hcψ.mul_right
  have hprod : Integrable (fun z => f z * ψ z) :=
    (hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hcψ.mul_left
  have hdir (e : ℂ) : (∫ z, f z * fderiv ℝ ψ z e) = -∫ z, ψ z * fderiv ℝ f z e := by
    have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := f) (g := ψ) (v := e) (μ := volume)
      (by simpa only [mul_comm] using hright e) (hleft e) hprod
      (fun z _ => hf.differentiable (by norm_num) z)
      (fun z _ => hψ.differentiable (by norm_num) z)
    simpa only [mul_comm] using he
  have h (a : ℂ) :
      (∫ z, f z * ((fderiv ℝ ψ z 1 + a * fderiv ℝ ψ z I) / 2)) =
        -∫ z, ψ z * ((fderiv ℝ f z 1 + a * fderiv ℝ f z I) / 2) := by
    rw [integral_mul_half_combination (hleft 1) (hleft I), hdir 1, hdir I,
      integral_mul_half_combination (hright 1) (hright I)]
    ring
  refine ⟨?_, h I⟩
  simpa only [LiZhongQC.dz, neg_mul, sub_eq_add_neg] using h (-I)

/-- Integration by parts for both ordinary Wirtinger derivatives of any actual
C1 function against a C1 compactly supported complex test. -/
theorem c1_wirtinger_integral_by_parts {f ψ : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    (∫ z, f z * LiZhongQC.dz ψ z) = -∫ z, ψ z * LiZhongQC.dz f z ∧
      (∫ z, f z * LiZhongQC.dzbar ψ z) = -∫ z, ψ z * LiZhongQC.dzbar f z :=
  c1_wirtinger_ibp hf hψ hcψ

/-- Every actual planar Lp input with p greater than two has normalized Cauchy
potential with genuine distributional derivatives Th and h. -/
theorem normalizedCauchyPotential_distributional {p : ℝ} (hp : 2 < p)
    {h : ℂ → ℂ} (hh : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ)) :
    HasDistributionalWirtingerDerivatives (normalizedCauchyPotential h)
      (LiZhongQC.hilbertH h) h univ := by
  have hp1 : 1 < p := by linarith
  have hp1e : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp1.le
  let η : ℕ → ℂ → ℂ := LiZhongQC.hilbertHApprox h
  let F : ℕ → ℂ → ℂ := fun n => normalizedCauchyPotential (η n)
  have hηC : ∀ n, ContDiff ℝ ∞ (η n) :=
    fun n => LiZhongQC.hilbertHApprox_contDiff hp1.le hh n
  have hηS : ∀ n, HasCompactSupport (η n) :=
    fun n => LiZhongQC.hilbertHApprox_hasCompactSupport h n
  have hηLp : ∀ n, MemLp (η n) (ENNReal.ofReal p) (volume : Measure ℂ) :=
    fun n => (hηC n).continuous.memLp_of_hasCompactSupport (μ := volume) (hηS n)
  have hηlim : Tendsto (fun n => eLpNorm (fun z => η n z - h z) (ENNReal.ofReal p)
      (volume : Measure ℂ))
      atTop (𝓝 0) := LiZhongQC.hilbertHApprox_tendsto hp1.le hh
  have hFC : ∀ n, ContDiff ℝ 1 (F n) :=
    fun n => normalizedCauchyPotential_contDiff ((hηC n).of_le (by simp)) (hηS n)
  have hFlim : TendstoLocallyUniformly F (normalizedCauchyPotential h) atTop :=
    normalizedCauchyPotential_tendstoLocallyUniformly hp hηLp hh hηlim
  have hPC : Continuous (normalizedCauchyPotential h) :=
    normalizedCauchyPotential_continuous_of_memLp hp hh
  obtain ⟨A, -, hA⟩ := LiZhongQC.zygmund_calderon hp1
  obtain ⟨hHLp, -, hHlim⟩ := LiZhongQC.hilbertH_tendsto_of_smooth_bound hp1 hA h hh
  have hHnLp : ∀ n, MemLp (LiZhongQC.hilbertHSmooth (η n)) (ENNReal.ofReal p)
      (volume : Measure ℂ) :=
    fun n => LiZhongQC.hilbertHSmooth_memLp (hηC n) (hηS n) hp1
  refine ⟨hPC.continuousOn.locallyIntegrableOn MeasurableSet.univ,
    (hHLp.locallyIntegrable hp1e).locallyIntegrableOn univ,
    (hh.locallyIntegrable hp1e).locallyIntegrableOn univ, ?_⟩
  intro ψ hψ hcψ _
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hd1 := continuous_c1_direction hψ1 1
  have hdI := continuous_c1_direction hψ1 I
  have hdC : Continuous (LiZhongQC.dz ψ) :=
    (hd1.sub (continuous_const.mul hdI)).div_const 2
  have hdbC : Continuous (LiZhongQC.dzbar ψ) :=
    (hd1.add (continuous_const.mul hdI)).div_const 2
  have hdS : HasCompactSupport (LiZhongQC.dz ψ) :=
    HasCompactSupport.intro hcψ.isCompact fun z hz => by
      simp only [LiZhongQC.dz, LiZhongQC.sp_fderiv_eq_zero_of_notMem_tsupport hz,
        mul_zero, sub_zero, zero_div]
  have hdbS : HasCompactSupport (LiZhongQC.dzbar ψ) :=
    HasCompactSupport.intro hcψ.isCompact fun z hz => by
      simp only [LiZhongQC.dzbar, LiZhongQC.sp_fderiv_eq_zero_of_notMem_tsupport hz,
        mul_zero, add_zero, zero_div]
  have hLz := integral_mul_tendsto_uniform_compact (fun n => (hFC n).continuous)
    hPC hdC hdS hFlim
  have hLb := integral_mul_tendsto_uniform_compact (fun n => (hFC n).continuous)
    hPC hdbC hdbS hFlim
  have hRz := integral_mul_tendsto_Lp_compact hp hHnLp hHLp hψ.continuous hcψ hHlim
  have hRb := integral_mul_tendsto_Lp_compact hp hηLp hh hψ.continuous hcψ hηlim
  have hEz : ∀ n, (∫ z, F n z * LiZhongQC.dz ψ z) =
      -∫ z, ψ z * LiZhongQC.hilbertHSmooth (η n) z := by
    intro n
    simpa only [F, normalizedCauchyPotential_dz (hηC n) (hηS n)] using
      (c1_wirtinger_ibp (hFC n) hψ1 hcψ).1
  have hEb : ∀ n, (∫ z, F n z * LiZhongQC.dzbar ψ z) = -∫ z, ψ z * η n z := by
    intro n
    simpa only [F, normalizedCauchyPotential_dzbar (hηC n) (hηS n)] using
      (c1_wirtinger_ibp (hFC n) hψ1 hcψ).2
  have hz : (∫ z, normalizedCauchyPotential h z * LiZhongQC.dz ψ z) =
      -∫ z, ψ z * LiZhongQC.hilbertH h z :=
    tendsto_nhds_unique hLz (hRz.neg.congr fun n => (hEz n).symm)
  have hb : (∫ z, normalizedCauchyPotential h z * LiZhongQC.dzbar ψ z) = -∫ z, ψ z * h z :=
    tendsto_nhds_unique hLb (hRb.neg.congr fun n => (hEb n).symm)
  simpa only [Measure.restrict_univ] using And.intro hz hb

end LowDimensionalTopology.Geometry.Quasiconformal
