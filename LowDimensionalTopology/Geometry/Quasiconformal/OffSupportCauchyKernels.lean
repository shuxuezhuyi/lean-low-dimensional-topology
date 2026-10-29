/-
The separation and decay estimates adapt Wu Xiaobin's Li-Zhong-QC-formalization,
commit 1c0d5473c020b66ed5106331a38a61536760b9b2, under Apache 2.0.
They replace half-plane geometry by an explicit distance-separation hypothesis.
-/
module
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory Filter Topology
namespace LowDimensionalTopology.Geometry.Quasiconformal.OffSupportCauchy

/-- Distance separation alone gives a uniform integrable-profile comparison. -/
theorem separation_profile {ζ w : ℂ} {δ R : ℝ} (hδ : 0 < δ)
    (hsep : δ ≤ ‖ζ - w‖) (hwR : ‖w‖ ≤ R) :
    δ * (1 + ‖ζ‖) ≤ (1 + R + δ) * ‖ζ - w‖ := by
  have h2 : ‖ζ‖ - ‖w‖ ≤ ‖ζ - w‖ := norm_sub_norm_le ζ w
  have e1 : δ * ‖ζ‖ ≤ δ * (‖ζ - w‖ + R) :=
    mul_le_mul_of_nonneg_left (by linarith) hδ.le
  have e2 : δ * (1 + R) ≤ ‖ζ - w‖ * (1 + R) :=
    mul_le_mul_of_nonneg_right hsep (by linarith [(norm_nonneg w).trans hwR])
  nlinarith

/-- The inverse kernel is bounded by a translate-independent decay profile. -/
theorem inverse_le_profile {ζ w : ℂ} {δ R : ℝ} (hδ : 0 < δ)
    (hsep : δ ≤ ‖ζ - w‖) (hwR : ‖w‖ ≤ R) :
    ‖(ζ - w)⁻¹‖ ≤ (1 + R + δ) / δ * (1 + ‖ζ‖)⁻¹ := by
  have hs := separation_profile hδ hsep hwR
  have hpos : 0 < ‖ζ - w‖ := hδ.trans_le hsep
  have hs1 : 0 < 1 + ‖ζ‖ := by positivity
  have key : (1 + ‖ζ‖) * ‖ζ - w‖⁻¹ ≤ (1 + R + δ) / δ := by
    rw [← div_eq_mul_inv, div_le_div_iff₀ hpos hδ]
    linarith
  rw [norm_inv]
  calc ‖ζ - w‖⁻¹ = (1 + ‖ζ‖)⁻¹ * ((1 + ‖ζ‖) * ‖ζ - w‖⁻¹) := by field_simp
    _ ≤ (1 + ‖ζ‖)⁻¹ * ((1 + R + δ) / δ) := by gcongr
    _ = _ := by ring

/-- The inverse cube has cubic decay under the same explicit separation. -/
theorem inverse_cube_le_profile {ζ w : ℂ} {δ R : ℝ} (hδ : 0 < δ)
    (hsep : δ ≤ ‖ζ - w‖) (hwR : ‖w‖ ≤ R) :
    ‖((ζ - w) ^ 3)⁻¹‖ ≤ ((1 + R + δ) / δ) ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹ := by
  have h := inverse_le_profile hδ hsep hwR
  rw [← inv_pow, norm_pow, ← inv_pow, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 3

/-- The inverse fourth power is bounded by the same integrable cubic profile. -/
theorem inverse_fourth_le_profile {ζ w : ℂ} {δ R : ℝ} (hδ : 0 < δ)
    (hsep : δ ≤ ‖ζ - w‖) (hwR : ‖w‖ ≤ R) :
    ‖((ζ - w) ^ 4)⁻¹‖ ≤ ((1 + R + δ) / δ) ^ 4 * ((1 + ‖ζ‖) ^ 3)⁻¹ := by
  have h := inverse_le_profile hδ hsep hwR
  have hs1 : 0 < 1 + ‖ζ‖ := by positivity
  have hi0 : 0 ≤ (1 + ‖ζ‖)⁻¹ := by positivity
  have hi1 : (1 + ‖ζ‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg ζ])
  have hA : 0 ≤ (1 + R + δ) / δ := by
    have : 0 ≤ R := (norm_nonneg w).trans hwR
    positivity
  rw [← inv_pow, norm_pow]
  calc ‖(ζ - w)⁻¹‖ ^ 4 ≤ ((1 + R + δ) / δ * (1 + ‖ζ‖)⁻¹) ^ 4 :=
        pow_le_pow_left₀ (norm_nonneg _) h 4
    _ = ((1 + R + δ) / δ) ^ 4 * (1 + ‖ζ‖)⁻¹ ^ 4 := by rw [mul_pow]
    _ ≤ ((1 + R + δ) / δ) ^ 4 * (1 + ‖ζ‖)⁻¹ ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hi0 hi1 (by norm_num)) (by positivity)
    _ = _ := by rw [inv_pow]

/-- Cubic decay is genuinely integrable for planar Lebesgue measure. -/
theorem cubic_profile_integrable :
    Integrable (fun ζ : ℂ => ((1 + ‖ζ‖) ^ 3)⁻¹) (volume : Measure ℂ) := by
  have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3)
    (by rw [Complex.finrank_real_complex]; norm_num)
  refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
  show (1 + ‖ζ‖) ^ (-(3 : ℝ)) = ((1 + ‖ζ‖) ^ 3)⁻¹
  rw [Real.rpow_neg (by positivity)]
  norm_cast


/-- Every point in the open exterior has a positive uniform separation radius. -/
private theorem exterior_radius {D : Set ℂ} {z : ℂ} (hz : z ∈ interior Dᶜ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ζ ∈ D, 2 * δ ≤ ‖ζ - z‖ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro ζ hζ
  have hn : ¬ ‖ζ - z‖ < ε := by
    intro h
    have hζb : ζ ∈ ball z ε := mem_ball.mpr (by simpa only [dist_eq_norm] using h)
    exact (interior_subset (hball hζb)) hζ
  linarith [not_lt.mp hn]

/-- The same separation is uniform on a genuine neighborhood of the evaluation point. -/
private theorem local_separation {ζ w z : ℂ} {δ : ℝ} (_hδ : 0 < δ)
    (hζ : 2 * δ ≤ ‖ζ - z‖) (hw : w ∈ ball z δ) :
    δ ≤ ‖ζ - w‖ ∧ ‖w‖ ≤ ‖z‖ + δ := by
  have hw' : ‖w - z‖ < δ := by simpa only [mem_ball, dist_eq_norm] using hw
  have htri : ‖ζ - z‖ ≤ ‖ζ - w‖ + ‖w - z‖ := by
    calc ‖ζ - z‖ = ‖(ζ - w) + (w - z)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hn : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
    calc ‖w‖ = ‖z + (w - z)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  constructor <;> linarith

/-- A bounded measurable coefficient has an absolutely integrable cubic kernel
on ANY measurable set away from its closure. No half-plane geometry is used. -/
theorem cubicKernel_integrable {D : Set ℂ} (hD : MeasurableSet D)
    {η : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : AEStronglyMeasurable η (volume.restrict D))
    (hb : ∀ᵐ ζ ∂(volume.restrict D), ‖η ζ‖ ≤ k)
    {z : ℂ} (hz : z ∈ interior Dᶜ) :
    IntegrableOn (fun ζ : ℂ => η ζ / (ζ - z) ^ 3) D := by
  obtain ⟨δ, hδ, hsep⟩ := exterior_radius hz
  let A : ℝ := (1 + (‖z‖ + δ) + δ) / δ
  refine Integrable.mono' ((cubic_profile_integrable.const_mul (A ^ 3)).const_mul k).integrableOn
    (hm.div₀ (by fun_prop : Measurable fun ζ : ℂ => (ζ - z) ^ 3).aestronglyMeasurable) ?_
  filter_upwards [hb, ae_restrict_mem hD] with ζ hζb hζ
  obtain ⟨hs, hR⟩ := local_separation hδ (hsep ζ hζ) (mem_ball_self hδ)
  rw [div_eq_mul_inv, norm_mul]
  exact mul_le_mul hζb (inverse_cube_le_profile hδ hs hR) (norm_nonneg _) hk

/-- The fourth Cauchy kernel is genuinely absolutely integrable on any
measurable domain at every point of its open exterior. -/
theorem fourthKernel_integrable {D : Set ℂ} (hD : MeasurableSet D)
    {η : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : AEStronglyMeasurable η (volume.restrict D))
    (hb : ∀ᵐ ζ ∂(volume.restrict D), ‖η ζ‖ ≤ k)
    {z : ℂ} (hz : z ∈ interior Dᶜ) :
    IntegrableOn (fun ζ : ℂ => η ζ / (ζ - z) ^ 4) D := by
  obtain ⟨δ, hδ, hsep⟩ := exterior_radius hz
  let A : ℝ := (1 + (‖z‖ + δ) + δ) / δ
  refine Integrable.mono' ((cubic_profile_integrable.const_mul (A ^ 4)).const_mul k).integrableOn
    (hm.div₀ (by fun_prop : Measurable fun ζ : ℂ => (ζ - z) ^ 4).aestronglyMeasurable) ?_
  filter_upwards [hb, ae_restrict_mem hD] with ζ hζb hζ
  obtain ⟨hs, hR⟩ := local_separation hδ (hsep ζ hζ) (mem_ball_self hδ)
  rw [div_eq_mul_inv, norm_mul]
  exact mul_le_mul hζb (inverse_fourth_le_profile hδ hs hR) (norm_nonneg _) hk

/-- In particular the integral of the absolute value is finite; the displayed
complex integral is never being used merely through its default value. -/
theorem fourthKernel_norm_integrable {D : Set ℂ} (hD : MeasurableSet D)
    {η : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : AEStronglyMeasurable η (volume.restrict D))
    (hb : ∀ᵐ ζ ∂(volume.restrict D), ‖η ζ‖ ≤ k)
    {z : ℂ} (hz : z ∈ interior Dᶜ) :
    IntegrableOn (fun ζ : ℂ => ‖η ζ / (ζ - z) ^ 4‖) D :=
  (fourthKernel_integrable hD hk hm hb hz).norm

/-- Differentiation of the cubic Cauchy integral on the actual open exterior.
The fourth-kernel domination is derived from distance separation. -/
theorem hasDerivAt_cubicIntegral {D : Set ℂ} (hD : MeasurableSet D)
    {η : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : AEStronglyMeasurable η (volume.restrict D))
    (hb : ∀ᵐ ζ ∂(volume.restrict D), ‖η ζ‖ ≤ k)
    {z : ℂ} (hz : z ∈ interior Dᶜ) :
    HasDerivAt (fun w => ∫ ζ in D, η ζ / (ζ - w) ^ 3)
      (3 * ∫ ζ in D, η ζ / (ζ - z) ^ 4) z := by
  obtain ⟨δ, hδ, hsep⟩ := exterior_radius hz
  let A : ℝ := (1 + (‖z‖ + δ) + δ) / δ
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict D)
    (F := fun w ζ => η ζ / (ζ - w) ^ 3)
    (F' := fun w ζ => 3 * (η ζ / (ζ - w) ^ 4))
    (bound := fun ζ => 3 * (k * (A ^ 4 * ((1 + ‖ζ‖) ^ 3)⁻¹)))
    (ball_mem_nhds z hδ)
    (Eventually.of_forall fun w =>
      hm.div₀ (by fun_prop : Measurable fun ζ : ℂ => (ζ - w) ^ 3).aestronglyMeasurable)
    (cubicKernel_integrable hD hk hm hb hz) ?_ ?_ ?_ ?_
  · rw [← integral_const_mul]
    exact h.2
  · exact (hm.div₀
      (by fun_prop : Measurable fun ζ : ℂ => (ζ - z) ^ 4).aestronglyMeasurable).const_mul 3
  · filter_upwards [hb, ae_restrict_mem hD] with ζ hζb hζ w hw
    obtain ⟨hs, hR⟩ := local_separation hδ (hsep ζ hζ) hw
    have hi := inverse_fourth_le_profile hδ hs hR
    rw [norm_mul, div_eq_mul_inv, norm_mul, Complex.norm_ofNat]
    gcongr
  · exact (((cubic_profile_integrable.const_mul (A ^ 4)).const_mul k).const_mul 3).integrableOn
  · filter_upwards [ae_restrict_mem hD] with ζ hζ w hw
    obtain ⟨hs, -⟩ := local_separation hδ (hsep ζ hζ) hw
    have hne : ζ ≠ w := sub_ne_zero.mp (norm_pos_iff.mp (hδ.trans_le hs))
    exact LiZhongQC.b36_p_hasDerivAt_K2 (η ζ) hne


private theorem kernelFirstDerivativeDifference_bound {ζ w a b : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hw : δ ≤ ‖ζ - w‖)
    (hwR : ‖w‖ ≤ R) (ha : δ ≤ ‖ζ - a‖) (haR : ‖a‖ ≤ R) (hb : δ ≤ ‖ζ - b‖) (hbR : ‖b‖ ≤ R) :
    ‖1 / (ζ - w) ^ 2 - 1 / ((ζ - a) * (ζ - b))‖ ≤
      6 * R * ((1 + R + δ) / δ) ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹ := by
  have hX : ζ - w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ hw)
  have hY : ζ - a ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ ha)
  have hZ : ζ - b ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hδ hb)
  have heq : 1 / (ζ - w) ^ 2 - 1 / ((ζ - a) * (ζ - b)) =
      (w - a) * ((ζ - w)⁻¹ * (ζ - a)⁻¹ * (ζ - a)⁻¹) +
        (w - a) * ((ζ - w)⁻¹ * (ζ - w)⁻¹ * (ζ - a)⁻¹) +
          (a - b) * ((ζ - a)⁻¹ * (ζ - a)⁻¹ * (ζ - b)⁻¹) := by
    field_simp
    ring
  set m : ℝ := (1 + R + δ) / δ * (1 + ‖ζ‖)⁻¹ with hm
  have hR : 0 ≤ R := (norm_nonneg w).trans hwR
  have hm0 : 0 ≤ m := by positivity
  have iw := inverse_le_profile hδ hw hwR
  have ia := inverse_le_profile hδ ha haR
  have ib := inverse_le_profile hδ hb hbR
  have hwa : ‖w - a‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
  have hab : ‖a - b‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
  have hm3 : m ^ 3 = ((1 + R + δ) / δ) ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹ := by
    rw [hm, mul_pow, inv_pow]
  rw [heq]
  calc ‖(w - a) * ((ζ - w)⁻¹ * (ζ - a)⁻¹ * (ζ - a)⁻¹) +
        (w - a) * ((ζ - w)⁻¹ * (ζ - w)⁻¹ * (ζ - a)⁻¹) +
          (a - b) * ((ζ - a)⁻¹ * (ζ - a)⁻¹ * (ζ - b)⁻¹)‖
      ≤ ‖(w - a) * ((ζ - w)⁻¹ * (ζ - a)⁻¹ * (ζ - a)⁻¹)‖ +
        ‖(w - a) * ((ζ - w)⁻¹ * (ζ - w)⁻¹ * (ζ - a)⁻¹)‖ +
          ‖(a - b) * ((ζ - a)⁻¹ * (ζ - a)⁻¹ * (ζ - b)⁻¹)‖ := norm_add₃_le
    _ ≤ 2 * R * (m * m * m) + 2 * R * (m * m * m) + 2 * R * (m * m * m) := by
        simp only [norm_mul]
        gcongr
    _ = 6 * R * ((1 + R + δ) / δ) ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹ := by
        rw [show 6 * R * ((1 + R + δ) / δ) ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹ = 6 * R * m ^ 3 by
          rw [hm3]; ring]
        ring



/-- The first derivative of the normalized kernel retains its cancellation at
infinity. Two fixed exterior points supply an integrable reference term. -/
private theorem normalizedKernelFirstDerivative_dominator
    {D : Set ℂ} (hD : MeasurableSet D) {z : ℂ} (hz : z ∈ interior Dᶜ) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ ζ ∈ D, 2 * δ ≤ ‖ζ - z‖) ∧
      ∃ g : ℂ → ℝ, Integrable g (volume.restrict D) ∧
        ∀ᵐ ζ ∂(volume.restrict D), ∀ w ∈ ball z δ,
          ‖1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1))‖ ≤ g ζ := by
  obtain ⟨δ, hδ, hsep⟩ := exterior_radius hz
  let b : ℂ := z + (δ / 2 : ℝ)
  have hbball : b ∈ ball z δ := by
    rw [mem_ball, dist_eq_norm]
    change ‖z + (δ / 2 : ℝ) - z‖ < δ
    rw [add_sub_cancel_left, Complex.norm_of_nonneg (by linarith : 0 ≤ δ / 2)]
    linarith
  have hab : z - b ≠ 0 := by
    change z - (z + (δ / 2 : ℝ)) ≠ 0
    rw [sub_add_eq_sub_sub, sub_self, zero_sub]
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (ne_of_gt (half_pos hδ)))
  let K : ℂ → ℂ := fun ζ => 1 / ((ζ - z) * (ζ - b)) - 1 / (ζ * (ζ - 1))
  have hK : Integrable K (volume.restrict D) := by
    refine (((LiZhongQC.ah_ker_integrable z).sub
      (LiZhongQC.ah_ker_integrable b)).div_const (z - b)).integrableOn.congr ?_
    filter_upwards [ae_restrict_mem hD, ae_restrict_of_ae (volume.ae_ne (0 : ℂ)),
      ae_restrict_of_ae (volume.ae_ne (1 : ℂ))] with ζ hζ h0 h1
    have ha := (local_separation hδ (hsep ζ hζ) (mem_ball_self hδ)).1
    have hb := (local_separation hδ (hsep ζ hζ) hbball).1
    have haz : ζ ≠ z := sub_ne_zero.mp (norm_pos_iff.mp (hδ.trans_le ha))
    have hbz : ζ ≠ b := sub_ne_zero.mp (norm_pos_iff.mp (hδ.trans_le hb))
    change (LiZhongQC.ahKer z ζ - LiZhongQC.ahKer b ζ) / (z - b) = K ζ
    rw [LiZhongQC.ahK_sub_eq h0 h1 haz hbz, sub_zero,
      mul_div_cancel_left₀ _ hab]
  let R : ℝ := ‖z‖ + δ
  let A : ℝ := (1 + R + δ) / δ
  refine ⟨δ, hδ, hsep, fun ζ => ‖K ζ‖ + 6 * R * A ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹,
    hK.norm.add (cubic_profile_integrable.const_mul _).integrableOn, ?_⟩
  filter_upwards [ae_restrict_mem hD] with ζ hζ w hw
  obtain ⟨hsw, hRw⟩ := local_separation hδ (hsep ζ hζ) hw
  obtain ⟨hsa, hRa⟩ := local_separation hδ (hsep ζ hζ) (mem_ball_self hδ)
  obtain ⟨hsb, hRb⟩ := local_separation hδ (hsep ζ hζ) hbball
  have hE := kernelFirstDerivativeDifference_bound hδ hsw hRw hsa hRa hsb hRb
  have he : 1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1)) =
      (1 / (ζ - w) ^ 2 - 1 / ((ζ - z) * (ζ - b))) + K ζ := by
    dsimp only [K]
    ring
  rw [he]
  calc _ ≤ ‖1 / (ζ - w) ^ 2 - 1 / ((ζ - z) * (ζ - b))‖ + ‖K ζ‖ := norm_add_le _ _
    _ ≤ _ := by dsimp only [R, A] at *; linarith

/-- First differentiation of the normalized integral on a general measurable
support domain. The two normalization singularities are excluded only a.e. -/
private theorem hasDerivAt_normalizedKernelIntegral
    {D : Set ℂ} (hD : MeasurableSet D) {η : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : AEStronglyMeasurable η (volume.restrict D))
    (hb : ∀ᵐ ζ ∂(volume.restrict D), ‖η ζ‖ ≤ k)
    {z : ℂ} (hz : z ∈ interior Dᶜ) :
    Integrable (fun ζ => η ζ * (1 / (ζ - z) ^ 2 - 1 / (ζ * (ζ - 1))))
      (volume.restrict D) ∧
      HasDerivAt (fun w => ∫ ζ in D, η ζ * LiZhongQC.ahKer w ζ)
        (∫ ζ in D, η ζ * (1 / (ζ - z) ^ 2 - 1 / (ζ * (ζ - 1)))) z := by
  obtain ⟨δ, hδ, hsep, g, hg, hgb⟩ := normalizedKernelFirstDerivative_dominator hD hz
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict D)
    (F := fun w ζ => η ζ * LiZhongQC.ahKer w ζ)
    (F' := fun w ζ => η ζ * (1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1))))
    (bound := fun ζ => k * g ζ) (ball_mem_nhds z hδ)
    (Eventually.of_forall fun w => hm.fun_mul (LiZhongQC.ahK_measurable w).aestronglyMeasurable)
    ((LiZhongQC.ah_ker_integrable z).integrableOn.bdd_mul hm hb) ?_ ?_ (hg.const_mul k) ?_
  · exact hm.fun_mul
      ((by fun_prop : Measurable fun ζ : ℂ =>
        1 / (ζ - z) ^ 2 - 1 / (ζ * (ζ - 1))).aestronglyMeasurable)
  · filter_upwards [hb, hgb] with ζ hζb hζ w hw
    rw [norm_mul]
    exact mul_le_mul hζb (hζ w hw) (norm_nonneg _) hk
  · filter_upwards [ae_restrict_mem hD, ae_restrict_of_ae (volume.ae_ne (0 : ℂ)),
      ae_restrict_of_ae (volume.ae_ne (1 : ℂ))] with ζ hζ h0 h1 w hw
    have hs := (local_separation hδ (hsep ζ hζ) hw).1
    have hne : ζ ≠ w := sub_ne_zero.mp (norm_pos_iff.mp (hδ.trans_le hs))
    exact (LiZhongQC.b36_p_hasDerivAt_ker h0 h1 hne).const_mul (η ζ)

/-- Second differentiation of the same actual normalized integral. -/
private theorem hasDerivAt_firstKernelIntegral
    {D : Set ℂ} (hD : MeasurableSet D) {η : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hm : AEStronglyMeasurable η (volume.restrict D))
    (hb : ∀ᵐ ζ ∂(volume.restrict D), ‖η ζ‖ ≤ k)
    {z : ℂ} (hz : z ∈ interior Dᶜ) :
    HasDerivAt (fun w => ∫ ζ in D, η ζ * (1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1))))
      (2 * ∫ ζ in D, η ζ / (ζ - z) ^ 3) z := by
  obtain ⟨δ, hδ, hsep⟩ := exterior_radius hz
  let A : ℝ := (1 + (‖z‖ + δ) + δ) / δ
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict D)
    (F := fun w ζ => η ζ * (1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1))))
    (F' := fun w ζ => 2 * (η ζ / (ζ - w) ^ 3))
    (bound := fun ζ => 2 * (k * (A ^ 3 * ((1 + ‖ζ‖) ^ 3)⁻¹)))
    (ball_mem_nhds z hδ)
    (Eventually.of_forall fun w => hm.fun_mul
      (by fun_prop : Measurable fun ζ : ℂ =>
        1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1))).aestronglyMeasurable)
    (hasDerivAt_normalizedKernelIntegral hD hk hm hb hz).1 ?_ ?_ ?_ ?_
  · rw [← integral_const_mul]
    exact h.2
  · exact (hm.div₀
      (by fun_prop : Measurable fun ζ : ℂ => (ζ - z) ^ 3).aestronglyMeasurable).const_mul 2
  · filter_upwards [hb, ae_restrict_mem hD] with ζ hζb hζ w hw
    obtain ⟨hs, hR⟩ := local_separation hδ (hsep ζ hζ) hw
    have hi := inverse_cube_le_profile hδ hs hR
    rw [norm_mul, div_eq_mul_inv, norm_mul, Complex.norm_ofNat]
    gcongr
  · exact (((cubic_profile_integrable.const_mul (A ^ 3)).const_mul k).const_mul 2).integrableOn
  · filter_upwards [ae_restrict_mem hD] with ζ hζ w hw
    have hs := (local_separation hδ (hsep ζ hζ) hw).1
    have hne : ζ ≠ w := sub_ne_zero.mp (norm_pos_iff.mp (hδ.trans_le hs))
    exact LiZhongQC.b36_p_hasDerivAt_K1 (η ζ) hne

/-- The actual normalized first variation has the literal fourth-kernel third
spatial derivative at every point of the open complement of its support domain. -/
theorem thirdDerivative_firstVariation {D : Set ℂ} (hD : MeasurableSet D)
    {η : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hη : LiZhongQC.IsBeltramiCoeff η univ k)
    (hsupport : ∀ᵐ ζ ∂volume, ζ ∉ D → η ζ = 0)
    {z : ℂ} (hz : z ∈ interior Dᶜ) :
    iteratedDeriv 3 (LiZhongQC.ahVar η) z =
      -(6 / Real.pi : ℂ) * ∫ ζ in D, η ζ / (ζ - z) ^ 4 := by
  have hm0 : AEStronglyMeasurable η (volume : Measure ℂ) := by
    simpa only [Measure.restrict_univ] using hη.1
  have hb0 : ∀ᵐ ζ ∂volume, ‖η ζ‖ ≤ k := by
    simpa only [Measure.restrict_univ] using hη.2
  have hm : AEStronglyMeasurable η (volume.restrict D) := hm0.restrict
  have hb : ∀ᵐ ζ ∂(volume.restrict D), ‖η ζ‖ ≤ k := ae_restrict_of_ae hb0
  let N : ℂ → ℂ := fun w => -(1 / Real.pi : ℂ) * ∫ ζ in D, η ζ * LiZhongQC.ahKer w ζ
  let G : ℂ → ℂ := fun w => ∫ ζ in D, η ζ * (1 / (ζ - w) ^ 2 - 1 / (ζ * (ζ - 1)))
  let H : ℂ → ℂ := fun w => ∫ ζ in D, η ζ / (ζ - w) ^ 3
  have hN : LiZhongQC.ahVar η = N := by
    funext w
    have hae : (fun ζ => η ζ * LiZhongQC.ahKer w ζ) =ᵐ[volume]
        D.indicator (fun ζ => η ζ * LiZhongQC.ahKer w ζ) := by
      filter_upwards [hsupport] with ζ hζ
      by_cases hζD : ζ ∈ D
      · rw [indicator_of_mem hζD]
      · rw [indicator_of_notMem hζD, hζ hζD, zero_mul]
    dsimp only [LiZhongQC.ahVar, N]
    rw [integral_congr_ae hae, integral_indicator hD]
  have h1 : ∀ w ∈ interior Dᶜ,
      HasDerivAt N (-(1 / Real.pi : ℂ) * G w) w := by
    intro w hw
    exact ((hasDerivAt_normalizedKernelIntegral hD hk hm hb hw).2).const_mul _
  have h2 : ∀ w ∈ interior Dᶜ, HasDerivAt G (2 * H w) w := by
    intro w hw
    exact hasDerivAt_firstKernelIntegral hD hk hm hb hw
  have h3 : HasDerivAt H (3 * ∫ ζ in D, η ζ / (ζ - z) ^ 4) z :=
    hasDerivAt_cubicIntegral hD hk hm hb hz
  have e1 : ∀ w ∈ interior Dᶜ,
      deriv N =ᶠ[𝓝 w] fun v => -(1 / Real.pi : ℂ) * G v := by
    intro w hw
    filter_upwards [isOpen_interior.mem_nhds hw] with v hv
    exact (h1 v hv).deriv
  have e2 : deriv (deriv N) =ᶠ[𝓝 z] fun v => -(1 / Real.pi : ℂ) * (2 * H v) := by
    filter_upwards [isOpen_interior.mem_nhds hz] with v hv
    rw [(e1 v hv).deriv_eq]
    exact ((h2 v hv).const_mul (-(1 / Real.pi : ℂ))).deriv
  have ht : deriv (deriv (deriv N)) z =
      -(6 / Real.pi : ℂ) * ∫ ζ in D, η ζ / (ζ - z) ^ 4 := by
    rw [e2.deriv_eq, ((h3.const_mul 2).const_mul (-(1 / Real.pi : ℂ))).deriv]
    ring
  rw [hN]
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using ht

/-- Both absolute integrability and the actual third derivative are derived
from the original bounded coefficient and its true support information. -/
theorem firstVariation_thirdDerivative_and_integrable
    {D : Set ℂ} (hD : MeasurableSet D) {η : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hη : LiZhongQC.IsBeltramiCoeff η univ k)
    (hsupport : ∀ᵐ ζ ∂volume, ζ ∉ D → η ζ = 0)
    {z : ℂ} (hz : z ∈ interior Dᶜ) :
    IntegrableOn (fun ζ : ℂ => η ζ / (ζ - z) ^ 4) D ∧
      iteratedDeriv 3 (LiZhongQC.ahVar η) z =
        -(6 / Real.pi : ℂ) * ∫ ζ in D, η ζ / (ζ - z) ^ 4 := by
  have hm : AEStronglyMeasurable η (volume : Measure ℂ) := by
    simpa only [Measure.restrict_univ] using hη.1
  have hb : ∀ᵐ ζ ∂volume, ‖η ζ‖ ≤ k := by
    simpa only [Measure.restrict_univ] using hη.2
  exact ⟨fourthKernel_integrable hD hk hm.restrict (ae_restrict_of_ae hb) hz,
    thirdDerivative_firstVariation hD hk hη hsupport hz⟩

end LowDimensionalTopology.Geometry.Quasiconformal.OffSupportCauchy
