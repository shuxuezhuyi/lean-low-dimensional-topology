module

public import LowDimensionalTopology.Geometry.Teichmuller.ElementaryAngularTwistHomeomorphism
public import LowDimensionalTopology.External.LiZhongQC.Ch02.S13_Representation
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Tactic.Positivity

/-!
# Quasiconformality and the actual coefficient of the elementary angular map

The same map is continuously differentiable away from its two seam lines.
The existing removability theorem gives quasiconformality across those null
lines. The actual spatial quotient agrees almost everywhere with the same
closed-band coefficient, whose strict bound holds for every real parameter.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter Topology MeasureTheory
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)

private def planeTau (θ : Width) (t : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if hz : 0 < z.im then coefficientCurve θ t (⟨z, hz⟩ : ℍ) else 0

private theorem planeTau_coe (θ : Width) (t : ℝ) (z : ℍ) :
    planeTau θ t z = coefficientCurve θ t z := by
  classical
  unfold planeTau
  exact dite_eq_left z.im_pos

private theorem norm_shear_fraction (ε : ℝ) :
    ‖Complex.I * (ε : ℂ) / (2 - Complex.I * (ε : ℂ))‖ =
      |ε| / Real.sqrt (4 + ε ^ 2) := by
  have hd : ‖(2 : ℂ) - Complex.I * (ε : ℂ)‖ = Real.sqrt (4 + ε ^ 2) := by
    rw [Complex.norm_def]
    congr 1
    norm_num [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, pow_two]
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, hd,
    Complex.norm_real, Real.norm_eq_abs]

private theorem shear_bound (ε : ℝ) :
    0 ≤ |ε| / Real.sqrt (4 + ε ^ 2) ∧ |ε| / Real.sqrt (4 + ε ^ 2) < 1 := by
  have hs : 0 < Real.sqrt (4 + ε ^ 2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg ε])
  refine ⟨div_nonneg (abs_nonneg _) hs.le, (div_lt_one hs).mpr ?_⟩
  apply (Real.lt_sqrt (abs_nonneg ε)).mpr
  nlinarith [sq_abs ε]

private theorem norm_planeTau_le (θ : Width) (t : ℝ) {z : ℂ}
    (hz : z ∈ LiZhongQC.upperHalf) :
    ‖planeTau θ t z‖ ≤ |shear θ t| / Real.sqrt (4 + shear θ t ^ 2) := by
  classical
  rw [planeTau_coe θ t (⟨z, hz⟩ : ℍ), coefficientCurve_eq_source]
  by_cases ha : Complex.arg z ∈ interval θ
  · have hnz : z ≠ 0 := (⟨z, hz⟩ : ℍ).ne_zero
    have hphase : ‖z / (starRingEnd ℂ) z‖ = 1 := by
      rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hnz)]
    simpa only [ite_eq_left ha, norm_mul, hphase, mul_one, norm_shear_fraction] using
      (le_refl (|shear θ t| / Real.sqrt (4 + shear θ t ^ 2)))
  · rw [ite_eq_right ha, norm_zero]
    exact (shear_bound (shear θ t)).1

private theorem measurable_planeTau (θ : Width) (t : ℝ) : Measurable (planeTau θ t) := by
  classical
  let c : ℂ := Complex.I * (shear θ t : ℂ) / (2 - Complex.I * (shear θ t : ℂ))
  have he : planeTau θ t = fun z : ℂ =>
      if 0 < z.im ∧ Complex.arg z ∈ interval θ then c * (z / (starRingEnd ℂ) z) else 0 := by
    funext z
    by_cases hz : 0 < z.im <;> simp [planeTau, hz, coefficientCurve_eq_source, c]
  have hi : MeasurableSet {z : ℂ | Complex.arg z ∈ interval θ} :=
    measurableSet_Icc.preimage Complex.measurable_arg
  rw [he]
  exact Measurable.ite ((measurableSet_lt measurable_const Complex.measurable_im).inter hi)
    (measurable_const.mul (measurable_id.div Complex.continuous_conj.measurable))
    measurable_const

private def seamForm (a : ℝ) : ℂ →L[ℝ] ℝ :=
  Real.cos a • Complex.imCLM - Real.sin a • Complex.reCLM

private def seamLines (θ : Width) : Set ℂ :=
  ((seamForm (Real.pi / 2 - (θ : ℝ))).toLinearMap.ker : Set ℂ) ∪
    ((seamForm (Real.pi / 2 + (θ : ℝ))).toLinearMap.ker : Set ℂ)

private theorem seam_trig_nonzero (θ : Width) :
    Real.sin (Real.pi / 2 - (θ : ℝ)) ≠ 0 ∧
      Real.sin (Real.pi / 2 + (θ : ℝ)) ≠ 0 ∧
      Real.cos (Real.pi / 2 - (θ : ℝ)) ≠ 0 ∧
      Real.cos (Real.pi / 2 + (θ : ℝ)) ≠ 0 := by
  have hc : 0 < Real.cos (θ : ℝ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, θ.property.1], θ.property.2⟩
  have hs : 0 < Real.sin (θ : ℝ) :=
    Real.sin_pos_of_pos_of_lt_pi θ.property.1 (by linarith [θ.property.2, Real.pi_pos])
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Real.sin_pi_div_two_sub] using hc.ne'
  · simpa only [add_comm (Real.pi / 2) (θ : ℝ), Real.sin_add_pi_div_two] using hc.ne'
  · simpa only [Real.cos_pi_div_two_sub] using hs.ne'
  · simpa only [add_comm (Real.pi / 2) (θ : ℝ), Real.cos_add_pi_div_two,
      neg_ne_zero] using hs.ne'

private theorem seam_null (a : ℝ) (ha : Real.sin a ≠ 0) :
    volume ((seamForm a).toLinearMap.ker : Set ℂ) = 0 := by
  apply MeasureTheory.Measure.addHaar_submodule volume
  intro htop
  have hmem : (1 : ℂ) ∈ (seamForm a).toLinearMap.ker := by
    rw [htop]
    exact Submodule.mem_top
  have hzero : seamForm a (1 : ℂ) = 0 := hmem
  apply ha
  simpa [seamForm] using hzero

private theorem seam_vertical_countable (a x : ℝ) (ha : Real.cos a ≠ 0) :
    {y : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ (seamForm a).toLinearMap.ker}.Countable := by
  apply (Set.countable_singleton (Real.sin a * x / Real.cos a)).mono
  intro y hy
  apply Set.mem_singleton_iff.mpr
  have he : Real.cos a * y - Real.sin a * x = 0 := by simpa [seamForm] using hy
  apply (eq_div_iff ha).mpr
  nlinarith

private theorem seam_horizontal_countable (a y : ℝ) (ha : Real.sin a ≠ 0) :
    {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ (seamForm a).toLinearMap.ker}.Countable := by
  apply (Set.countable_singleton (Real.cos a * y / Real.sin a)).mono
  intro x hx
  apply Set.mem_singleton_iff.mpr
  have he : Real.cos a * y - Real.sin a * x = 0 := by simpa [seamForm] using hx
  apply (eq_div_iff ha).mpr
  nlinarith

private theorem angle_mem_seam {z : ℂ} {a : ℝ} (ha : Complex.arg z = a) :
    z ∈ (seamForm a).toLinearMap.ker := by
  change Real.cos a * z.im - Real.sin a * z.re = 0
  rw [← Complex.norm_mul_sin_arg z, ← Complex.norm_mul_cos_arg z, ha]
  ring

private theorem spatial_away_seams (θ : Width) (t : ℝ) {z : ℂ}
    (hz : z ∈ LiZhongQC.upperHalf \ seamLines θ) :
    ContDiffAt ℝ 1 (elementaryMapPlane θ t) z ∧
      LiZhongQC.dz (elementaryMapPlane θ t) z ≠ 0 ∧
      LiZhongQC.complexDilatation (elementaryMapPlane θ t) z = planeTau θ t z := by
  classical
  let zh : ℍ := ⟨z, hz.1⟩
  have hslit : z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hz.1))
  have harg : ContDiffAt ℝ 1 Complex.arg z := by
    simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using
      Complex.imCLM.contDiff.contDiffAt.comp z
        ((Complex.contDiffAt_log (n := 1) hslit).restrict_scalars ℝ)
  have him : ∀ᶠ w : ℂ in 𝓝 z, 0 < w.im :=
    (Complex.continuous_im.tendsto z).eventually (isOpen_Ioi.mem_nhds hz.1)
  have hlo_ne : Complex.arg z ≠ Real.pi / 2 - (θ : ℝ) := by
    intro he
    exact hz.2 (Or.inl (angle_mem_seam he))
  have hhi_ne : Complex.arg z ≠ Real.pi / 2 + (θ : ℝ) := by
    intro he
    exact hz.2 (Or.inr (angle_mem_seam he))
  rcases lt_or_gt_of_ne hlo_ne with hlo | hlo
  · have hang : ∀ᶠ w : ℂ in 𝓝 z, Complex.arg w < Real.pi / 2 - (θ : ℝ) :=
      (Complex.continuousAt_arg hslit).eventually (isOpen_Iio.mem_nhds hlo)
    have he : elementaryMapPlane θ t =ᶠ[𝓝 z] (fun w : ℂ => w) := by
      filter_upwards [him, hang] with w hw hwarg
      rw [elementaryMapPlane, dite_eq_left hw, coe_elementaryMap, ite_eq_left hwarg]
    have hsp := elementaryMapPlane_spatial_below θ t zh hlo
    exact ⟨contDiffAt_id.congr_of_eventuallyEq he, hsp.2.2.2.1,
      hsp.2.2.2.2.trans (planeTau_coe θ t zh).symm⟩
  · rcases lt_or_gt_of_ne hhi_ne with hhi | hhi
    · have hlow : ∀ᶠ w : ℂ in 𝓝 z, Real.pi / 2 - (θ : ℝ) < Complex.arg w :=
        (Complex.continuousAt_arg hslit).eventually (isOpen_Ioi.mem_nhds hlo)
      have hhigh : ∀ᶠ w : ℂ in 𝓝 z, Complex.arg w < Real.pi / 2 + (θ : ℝ) :=
        (Complex.continuousAt_arg hslit).eventually (isOpen_Iio.mem_nhds hhi)
      have he : elementaryMapPlane θ t =ᶠ[𝓝 z] fun w : ℂ =>
          w * (Real.exp (shear θ t * (Complex.arg w - Real.pi / 2 + (θ : ℝ))) : ℂ) := by
        filter_upwards [him, hlow, hhigh] with w hw hwlo hwhi
        rw [elementaryMapPlane, dite_eq_left hw, coe_elementaryMap,
          ite_eq_right (not_lt.mpr hwlo.le), ite_eq_left hwhi.le]
      have hexp : ContDiffAt ℝ 1
          (fun w : ℂ => Real.exp (shear θ t * (Complex.arg w - Real.pi / 2 + (θ : ℝ)))) z :=
        (contDiffAt_const.mul ((harg.sub contDiffAt_const).add contDiffAt_const)).exp
      have hbranch : ContDiffAt ℝ 1
          (fun w : ℂ => w *
            (Real.exp (shear θ t * (Complex.arg w - Real.pi / 2 + (θ : ℝ))) : ℂ)) z :=
        contDiffAt_id.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp z hexp)
      have hsp := elementaryMapPlane_spatial_middle θ t zh hlo hhi
      exact ⟨hbranch.congr_of_eventuallyEq he, hsp.2.2.2.1,
        hsp.2.2.2.2.trans (planeTau_coe θ t zh).symm⟩
    · have hang : ∀ᶠ w : ℂ in 𝓝 z, Real.pi / 2 + (θ : ℝ) < Complex.arg w :=
        (Complex.continuousAt_arg hslit).eventually (isOpen_Ioi.mem_nhds hhi)
      have he : elementaryMapPlane θ t =ᶠ[𝓝 z]
          (fun w : ℂ => w * (Real.exp (-t) : ℂ)) := by
        filter_upwards [him, hang] with w hw hwarg
        have hn : ¬ Complex.arg w < Real.pi / 2 - (θ : ℝ) := by linarith [θ.property.1]
        rw [elementaryMapPlane, dite_eq_left hw, coe_elementaryMap,
          ite_eq_right hn, ite_eq_right (not_le.mpr hwarg)]
      have hbranch : ContDiffAt ℝ 1 (fun w : ℂ => w * (Real.exp (-t) : ℂ)) z :=
        contDiffAt_id.mul contDiffAt_const
      have hsp := elementaryMapPlane_spatial_above θ t zh hhi
      exact ⟨hbranch.congr_of_eventuallyEq he, hsp.2.2.2.1,
        hsp.2.2.2.2.trans (planeTau_coe θ t zh).symm⟩

/-- The same elementary map is genuinely quasiconformal on the whole H,
and its actual spatial coefficient is the original tau almost everywhere. -/
theorem elementaryMap_actual_qc_and_coefficient (θ : Width) (t : ℝ) :
    let ε := shear θ t
    let k := |ε| / Real.sqrt (4 + ε ^ 2)
    let K := (1 + k) / (1 - k)
    let W := elementaryMapPlane θ t
    let τ : ℂ → ℂ := by
      classical
      exact fun z => if hz : 0 < z.im then coefficientCurve θ t (⟨z, hz⟩ : ℍ) else 0
    0 ≤ k ∧ k < 1 ∧ 1 ≤ K ∧
      LiZhongQC.IsKQC W LiZhongQC.upperHalf K ∧
      (∀ᵐ z ∂volume.restrict LiZhongQC.upperHalf,
        LiZhongQC.complexDilatation W z = τ z) ∧
      LiZhongQC.IsBeltramiCoeff τ LiZhongQC.upperHalf k := by
  let k := |shear θ t| / Real.sqrt (4 + shear θ t ^ 2)
  let K := (1 + k) / (1 - k)
  let W := elementaryMapPlane θ t
  let L := seamLines θ
  obtain ⟨hk0, hk1⟩ := shear_bound (shear θ t)
  have hK : 1 ≤ K := by
    apply (le_div_iff₀ (sub_pos.mpr hk1)).mpr
    linarith
  obtain ⟨hsm, hsp, hcm, hcp⟩ := seam_trig_nonzero θ
  have hnull : volume L = 0 :=
    measure_union_null (seam_null _ hsm) (seam_null _ hsp)
  have hv : ∀ᵐ x : ℝ, {y : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ L}.Countable :=
    ae_of_all _ (fun x => (seam_vertical_countable _ x hcm).union
      (seam_vertical_countable _ x hcp))
  have hh : ∀ᵐ y : ℝ, {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ L}.Countable :=
    ae_of_all _ (fun y => (seam_horizontal_countable _ y hsm).union
      (seam_horizontal_countable _ y hsp))
  have hclosed (a : ℝ) : IsClosed ((seamForm a).toLinearMap.ker : Set ℂ) :=
    isClosed_singleton.preimage (seamForm a).continuous
  have hopen : IsOpen (LiZhongQC.upperHalf \ L) :=
    LiZhongQC.isOpen_upperHalf.sdiff ((hclosed _).union (hclosed _))
  have hhomeo := (elementaryMap_inverse_continuous θ t).2.2.2
  have hC1 : LiZhongQC.IsC1Quasiconformal W (LiZhongQC.upperHalf \ L) K := by
    refine ⟨hopen, hK, (fun z hz => (spatial_away_seams θ t hz).1.contDiffWithinAt),
      LiZhongQC.aqc_isHomeomorphOnto_restrict hhomeo LiZhongQC.isOpen_upperHalf
        sdiff_subset hopen, ?_⟩
    intro z hz
    obtain ⟨_, hdz, he⟩ := spatial_away_seams θ t hz
    have hq : ‖LiZhongQC.complexDilatation W z‖ ≤ k := by
      rw [he]
      exact norm_planeTau_le θ t hz.1
    have hdzpos : 0 < ‖LiZhongQC.dz W z‖ := norm_pos_iff.mpr hdz
    have hq1 : ‖LiZhongQC.complexDilatation W z‖ < 1 := hq.trans_lt hk1
    refine ⟨?_, ?_⟩
    · have hratio : ‖LiZhongQC.dzbar W z‖ / ‖LiZhongQC.dz W z‖ ≤ k := by
        simpa only [LiZhongQC.complexDilatation, norm_div] using hq
      have hm := (div_le_iff₀ hdzpos).mp hratio
      nlinarith
    · change (1 + ‖LiZhongQC.complexDilatation W z‖) /
        (1 - ‖LiZhongQC.complexDilatation W z‖) ≤ (1 + k) / (1 - k)
      apply (div_le_div_iff₀ (sub_pos.mpr hq1) (sub_pos.mpr hk1)).mpr
      nlinarith
  have hqc : LiZhongQC.IsKQC W LiZhongQC.upperHalf K := by
    have hhomeoImage : LiZhongQC.IsHomeomorphOnto W LiZhongQC.upperHalf
        (W '' LiZhongQC.upperHalf) := by
      rw [hhomeo.2.2.1]
      exact hhomeo
    apply LiZhongQC.s13x_removable LiZhongQC.isOpen_upperHalf hK
      hhomeoImage hnull hv hh
    intro z hz
    exact ⟨LiZhongQC.upperHalf \ L, hopen, hz, sdiff_subset,
      LiZhongQC.isKQC_of_isC1Quasiconformal hC1⟩
  have hae : ∀ᵐ z ∂volume.restrict LiZhongQC.upperHalf,
      LiZhongQC.complexDilatation W z = planeTau θ t z := by
    filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hnull),
      ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet] with z hn hz
    exact (spatial_away_seams θ t ⟨hz, hn⟩).2.2
  refine ⟨hk0, hk1, hK, hqc, hae,
    (measurable_planeTau θ t).aestronglyMeasurable.restrict, ?_⟩
  filter_upwards [ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet] with z hz
  exact norm_planeTau_le θ t hz

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
