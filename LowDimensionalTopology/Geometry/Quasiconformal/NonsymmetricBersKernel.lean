/-
The normalized-solution, coefficient and quasiconformal area APIs reuse
Wu Xiaobin's Li-Zhong-QC-formalization, pinned commit
1c0d5473c020b66ed5106331a38a61536760b9b2, under Apache 2.0.
The map below is the nonsymmetric normalized plane solution throughout.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalBersVariation
public import LowDimensionalTopology.Geometry.Quasiconformal.OffSupportCauchyKernels
public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiInverse
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

namespace LowDimensionalTopology.Geometry.Quasiconformal.CanonicalBersVariation

/-- The genuine normalized plane solution as its actual global homeomorphism. -/
def baseHomeomorph (μ : LiZhongQC.BeltramiH) : ℂ ≃ₜ ℂ where
  toFun := baseMap μ
  invFun := baseInverse μ
  left_inv := baseMap_leftInverse μ
  right_inv := baseMap_rightInverse μ
  continuous_toFun := by
    obtain ⟨K, hK⟩ := (LiZhongQC.ut_spec μ).1
    exact continuousOn_univ.mp hK.2.2.1.1
  continuous_invFun := by
    obtain ⟨K, hK⟩ := (LiZhongQC.ut_spec μ).1
    have h := hK.2.2.1.2.2.2
    rw [(LiZhongQC.ut_spec μ).2.1] at h
    exact continuousOn_univ.mp h

/-- The actual image of the upper half-plane under the same nonsymmetric solution. -/
def upperImage (μ : LiZhongQC.BeltramiH) : Set ℂ :=
  baseMap μ '' LiZhongQC.upperHalf

theorem upperImage_isOpen (μ : LiZhongQC.BeltramiH) : IsOpen (upperImage μ) :=
  (baseHomeomorph μ).isOpenMap _ LiZhongQC.isOpen_upperHalf

/-- The distorted lower half-plane is an actual open exterior of the distorted upper half-plane. -/
theorem lowerImage_subset_interior_compl_upperImage (μ : LiZhongQC.BeltramiH) :
    lowerImage μ ⊆ interior (upperImage μ)ᶜ := by
  have hs : lowerImage μ ⊆ (upperImage μ)ᶜ := by
    rintro w ⟨z, hz, rfl⟩ ⟨ζ, hζ, he⟩
    have hζz : ζ = z := baseMap_injective μ he
    subst ζ
    change z.im < 0 at hz
    change 0 < z.im at hζ
    exact (not_lt_of_gt hz) hζ
  intro w hw
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset ((lowerImage_isOpen μ).mem_nhds hw) hs)

/-- The actual quotient derivative coefficient, with no fixed-half-plane replacement. -/
def transportedDirection (μ : LiZhongQC.BeltramiH) (η : ℂ → ℂ) : ℂ → ℂ :=
  LiZhongQC.ahT_dot η μ.val (baseMap μ)

/-- Its genuine essential bound is derived from the two original coefficient bounds. -/
theorem transportedDirection_isBeltramiCoeff (μ : LiZhongQC.BeltramiH)
    {η : ℂ → ℂ} {M k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hμ : LiZhongQC.IsBeltramiCoeff μ.val univ k)
    (hη : LiZhongQC.IsBeltramiCoeff η univ M) :
    LiZhongQC.IsBeltramiCoeff (transportedDirection μ η) univ (M / (1 - k ^ 2)) := by
  have hqmp := LiZhongQC.ahT_qmp_inv (LiZhongQC.ut_spec μ).1 (LiZhongQC.ut_spec μ).2.1
  have hμm : AEStronglyMeasurable μ.val (volume : Measure ℂ) := by
    simpa only [Measure.restrict_univ] using hμ.1
  have hηm : AEStronglyMeasurable η (volume : Measure ℂ) := by
    simpa only [Measure.restrict_univ] using hη.1
  have hdzm : AEStronglyMeasurable (LiZhongQC.dz (baseMap μ)) volume :=
    (LiZhongQC.measurable_dz _).aestronglyMeasurable
  have hρm : AEStronglyMeasurable
      (fun z => LiZhongQC.dz (baseMap μ) z / conj (LiZhongQC.dz (baseMap μ) z)) volume :=
    hdzm.div₀ (Complex.continuous_conj.comp_aestronglyMeasurable hdzm)
  have hin : AEStronglyMeasurable (fun z =>
      η z / (1 - conj (μ.val z) * μ.val z) *
        (LiZhongQC.dz (baseMap μ) z / conj (LiZhongQC.dz (baseMap μ) z))) volume :=
    (hηm.div₀ (aestronglyMeasurable_const.sub
      ((Complex.continuous_conj.comp_aestronglyMeasurable hμm).mul hμm))).mul hρm
  refine ⟨?_, ?_⟩
  · rw [Measure.restrict_univ]
    exact hin.comp_quasiMeasurePreserving hqmp
  · rw [Measure.restrict_univ]
    have hbμ : ∀ᵐ z ∂volume, ‖μ.val z‖ ≤ k := by
      simpa only [Measure.restrict_univ] using hμ.2
    have hbη : ∀ᵐ z ∂volume, ‖η z‖ ≤ M := by
      simpa only [Measure.restrict_univ] using hη.2
    filter_upwards [hqmp.ae (hbμ.and hbη)] with w hw
    exact LiZhongQC.ahT_frac_le hk0 hk1 hw.1 hw.1
      (LiZhongQC.ahT_norm_div_conj_le _) hw.2

/-- The true upper support is transported through the true global inverse. -/
theorem transportedDirection_eq_zero_off_upperImage (μ : LiZhongQC.BeltramiH)
    {η : ℂ → ℂ} (hzero : ∀ z : ℂ, z.im ≤ 0 → η z = 0) :
    ∀ w ∉ upperImage μ, transportedDirection μ η w = 0 := by
  intro w hw
  have hx : (baseInverse μ w).im ≤ 0 := by
    by_contra hn
    apply hw
    exact ⟨baseInverse μ w, lt_of_not_ge hn, baseMap_rightInverse μ w⟩
  change η (baseInverse μ w) / _ * _ = 0
  rw [hzero _ hx, zero_div, zero_mul]

/-- A positive Jacobian supplies the nonzero spatial derivative needed for actual cancellation. -/
theorem jacobian_mul_transportedDirection_forward_ae (μ : LiZhongQC.BeltramiH)
    {η : ℂ → ℂ} :
    ∀ᵐ z : ℂ ∂volume,
      (LiZhongQC.jacobian (baseMap μ) z : ℂ) *
        transportedDirection μ η (baseMap μ z) = η z * LiZhongQC.dz (baseMap μ) z ^ 2 := by
  obtain ⟨K, hK⟩ := (LiZhongQC.ut_spec μ).1
  have hpde := LiZhongQC.abW_ae_dilatation hK
  have hJpos := LiZhongQC.thm9_6_cor2_jacobian_pos hK
  rw [Measure.restrict_univ] at hpde hJpos
  obtain ⟨k, hk0, hk1, hμ⟩ := μ.property.1
  have hb : ∀ᵐ z ∂volume, ‖μ.val z‖ ≤ k := by
    simpa only [Measure.restrict_univ] using hμ.2
  filter_upwards [hpde, hJpos, (LiZhongQC.ut_spec μ).2.2.2.2, hb] with z hp hJ hcd hbz
  have hpdeμ : LiZhongQC.dzbar (baseMap μ) z = μ.val z * LiZhongQC.dz (baseMap μ) z := by
    simpa only [baseMap, hcd] using hp.1
  change 0 < LiZhongQC.jacobian (baseMap μ) z at hJ
  have hd : LiZhongQC.dz (baseMap μ) z ≠ 0 := by
    intro hd0
    unfold LiZhongQC.jacobian at hJ
    rw [hd0, norm_zero, zero_pow (by norm_num)] at hJ
    nlinarith [sq_nonneg ‖LiZhongQC.dzbar (baseMap μ) z‖]
  have hdc : conj (LiZhongQC.dz (baseMap μ) z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hd
  have hden : 1 - conj (μ.val z) * μ.val z ≠ 0 := by
    apply norm_pos_iff.mp
    exact (by nlinarith : 0 < 1 - k ^ 2).trans_le
      (LiZhongQC.ahT_denom_ge hk0 hbz hbz)
  have hraw : (LiZhongQC.jacobian (baseMap μ) z : ℂ) =
      (1 - conj (μ.val z) * μ.val z) *
        (LiZhongQC.dz (baseMap μ) z * conj (LiZhongQC.dz (baseMap μ) z)) := by
    have h1 : LiZhongQC.dz (baseMap μ) z * conj (LiZhongQC.dz (baseMap μ) z) =
        ((‖LiZhongQC.dz (baseMap μ) z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    have h2 : LiZhongQC.dzbar (baseMap μ) z * conj (LiZhongQC.dzbar (baseMap μ) z) =
        ((‖LiZhongQC.dzbar (baseMap μ) z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.sq_norm]
    have he : (LiZhongQC.jacobian (baseMap μ) z : ℂ) =
        LiZhongQC.dz (baseMap μ) z * conj (LiZhongQC.dz (baseMap μ) z) -
          LiZhongQC.dzbar (baseMap μ) z * conj (LiZhongQC.dzbar (baseMap μ) z) :=
      (Complex.ofReal_sub _ _).trans (congrArg₂ (fun a b : ℂ => a - b) h1.symm h2.symm)
    rw [he, hpdeμ, map_mul]
    ring
  change (LiZhongQC.jacobian (baseMap μ) z : ℂ) *
    (η (baseInverse μ (baseMap μ z)) /
      (1 - conj (μ.val (baseInverse μ (baseMap μ z))) * μ.val (baseInverse μ (baseMap μ z))) *
        (LiZhongQC.dz (baseMap μ) (baseInverse μ (baseMap μ z)) /
          conj (LiZhongQC.dz (baseMap μ) (baseInverse μ (baseMap μ z))))) = _
  rw [baseMap_leftInverse μ z, hraw]
  field_simp [hden, hdc]

private theorem integrable_jacobian_mul_base (μ : LiZhongQC.BeltramiH)
    {G : ℂ → ℂ} (hG : Integrable G (volume : Measure ℂ)) :
    Integrable (fun z => (LiZhongQC.jacobian (baseMap μ) z : ℂ) * G (baseMap μ z)) volume := by
  obtain ⟨K, hK⟩ := (LiZhongQC.ut_spec μ).1
  let e := baseHomeomorph μ
  have hmap : Integrable G (Measure.map e
      (volume.withDensity (fun z => ENNReal.ofReal (LiZhongQC.jacobian e z)))) := by
    rw [quasiconformal_homeomorph_map_jacobian e hK]
    exact hG
  have hpull := hmap.comp_measurable e.continuous.measurable
  have hJ : Measurable (fun z => ENNReal.ofReal (LiZhongQC.jacobian e z)) :=
    (((LiZhongQC.measurable_dz e).norm.pow_const 2).sub
      ((LiZhongQC.measurable_dzbar e).norm.pow_const 2)).ennreal_ofReal
  have hfinite : ∀ᵐ z : ℂ ∂volume, ENNReal.ofReal (LiZhongQC.jacobian e z) < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hweighted := (integrable_withDensity_iff_integrable_smul' hJ hfinite).1 hpull
  have he : (e : ℂ → ℂ) = LiZhongQC.normalizedSolution μ.val := by
    funext z
    rfl
  have hpos : ∀ᵐ z : ℂ ∂volume, 0 < LiZhongQC.jacobian e z := by
    rw [he]
    simpa only [Measure.restrict_univ] using LiZhongQC.thm9_6_cor2_jacobian_pos hK
  apply hweighted.congr
  filter_upwards [hpos] with z hz
  exact (congrArg (fun a : ℝ => a • G (e z))
    (ENNReal.toReal_ofReal hz.le)).trans Complex.real_smul

/-- The literal arbitrary-base fourth kernel uses the original spatial derivative. -/
def originalFourthKernel (μ : LiZhongQC.BeltramiH) (η : ℂ → ℂ) (z ζ : ℂ) : ℂ :=
  η ζ * LiZhongQC.dz (baseMap μ) ζ ^ 2 / (baseMap μ ζ - baseMap μ z) ^ 4

/-- Absolute integrability and actual area substitution for the same original nonsymmetric map. -/
theorem fourthKernel_change_of_variables (μ : LiZhongQC.BeltramiH)
    {η : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hη : LiZhongQC.IsBeltramiCoeff η univ M)
    (hzero : ∀ ζ : ℂ, ζ.im ≤ 0 → η ζ = 0)
    {z : ℂ} (hz : z ∈ LiZhongQC.lowerHalf) :
    IntegrableOn (originalFourthKernel μ η z) LiZhongQC.upperHalf ∧
      (∫ w in upperImage μ, transportedDirection μ η w / (w - baseMap μ z) ^ 4) =
        ∫ ζ in LiZhongQC.upperHalf, originalFourthKernel μ η z ζ := by
  obtain ⟨k, hk0, hk1, hμ⟩ := μ.property.1
  have hL := transportedDirection_isBeltramiCoeff μ hk0 hk1 hμ hη
  have hL0 : 0 ≤ M / (1 - k ^ 2) := div_nonneg hM (by nlinarith)
  have hzL : baseMap μ z ∈ lowerImage μ := ⟨z, hz, rfl⟩
  have hL1 := (OffSupportCauchy.firstVariation_thirdDerivative_and_integrable
    (upperImage_isOpen μ).measurableSet hL0 hL
    (Eventually.of_forall (transportedDirection_eq_zero_off_upperImage μ hzero))
    (lowerImage_subset_interior_compl_upperImage μ hzL)).1
  let G : ℂ → ℂ := (upperImage μ).indicator
    (fun w => transportedDirection μ η w / (w - baseMap μ z) ^ 4)
  have hG : Integrable G volume :=
    (integrable_indicator_iff (upperImage_isOpen μ).measurableSet).2 hL1
  have hkey : (fun ζ => (LiZhongQC.jacobian (baseMap μ) ζ : ℂ) * G (baseMap μ ζ)) =ᵐ[volume]
      LiZhongQC.upperHalf.indicator (originalFourthKernel μ η z) := by
    filter_upwards [jacobian_mul_transportedDirection_forward_ae (μ := μ) (η := η)] with ζ hζ
    by_cases hζU : ζ ∈ LiZhongQC.upperHalf
    · have hζD : baseMap μ ζ ∈ upperImage μ := ⟨ζ, hζU, rfl⟩
      dsimp only [G]
      rw [indicator_of_mem hζD, indicator_of_mem hζU, ← mul_div_assoc, hζ]
      rfl
    · have hζD : baseMap μ ζ ∉ upperImage μ := by
        rintro ⟨v, hv, he⟩
        exact hζU ((baseMap_injective μ he) ▸ hv)
      dsimp only [G]
      rw [indicator_of_notMem hζD, indicator_of_notMem hζU, mul_zero]
  have hraw : Integrable (LiZhongQC.upperHalf.indicator (originalFourthKernel μ η z)) volume :=
    (integrable_jacobian_mul_base μ hG).congr hkey
  refine ⟨(integrable_indicator_iff LiZhongQC.isOpen_upperHalf.measurableSet).1 hraw, ?_⟩
  obtain ⟨K, hK⟩ := (LiZhongQC.ut_spec μ).1
  have hg := LiZhongQC.nxS_genHomeoSolution_congr
    (LiZhongQC.thm10_2_genHomeoSolution_of_isKQC hK).2
    (by simpa only [Measure.restrict_univ] using (LiZhongQC.ut_spec μ).2.2.2.2)
  obtain ⟨hfh, fx, fy, hfd, hfb⟩ := hg
  have hc := LiZhongQC.sp_c_change_of_variables hk1 isOpen_univ hμ.2 hfh hfd hfb G
  rw [(LiZhongQC.ut_spec μ).2.1, Measure.restrict_univ] at hc
  calc
    _ = ∫ w, G w := (integral_indicator (upperImage_isOpen μ).measurableSet).symm
    _ = ∫ ζ, (LiZhongQC.jacobian (baseMap μ) ζ : ℂ) * G (baseMap μ ζ) := hc
    _ = ∫ ζ, LiZhongQC.upperHalf.indicator (originalFourthKernel μ η z) ζ := integral_congr_ae hkey
    _ = _ := integral_indicator LiZhongQC.isOpen_upperHalf.measurableSet

end LowDimensionalTopology.Geometry.Quasiconformal.CanonicalBersVariation
