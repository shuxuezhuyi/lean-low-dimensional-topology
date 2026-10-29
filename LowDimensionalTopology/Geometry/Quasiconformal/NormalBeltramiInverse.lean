/-
The quasiconformal area and fixed-point potential theorems used below are due
to Wu Xiaobin, Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2. Their Apache-2.0 attribution is
retained in the external source and THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiEstimates
public import LowDimensionalTopology.Geometry.Quasiconformal.NormalBeltramiQuasiconformal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic.Ring

/-!
# Area transport and normalization at infinity for actual normal solutions

The inverse remains normal at the same prescribed exponent. Its coefficient
bound and compact essential support are derived from the original data.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- The actual Jacobian density of a quasiconformal plane homeomorphism
pushes forward to Lebesgue measure. This statement also controls nonnegative
integrals before finiteness is known. -/
theorem quasiconformal_homeomorph_map_jacobian
    (e : ℂ ≃ₜ ℂ) {K : ℝ} (he : IsKQC e univ K) :
    Measure.map e (volume.withDensity (fun z => ENNReal.ofReal (jacobian e z))) = volume := by
  ext s hs
  rw [Measure.map_apply e.continuous.measurable hs,
    withDensity_apply _ (hs.preimage e.continuous.measurable)]
  have harea := thm9_6_absolutelyContinuous he
    (hs.preimage e.continuous.measurable) (subset_univ _)
  rw [e.image_preimage] at harea
  exact harea.symm

/-- Weighted area change of variables for any measurable nonnegative weight,
without an integrability assumption on either side. -/
theorem quasiconformal_homeomorph_lintegral
    (e : ℂ ≃ₜ ℂ) {K : ℝ} (he : IsKQC e univ K)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ w, g w) = ∫⁻ z, ENNReal.ofReal (jacobian e z) * g (e z) := by
  have hJ : Measurable (fun z => ENNReal.ofReal (jacobian e z)) :=
    (((measurable_dz e).norm.pow_const 2).sub
      ((measurable_dzbar e).norm.pow_const 2)).ennreal_ofReal
  calc
    _ = ∫⁻ w, g w ∂Measure.map e
        (volume.withDensity (fun z => ENNReal.ofReal (jacobian e z))) := by
      rw [quasiconformal_homeomorph_map_jacobian e he]
    _ = ∫⁻ z, g (e z) ∂volume.withDensity
        (fun z => ENNReal.ofReal (jacobian e z)) :=
      lintegral_map hg e.continuous.measurable
    _ = _ := lintegral_withDensity_eq_lintegral_mul volume hJ
      (hg.comp e.continuous.measurable)

/-- Every actual normal solution for a compactly essentially supported
coefficient has the same affine normalization at infinity. No growth or
homeomorphism premise is added. -/
theorem normalLpSolution_tendsto_div_one
    {μ f : ℂ → ℂ} {k p : ℝ} (hp : 2 < p)
    (hμ : IsBeltramiCoeff μ univ k)
    (hμLp : MemLp μ (ENNReal.ofReal p) (volume : Measure ℂ))
    (hcomp : HasCompactEssentialSupport μ) (hf : IsNormalLpSolution μ f p) :
    Tendsto (fun z => f z / z) (cocompact ℂ) (𝓝 1) := by
  obtain ⟨ω, hω, hfixed, hrepr⟩ := normalLpSolution_representation hp hμ hμLp hf
  obtain ⟨K, hK, hzero⟩ := hcomp
  let ν : ℂ → ℂ := K.indicator μ
  have hν : ν =ᵐ[volume] μ := by
    filter_upwards [hzero] with z hz
    by_cases hzK : z ∈ K
    · exact indicator_of_mem hzK _
    · change K.indicator μ z = μ z
      rw [indicator_of_notMem hzK, hz hzK]
  obtain ⟨R, hRpos, hRK⟩ := hK.isBounded.exists_pos_norm_le
  have hνSupp : ∀ z, R < ‖z‖ → ν z = 0 := by
    intro z hz
    exact indicator_of_notMem (fun hzK => (not_le_of_gt hz) (hRK z hzK)) _
  have hνFixed : ω =ᵐ[volume] fun z => ν z * hilbertH ω z + ν z := by
    filter_upwards [hfixed, hν] with z hz hνz
    simpa only [hνz] using hz
  have hP := normalizedCauchyPotential_eq_cauchyT_sub_of_fixedPoint hp hω hνSupp hνFixed
  have hfshift : f = fun z => (z + cauchyT ω z) - cauchyT ω 0 := by
    rw [hrepr, hP]
    funext z
    dsimp only
    ring
  have hraw := t2_tendsto_div_one hp hRpos hνSupp hω hνFixed
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hlim := hraw.sub (hinv.const_mul (cauchyT ω 0))
  simp only [mul_zero, sub_zero] at hlim
  refine hlim.congr fun z => ?_
  rw [hfshift, sub_div, div_eq_mul_inv (cauchyT ω 0)]

/-- The inverse of the same actual plane homeomorphism retains the affine
normalization at infinity. -/
theorem homeomorph_inverse_tendsto_div_one
    (e : ℂ ≃ₜ ℂ)
    (he : Tendsto (fun z => e z / z) (cocompact ℂ) (𝓝 1)) :
    Tendsto (fun w => e.symm w / w) (cocompact ℂ) (𝓝 1) := by
  have hcomp := he.comp e.symm.map_cocompact.le
  have hlim := hcomp.inv₀ (one_ne_zero : (1 : ℂ) ≠ 0)
  simpa only [Function.comp_apply, e.apply_symm_apply, inv_div, inv_one] using hlim

/-- The same actual inverse of every normal solution is again a normal
solution at the original exponent. The inverse coefficient has the same
bound and compact essential support, all derived from the original data. -/
theorem normalLpSolution_inverse
    (μ : MeasurableBeltramiSpace)
    {f : ℂ → ℂ} {k p : ℝ} (hk : k ∈ Ico (0 : ℝ) 1) (hμk : ‖μ‖ ≤ k)
    (hcomp : HasCompactEssentialSupport (μ : ℂ → ℂ))
    (hp : 2 < p) (hsmall : k * smoothHilbertNorm p < 1)
    (hf : IsNormalLpSolution (μ : ℂ → ℂ) f p) :
    ∃ e : ℂ ≃ₜ ℂ, (e : ℂ → ℂ) = f ∧
      IsBeltramiCoeff (complexDilatation e.symm) univ k ∧
      HasCompactEssentialSupport (complexDilatation e.symm) ∧
      IsNormalLpSolution (complexDilatation e.symm) e.symm p := by
  obtain ⟨hQC, ⟨e, he⟩, hcoeff⟩ :=
    normalLpSolution_quasiconformal μ hk hμk hcomp hp hsmall hf
  have hqe : IsKQC e univ ((1 + k) / (1 - k)) := by simpa only [he] using hQC
  have hcoeq : complexDilatation e =ᵐ[volume] (μ : ℂ → ℂ) := by
    simpa only [he] using hcoeff
  have himg : e '' univ = univ := by rw [image_univ, e.surjective.range_eq]
  have hinv : Function.invFunOn e univ = e.symm := by
    funext y
    have hy : y ∈ e '' univ := by rw [himg]; exact mem_univ y
    have h1 : e (Function.invFunOn e univ y) = y := Function.invFunOn_eq hy
    rw [← h1, e.symm_apply_apply, h1]
  have hinvQC : IsKQC e.symm univ ((1 + k) / (1 - k)) := by
    simpa only [hinv, himg] using thm7_2_inv hqe
  let ν : ℂ → ℂ := complexDilatation e.symm
  have hinvFormula : ∀ᵐ z ∂(volume : Measure ℂ),
      ν (e z) = -(μ z) * (dz e z / conj (dz e z)) := by
    have h := eq13_5_7_inverse hqe
    rw [Measure.restrict_univ, hinv] at h
    filter_upwards [h, hcoeq] with z hz hμz
    exact hz.2.2.trans (by rw [hμz])
  have hμbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k := by
    filter_upwards [lpInfinity_norm_ae_le μ] with z hz
    exact hz.trans hμk
  have hνboundForward : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν (e z)‖ ≤ k := by
    filter_upwards [hinvFormula, hμbound] with z hz hμz
    rw [hz, norm_mul, norm_neg]
    calc
      _ ≤ ‖μ z‖ * 1 :=
        mul_le_mul_of_nonneg_left (ahT_norm_div_conj_le (dz e z)) (norm_nonneg _)
      _ ≤ k := by simpa only [mul_one] using hμz
  have hνbound : ∀ᵐ w ∂(volume : Measure ℂ), ‖ν w‖ ≤ k := by
    have hb := abT_ae_image hqe (p := fun w => ‖ν w‖ ≤ k)
      (by simpa only [Measure.restrict_univ] using hνboundForward)
    simpa only [himg, Measure.restrict_univ] using hb
  have hνCoeff : IsBeltramiCoeff ν univ k := by
    refine ⟨?_, ?_⟩
    · change AEStronglyMeasurable (complexDilatation e.symm) (volume.restrict univ)
      exact ((measurable_dzbar e.symm).div (measurable_dz e.symm)).aestronglyMeasurable
    · simpa only [Measure.restrict_univ] using hνbound
  obtain ⟨K, hK, hzero⟩ := hcomp
  have hνzeroForward : ∀ᵐ z ∂(volume : Measure ℂ), e z ∉ e '' K → ν (e z) = 0 := by
    filter_upwards [hinvFormula, hzero] with z hz hμz
    intro hzK
    have hzNotK : z ∉ K := fun hz' => hzK ⟨z, hz', rfl⟩
    rw [hz, hμz hzNotK, neg_zero, zero_mul]
  have hνzero : ∀ᵐ w ∂(volume : Measure ℂ), w ∉ e '' K → ν w = 0 := by
    have hb := abT_ae_image hqe (p := fun w => w ∉ e '' K → ν w = 0)
      (by simpa only [Measure.restrict_univ] using hνzeroForward)
    simpa only [himg, Measure.restrict_univ] using hb
  have hνcomp : HasCompactEssentialSupport ν := ⟨e '' K, hK.image e.continuous, hνzero⟩
  let νLp := MeasurableBeltramiBall.coefficientMemLp hνCoeff
  let γ : MeasurableBeltramiSpace := νLp.toLp ν
  have hγ : (γ : ℂ → ℂ) =ᵐ[volume] ν := νLp.coeFn_toLp
  have hγk : ‖γ‖ ≤ k := by
    apply lpInfinity_norm_le_of_ae_bound γ hk.1
    filter_upwards [hγ, hνbound] with z hz hb
    rw [hz]
    exact hb
  have hγcomp : HasCompactEssentialSupport (γ : ℂ → ℂ) :=
    (hasCompactEssentialSupport_congr_ae hγ).mpr hνcomp
  have hνLp : MemLp ν (ENNReal.ofReal p) (volume : Measure ℂ) :=
    MemLp.ae_eq hγ
      (measurableBeltrami_memLp_of_compactEssentialSupport γ hγcomp (ENNReal.ofReal p))
  obtain ⟨N, hN, -⟩ := existsUnique_normalLpSolution_of_memLp hk.1 hp hνCoeff hνLp hsmall
  have hγN : IsNormalLpSolution (γ : ℂ → ℂ) N p :=
    (isNormalLpSolution_congr_coefficient_ae hγ).mpr hN
  obtain ⟨hNQC, -, hNcoeff⟩ :=
    normalLpSolution_quasiconformal γ hk hγk hγcomp hp hsmall hγN
  have hμCoeff : IsBeltramiCoeff (μ : ℂ → ℂ) univ k := by
    refine ⟨(MeasurableBeltramiSpace.isBeltramiCoeff μ).1, ?_⟩
    simpa only [Measure.restrict_univ] using hμbound
  have hμLp := measurableBeltrami_memLp_of_compactEssentialSupport μ
    ⟨K, hK, hzero⟩ (ENNReal.ofReal p)
  have hflim := normalLpSolution_tendsto_div_one hp hμCoeff hμLp ⟨K, hK, hzero⟩ hf
  have helim : Tendsto (fun z => e z / z) (cocompact ℂ) (𝓝 1) := by
    simpa only [he] using hflim
  have hνlim := homeomorph_inverse_tendsto_div_one e helim
  have hNlim := normalLpSolution_tendsto_div_one hp hνCoeff hνLp hνcomp hN
  have he0 : e 0 = 0 := by rw [he]; exact hf.2.1
  have hinv0 : e.symm 0 = 0 := by
    apply e.injective
    simp only [e.apply_symm_apply, he0]
  let ρ : ℂ → ℂ := (e '' K).indicator ν
  have hρ : ρ =ᵐ[volume] ν := by
    filter_upwards [hνzero] with w hw
    by_cases hwK : w ∈ e '' K
    · exact indicator_of_mem hwK _
    · change (e '' K).indicator ν w = ν w
      rw [indicator_of_notMem hwK, hw hwK]
  have hρCoeff : IsBeltramiCoeff ρ univ k :=
    (planar_isBeltramiCoeff_congr_ae hρ).mpr hνCoeff
  obtain ⟨R, -, hRK⟩ := (hK.image e.continuous).isBounded.exists_pos_norm_le
  have hρSupp : ∀ w, R < ‖w‖ → ρ w = 0 := by
    intro w hw
    exact indicator_of_notMem (fun hwK => (not_le_of_gt hw) (hRK w hwK)) _
  have hρCompact : IsCompactBeltramiCoeff ρ k := ⟨hρCoeff, R, hρSupp⟩
  have hNρ : complexDilatation N =ᵐ[volume] ρ :=
    hNcoeff.trans (hγ.trans hρ.symm)
  have hEq : (e.symm : ℂ → ℂ) = N :=
    thm12_2_unique hk.1 hk.2 hρCompact ⟨_, hinvQC⟩ ⟨_, hNQC⟩
      hρ.symm hNρ hνlim hNlim hinv0 hN.2.1
  refine ⟨e, he, hνCoeff, hνcomp, ?_⟩
  exact (congrArg (fun m : ℂ → ℂ => IsNormalLpSolution ν m p) hEq).mpr hN

end LowDimensionalTopology.Geometry.Quasiconformal
