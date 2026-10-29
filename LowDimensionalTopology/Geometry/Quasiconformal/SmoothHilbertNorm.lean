/-
The singular-integral estimates and their density extension are due to
Wu Xiaobin's Li-Zhong-QC-formalization, commit
1c0d5473c020b66ed5106331a38a61536760b9b2, with retained attribution.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.HilbertLpOperator
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# The smooth unit-sphere definition of the Hilbert operator norm

The norm is defined by the actual smooth compactly supported unit inputs.
An explicit normalized bump supplies a unit input. Rescaling each nonzero
smooth test then identifies this supremum with the actual Lp operator norm.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The supremum of the actual singular-transform norms on smooth compact
inputs of Lp norm one. Both norms use planar Lebesgue measure. -/
def smoothHilbertNorm (p : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ h : ℂ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
    (eLpNorm h (ENNReal.ofReal p) (volume : Measure ℂ)).toReal = 1 ∧
      a = (eLpNorm (hilbertHSmooth h) (ENNReal.ofReal p) (volume : Measure ℂ)).toReal}

private theorem toReal_eLpNorm_const_mul (c : ℂ) (h : ℂ → ℂ) (p : ℝ≥0∞) :
    (eLpNorm (fun z => c * h z) p (volume : Measure ℂ)).toReal =
      ‖c‖ * (eLpNorm h p (volume : Measure ℂ)).toReal := by
  rw [show (fun z => c * h z) = c • h from rfl, eLpNorm_const_smul,
    ENNReal.toReal_mul, toReal_enorm]

/-- A genuine normalized bump gives a smooth compact unit input in every
finite Lp space with positive exponent. -/
theorem exists_smooth_compact_unit_memLp {p : ℝ} (hp : 0 < p) :
    ∃ h : ℂ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      (eLpNorm h (ENNReal.ofReal p) (volume : Measure ℂ)).toReal = 1 := by
  let b : ℂ → ℂ := fun z => ((lemma92Bump 0).normed volume z : ℂ)
  have hb : ContDiff ℝ ∞ b :=
    Complex.ofRealCLM.contDiff.comp
      ((lemma92Bump 0).contDiff_normed (μ := volume) (n := ⊤))
  have hbc : HasCompactSupport b :=
    (lemma92Bump 0).hasCompactSupport_normed.comp_left (g := fun x : ℝ => (x : ℂ)) rfl
  have hbm : MemLp b (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hb.continuous.memLp_of_hasCompactSupport hbc
  have hbint : (∫ z, b z) = (1 : ℂ) := by
    change (∫ z, ((lemma92Bump 0).normed volume z : ℂ)) = 1
    rw [integral_complex_ofReal, (lemma92Bump 0).integral_normed, Complex.ofReal_one]
  have hbne : eLpNorm b (ENNReal.ofReal p) (volume : Measure ℂ) ≠ 0 := by
    intro hz
    have hzero : b =ᵐ[volume] (0 : ℂ → ℂ) :=
      (eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.mpr hp).ne').mp hz
    have hint : (∫ z, b z) = (0 : ℂ) := by
      simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hzero
    exact one_ne_zero (hbint.symm.trans hint)
  let N : ℝ := (eLpNorm b (ENNReal.ofReal p) (volume : Measure ℂ)).toReal
  have hN : 0 < N := ENNReal.toReal_pos hbne hbm.eLpNorm_ne_top
  have hc : ‖((N : ℂ)⁻¹)‖ = N⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  refine ⟨fun z => (N : ℂ)⁻¹ * b z, contDiff_const.mul hb, hbc.mul_left, ?_⟩
  rw [toReal_eLpNorm_const_mul, hc]
  exact inv_mul_cancel₀ hN.ne'

private theorem smooth_hilbert_real_norm_bound {p : ℝ} (hp : 1 < p)
    {h : ℂ → ℂ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    (eLpNorm (hilbertHSmooth h) (ENNReal.ofReal p) (volume : Measure ℂ)).toReal ≤
      hilbertNorm p * (eLpNorm h (ENNReal.ofReal p) (volume : Measure ℂ)).toReal := by
  have hm : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ) :=
    hh.continuous.memLp_of_hasCompactSupport hc
  have hb := eq11_16 hp hm
  rwa [eLpNorm_congr_ae (hilbertH_eq_ae_smooth hh hc)] at hb

/-- The smooth unit-input set is nonempty; no unit-sphere density is assumed. -/
theorem smoothHilbertNorm_set_nonempty {p : ℝ} (hp : 0 < p) :
    {a : ℝ | ∃ h : ℂ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
      (eLpNorm h (ENNReal.ofReal p) (volume : Measure ℂ)).toReal = 1 ∧
        a = (eLpNorm (hilbertHSmooth h) (ENNReal.ofReal p)
          (volume : Measure ℂ)).toReal}.Nonempty := by
  obtain ⟨h, hh, hc, hn⟩ := exists_smooth_compact_unit_memLp hp
  exact ⟨_, h, hh, hc, hn, rfl⟩

/-- The literal smooth unit-sphere supremum equals the all-Lp norm-ratio
supremum, by the actual smooth bound and explicit scalar normalization. -/
theorem smoothHilbertNorm_eq_hilbertNorm {p : ℝ} (hp : 1 < p) :
    smoothHilbertNorm p = hilbertNorm p := by
  let S : Set ℝ := {a : ℝ | ∃ h : ℂ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
    (eLpNorm h (ENNReal.ofReal p) (volume : Measure ℂ)).toReal = 1 ∧
      a = (eLpNorm (hilbertHSmooth h) (ENNReal.ofReal p) (volume : Measure ℂ)).toReal}
  have hbound : ∀ a ∈ S, a ≤ hilbertNorm p := by
    rintro a ⟨h, hh, hc, hn, rfl⟩
    simpa only [hn, mul_one] using smooth_hilbert_real_norm_bound hp hh hc
  have hSb : BddAbove S := ⟨hilbertNorm p, hbound⟩
  have hSn : S.Nonempty := smoothHilbertNorm_set_nonempty (lt_trans one_pos hp)
  have hA : 0 ≤ smoothHilbertNorm p := by
    apply Real.sSup_nonneg
    rintro a ⟨h, -, -, -, rfl⟩
    exact ENNReal.toReal_nonneg
  apply le_antisymm
  · exact csSup_le hSn hbound
  · apply hilbertNorm_le_of_smooth_bound hp hA
    intro h hh hc
    have hm : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ) :=
      hh.continuous.memLp_of_hasCompactSupport hc
    by_cases hz : eLpNorm h (ENNReal.ofReal p) (volume : Measure ℂ) = 0
    · have hb := hilbertHSmooth_le_hilbertNorm hp h hh hc
      rw [hz, mul_zero] at hb
      rw [hz, mul_zero]
      exact hb
    · let N : ℝ := (eLpNorm h (ENNReal.ofReal p) (volume : Measure ℂ)).toReal
      have hN : 0 < N := ENNReal.toReal_pos hz hm.eLpNorm_ne_top
      let c : ℂ := (N : ℂ)⁻¹
      let ψ : ℂ → ℂ := fun z => c * h z
      have hcN : ‖c‖ = N⁻¹ := by
        rw [show c = (N : ℂ)⁻¹ from rfl, norm_inv, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hN]
      have hψ : ContDiff ℝ ∞ ψ := contDiff_const.mul hh
      have hcψ : HasCompactSupport ψ := hc.mul_left
      have hunit : (eLpNorm ψ (ENNReal.ofReal p) (volume : Measure ℂ)).toReal = 1 := by
        rw [show ψ = (fun z => c * h z) from rfl, toReal_eLpNorm_const_mul, hcN]
        exact inv_mul_cancel₀ hN.ne'
      have hψbound :
          (eLpNorm (hilbertHSmooth ψ) (ENNReal.ofReal p) (volume : Measure ℂ)).toReal ≤
            smoothHilbertNorm p := le_csSup hSb ⟨ψ, hψ, hcψ, hunit, rfl⟩
      have hscaled :
          (eLpNorm (hilbertHSmooth ψ) (ENNReal.ofReal p) (volume : Measure ℂ)).toReal =
            N⁻¹ * (eLpNorm (hilbertHSmooth h) (ENNReal.ofReal p)
              (volume : Measure ℂ)).toReal := by
        rw [show ψ = (fun z => c * h z) from rfl, hilbertHSmooth_smul c hh hc,
          toReal_eLpNorm_const_mul, hcN]
      rw [hscaled] at hψbound
      have hreal :
          (eLpNorm (hilbertHSmooth h) (ENNReal.ofReal p) (volume : Measure ℂ)).toReal ≤
            smoothHilbertNorm p * N := by
        calc (eLpNorm (hilbertHSmooth h) (ENNReal.ofReal p) (volume : Measure ℂ)).toReal
            = N * (N⁻¹ *
                (eLpNorm (hilbertHSmooth h) (ENNReal.ofReal p) (volume : Measure ℂ)).toReal) := by
                  rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
          _ ≤ N * smoothHilbertNorm p := mul_le_mul_of_nonneg_left hψbound hN.le
          _ = smoothHilbertNorm p * N := mul_comm _ _
      have hreal' :
          (eLpNorm (hilbertHSmooth h) (ENNReal.ofReal p) (volume : Measure ℂ)).toReal ≤
            smoothHilbertNorm p *
              (eLpNorm h (ENNReal.ofReal p) (volume : Measure ℂ)).toReal := hreal
      have he := ENNReal.ofReal_le_ofReal hreal'
      have hHfin := (hilbertHSmooth_memLp hh hc hp).eLpNorm_ne_top
      rwa [ENNReal.ofReal_toReal hHfin, ENNReal.ofReal_mul hA,
        ENNReal.ofReal_toReal hm.eLpNorm_ne_top] at he

/-- The smooth-input supremum is the exact norm of the genuine Lp operator. -/
theorem norm_hilbertLp_eq_smoothHilbertNorm {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) : ‖hilbertLp hp‖ = smoothHilbertNorm p :=
  (norm_hilbertLp hp).trans (smoothHilbertNorm_eq_hilbertNorm hp).symm

/-- The literal smooth-input norm at exponent two equals one. -/
theorem smoothHilbertNorm_two : smoothHilbertNorm 2 = 1 := by
  rw [smoothHilbertNorm_eq_hilbertNorm one_lt_two, LiZhongQC.thm11_3_cor1]

/-- The literal smooth-input norms are continuous for every p>1. -/
theorem smoothHilbertNorm_continuousOn : ContinuousOn smoothHilbertNorm (Ioi 1) :=
  LiZhongQC.hilbertNorm_continuousOn.congr fun _ hp => smoothHilbertNorm_eq_hilbertNorm hp

/-- The same literal norms tend to one as the exponent tends to two. -/
theorem smoothHilbertNorm_tendsto_two : Tendsto smoothHilbertNorm (𝓝 2) (𝓝 1) := by
  have h := smoothHilbertNorm_continuousOn.continuousAt (Ioi_mem_nhds one_lt_two)
  rwa [ContinuousAt, smoothHilbertNorm_two] at h

end LowDimensionalTopology.Geometry.Quasiconformal
