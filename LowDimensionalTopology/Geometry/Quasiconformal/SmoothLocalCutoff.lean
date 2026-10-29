/-
Cutoff construction adapted from Wu Xiaobin's Li-Zhong-QC-formalization,
commit 1c0d5473c020b66ed5106331a38a61536760b9b2, using Mathlib's smooth cutoff.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.External.LiZhongQC.Ch02.S13_Representation

/-!
# Smooth compact localization of actual approximation sequences

A single smooth cutoff, equal to one near the prescribed compact set, preserves
both the values and actual real derivatives of each approximation there.
The cutoff construction follows the existing S13 support construction, using
Mathlib's smooth cutoff theorem at infinite regularity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem exists_smooth_compact_cutoff {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧ (∀ᶠ z in 𝓝ˢ K, χ z = 1) ∧
      tsupport χ ⊆ U ∧ HasCompactSupport χ := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf1, hf0, -⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (modelWithCornersSelf ℝ ℂ) (n := ⊤) hK.isClosed hKL
  have hsmooth : ContDiff ℝ ∞ (⇑f) := contMDiff_iff_contDiff.1 f.contMDiff
  let χ : ℂ → ℂ := fun z => (f z : ℂ)
  have hχsmooth : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp hsmooth
  have hsupp : Function.support χ ⊆ L := by
    intro z hz
    by_contra hzL
    exact hz (by simp only [χ, hf0 z hzL, Complex.ofReal_zero])
  have htsupp : tsupport χ ⊆ L := closure_minimal hsupp hL.isClosed
  refine ⟨χ, hχsmooth, ?_, htsupp.trans hLU,
    hL.of_isClosed_subset (isClosed_tsupport _) htsupp⟩
  filter_upwards [hf1] with z hz
  simp only [χ, hz, Complex.ofReal_one]


/-- Actual smooth approximants may be localized compactly inside the open domain,
without changing their values or real derivatives near the chosen compact set.
The exponent is arbitrary: this support argument preserves any given Lp limit. -/
theorem smooth_compact_localization {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {fn : ℕ → ℂ → ℂ} {f fx fy : ℂ → ℂ} {p : ℝ≥0∞}
    (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
    (hval : TendstoUniformlyOn fn f atTop K)
    (hx : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn n) z 1 - fx z)
      p (volume.restrict K)) atTop (𝓝 0))
    (hy : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn n) z Complex.I - fy z)
      p (volume.restrict K)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℂ → ℂ,
      (∀ n, ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n) ∧ tsupport (φ n) ⊆ U) ∧
      (∀ n x, x ∈ K → φ n =ᶠ[𝓝 x] fn n) ∧
      TendstoUniformlyOn φ f atTop K ∧
      Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (φ n) z 1 - fx z)
        p (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (φ n) z Complex.I - fy z)
        p (volume.restrict K)) atTop (𝓝 0) := by
  obtain ⟨χ, hχ, hχ1, hχU, hχS⟩ := exists_smooth_compact_cutoff hK hU hKU
  let φ : ℕ → ℂ → ℂ := fun n z => χ z * fn n z
  have heq (n : ℕ) {x : ℂ} (hxK : x ∈ K) : φ n =ᶠ[𝓝 x] fn n := by
    filter_upwards [hχ1.filter_mono (nhds_le_nhdsSet hxK)] with z hz
    show χ z * fn n z = fn n z
    rw [hz, one_mul]
  have hder (g : ℂ → ℂ) (v : ℂ)
      (hc : Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (fn n) z v - g z)
        p (volume.restrict K)) atTop (𝓝 0)) :
      Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (φ n) z v - g z)
        p (volume.restrict K)) atTop (𝓝 0) := by
    refine hc.congr' (Eventually.of_forall fun n => ?_)
    symm
    refine eLpNorm_congr_ae ((ae_restrict_iff' hK.measurableSet).2
      (Eventually.of_forall fun z hz => ?_))
    change fderiv ℝ (φ n) z v - g z = fderiv ℝ (fn n) z v - g z
    rw [(heq n hz).fderiv_eq (𝕜 := ℝ)]
  refine ⟨φ, ?_, fun n x hxK => heq n hxK, ?_, hder fx 1 hx,
    hder fy Complex.I hy⟩
  · intro n
    exact ⟨hχ.mul (hfn n), hχS.mul_right, tsupport_mul_subset_left.trans hχU⟩
  · exact hval.congr (Eventually.of_forall fun n z hz => (heq n hz).self_of_nhds.symm)

end LowDimensionalTopology.Geometry.Quasiconformal
