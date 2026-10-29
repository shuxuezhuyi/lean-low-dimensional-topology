/-
Copyright (c) 2026 Wu Xiaobin.
The normalized Ahlfors-Weill assembly adapts Wu Xiaobin's
Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2, original file
LiZhongQC/Ch10/S33_BersEmbedding.lean (the l333_core construction).
It reuses the ratio APIs from original file
LiZhongQC/Ch05/S20_SchwarzDomains.lean.
Local changes: retain the actual normalized-pair formula, prove real
analyticity by real scalar restriction and rational composition, and assemble
the canonical asymmetric normalized solution and its exact Bers inverse class
through the existing native automorphic parameter API.
Released under Apache 2.0 license as described in the file LICENSE.
See THIRD_PARTY_NOTICES.md and the retained LiZhongQC license.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeAhlforsWeillSection
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open LiZhongQC

private theorem normalized_pair_analyticOnNhd
    {w₁ w₂ H : ℂ → ℂ} {α β κ δ : ℂ}
    (hw₁ : DifferentiableOn ℂ w₁ lowerHalf)
    (hw₂ : DifferentiableOn ℂ w₂ lowerHalf)
    (hW : ∀ z ∈ lowerHalf,
      w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1)
    (hH : ∀ z ∈ upperHalf,
      mobiusExt α β κ δ (l333_E w₁ w₂ z) = ((H z : ℂ) : ExtPlane)) :
    AnalyticOnNhd ℝ H upperHalf := by
  let N₁ : ℂ → ℂ := fun z => w₁ (conj z) + (z - conj z) * deriv w₁ (conj z)
  let N₂ : ℂ → ℂ := fun z => w₂ (conj z) + (z - conj z) * deriv w₂ (conj z)
  have hME (y : ℂ) (hy : y ∈ upperHalf) :
      mobiusExt α β κ δ (l333_E w₁ w₂ y) =
        t203_ratio (α * N₁ y + β * N₂ y) (κ * N₁ y + δ * N₂ y) := by
    simpa only [l333_E, div_one, N₁, N₂] using
      (t203_c1_mobius_ratio (a := α) (b := β) (c := κ) (d := δ) (σ := 1)
        (x := N₁ y) (y := N₂ y) one_ne_zero
        (l333_mux_pair_ne (u := y - conj y) (hW (conj y) (l333_bel_conj_mem hy))))
  have hden (y : ℂ) (hy : y ∈ upperHalf) : κ * N₁ y + δ * N₂ y ≠ 0 := by
    apply t203_c1_ratio_ne
    rw [← hME y hy, hH y hy]
    exact OnePoint.coe_ne_infty _
  have hev {z : ℂ} (hz : z ∈ upperHalf) :
      H =ᶠ[𝓝 z] fun y => (α * N₁ y + β * N₂ y) / (κ * N₁ y + δ * N₂ y) := by
    filter_upwards [isOpen_upperHalf.mem_nhds hz] with y hy
    have he := congrArg extToC ((hH y hy).symm.trans (hME y hy))
    rw [t203_c1_extToC_ratio (hden y hy)] at he
    exact he
  intro z hz
  have hzL := l333_bel_conj_mem hz
  have hc : AnalyticAt ℝ (fun y : ℂ => conj y) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).analyticAt z
  have ha₁ : AnalyticAt ℝ w₁ (conj z) :=
    (hw₁.analyticAt (isOpen_lowerHalf.mem_nhds hzL)).restrictScalars
  have ha₂ : AnalyticAt ℝ w₂ (conj z) :=
    (hw₂.analyticAt (isOpen_lowerHalf.mem_nhds hzL)).restrictScalars
  have hd₁ : AnalyticAt ℝ (deriv w₁) (conj z) :=
    ((hw₁.deriv isOpen_lowerHalf).analyticAt (isOpen_lowerHalf.mem_nhds hzL)).restrictScalars
  have hd₂ : AnalyticAt ℝ (deriv w₂) (conj z) :=
    ((hw₂.deriv isOpen_lowerHalf).analyticAt (isOpen_lowerHalf.mem_nhds hzL)).restrictScalars
  have hN₁ : AnalyticAt ℝ N₁ z :=
    (ha₁.comp hc).add ((analyticAt_id.sub hc).mul (hd₁.comp hc))
  have hN₂ : AnalyticAt ℝ N₂ z :=
    (ha₂.comp hc).add ((analyticAt_id.sub hc).mul (hd₂.comp hc))
  have hn : AnalyticAt ℝ (fun y => α * N₁ y + β * N₂ y) z :=
    (analyticAt_const.mul hN₁).add (analyticAt_const.mul hN₂)
  have hd : AnalyticAt ℝ (fun y => κ * N₁ y + δ * N₂ y) z :=
    (analyticAt_const.mul hN₁).add (analyticAt_const.mul hN₂)
  exact (hn.div hd (hden z hz)).congr (hev hz).symm

/-- The actual normalized Ahlfors-Weill construction retains its two
normalized holomorphic solutions and both finite rational expressions. -/
theorem ahlforsWeill_core_normalizedPair {φ : ℂ → ℂ} {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s < 1 / 2)
    (hφd : DifferentiableOn ℂ φ lowerHalf)
    (hφ : ∀ z ∈ lowerHalf, ‖φ z‖ * z.im ^ 2 ≤ s) :
    ∃ (H : ℂ → ℂ) (K : ℝ), IsKQC H univ K ∧ H '' univ = univ ∧
      H 0 = 0 ∧ H 1 = 1 ∧ DifferentiableOn ℂ H lowerHalf ∧
      (∀ z ∈ lowerHalf, schwarzian H z = φ z) ∧
      (∀ z ∈ upperHalf, complexDilatation H z = -2 * (z.im : ℂ) ^ 2 * φ (conj z)) ∧
      AnalyticOnNhd ℝ H upperHalf ∧
      ∃ (v₁ v₂ : ℂ → ℂ) (d : ℂ), d ≠ 0 ∧
        DifferentiableOn ℂ v₁ lowerHalf ∧ DifferentiableOn ℂ v₂ lowerHalf ∧
        (∀ z ∈ lowerHalf,
          deriv (deriv v₁) z + φ z / 2 * v₁ z = 0 ∧
          deriv (deriv v₂) z + φ z / 2 * v₂ z = 0 ∧
          v₁ z * deriv v₂ z - v₂ z * deriv v₁ z = d) ∧
        (∀ z ∈ lowerHalf, v₂ z ≠ 0 ∧ H z = v₁ z / v₂ z) ∧
        (∀ z ∈ upperHalf,
          v₂ (conj z) + (z - conj z) * deriv v₂ (conj z) ≠ 0 ∧
          H z = (v₁ (conj z) + (z - conj z) * deriv v₁ (conj z)) /
            (v₂ (conj z) + (z - conj z) * deriv v₂ (conj z))) := by
  obtain ⟨w₁, w₂, hw₁, hw₂, hode, hloc, hSf, hmero⟩ := l333_ode hφd
  obtain ⟨hfam, hconv⟩ := l333_family hs0 hs hφ hw₁ hw₂ hode
  obtain ⟨hdisc, hmono, hU⟩ := l333_disc_facts
  have hk0 : 0 ≤ 4 * s / 2 := by positivity
  have hk1 : 4 * s / 2 < 1 := by linarith
  obtain ⟨G, A, T, h, hA, hT, hh, hhs, hG, hGD, hGlim⟩ :=
    l333_limit (D := lowerHalf) (f := fun z => w₁ z / w₂ z)
      (Dn := l333_disc) (F := l333_F w₁ w₂) hk0 hk1 le_rfl
      ⟨-I, by simp [lowerHalf]⟩ isOpen_lowerHalf hmono (fun n => (hdisc n).2.1) hU
      fun n => ⟨(hfam n).1, (hfam n).2.1,
        fun z hz => ((hfam n).2.2.1 z hz).trans
          (hmero z ((hdisc n).2.2.2.1 (subset_closure hz))).symm, (hfam n).2.2.2⟩
  obtain ⟨α, β, κ, δ, hdet, H, hH, hHs, hH0, hH1, hM⟩ :=
    l333_normalize hA hT hh hhs hG
  have hGv : ∀ v ∈ lowerHalf,
      mobiusExt α β κ δ (meroToExt (fun z => w₁ z / w₂ z) v) =
        ((H v : ℂ) : ExtPlane) := by
    intro v hv
    rw [← hGD v hv, hM]
    rfl
  have hEH : ∀ y ∈ upperHalf,
      mobiusExt α β κ δ (l333_E w₁ w₂ y) = ((H y : ℂ) : ExtPlane) := by
    intro y hy
    rw [← hGlim y _ (hconv y hy), hM]
    rfl
  refine ⟨H, (1 + 4 * s / 2) / (1 - 4 * s / 2), hH, hHs, hH0, hH1,
    fun v hv => (aw_ext_analyticAt isOpen_lowerHalf hloc hGv hv).differentiableAt.differentiableWithinAt,
    fun v hv => (aw_ext_schwarzian isOpen_lowerHalf hloc hdet hGv hv).trans (hSf v hv),
    fun z hz => l333_mu_exact hdet hw₁ hw₂ hode hEH hz,
    normalized_pair_analyticOnNhd hw₁ hw₂ (fun z hz => (hode z hz).2.2) hEH, ?_⟩
  let v₁ : ℂ → ℂ := fun z => α * w₁ z + β * w₂ z
  let v₂ : ℂ → ℂ := fun z => κ * w₁ z + δ * w₂ z
  have hv₁ : DifferentiableOn ℂ v₁ lowerHalf := (hw₁.const_mul α).add (hw₂.const_mul β)
  have hv₂ : DifferentiableOn ℂ v₂ lowerHalf := (hw₁.const_mul κ).add (hw₂.const_mul δ)
  refine ⟨v₁, v₂, α * δ - β * κ, hdet, hv₁, hv₂, ?_, ?_, ?_⟩
  · intro z hz
    have h₁ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ α β hz
    have h₂ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ κ δ hz
    refine ⟨?_, ?_, ?_⟩
    · change deriv (deriv fun y => α * w₁ y + β * w₂ y) z +
        φ z / 2 * (α * w₁ z + β * w₂ z) = 0
      rw [h₁.2]
      linear_combination α * (hode z hz).1 + β * (hode z hz).2.1
    · change deriv (deriv fun y => κ * w₁ y + δ * w₂ y) z +
        φ z / 2 * (κ * w₁ z + δ * w₂ z) = 0
      rw [h₂.2]
      linear_combination κ * (hode z hz).1 + δ * (hode z hz).2.1
    · dsimp only [v₁, v₂]
      rw [h₁.1, h₂.1]
      exact neh_wronskian_comb (hode z hz).2.2
  · intro z hz
    have hne : w₁ z ≠ 0 ∨ w₂ z ≠ 0 := by
      simpa only [zero_mul, add_zero] using
        (l333_mux_pair_ne (u := 0) (hode z hz).2.2)
    have hME : mobiusExt α β κ δ (meroToExt (fun y => w₁ y / w₂ y) z) =
        t203_ratio (v₁ z) (v₂ z) := by
      rw [hmero z hz]
      simpa only [v₁, v₂, div_one] using
        (t203_c1_mobius_ratio (a := α) (b := β) (c := κ) (d := δ)
          (σ := 1) one_ne_zero hne)
    have he := (hGv z hz).symm.trans hME
    have hden : v₂ z ≠ 0 :=
      t203_c1_ratio_ne (he ▸ OnePoint.coe_ne_infty (H z))
    refine ⟨hden, ?_⟩
    have hv := congrArg extToC he
    rw [t203_c1_extToC_ratio hden] at hv
    exact hv
  · intro z hz
    have hzL := l333_bel_conj_mem hz
    have h₁ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ α β hzL
    have h₂ := t203_ode_comb_deriv isOpen_lowerHalf hw₁ hw₂ κ δ hzL
    have hME : mobiusExt α β κ δ (l333_E w₁ w₂ z) =
        t203_ratio (v₁ (conj z) + (z - conj z) * deriv v₁ (conj z))
          (v₂ (conj z) + (z - conj z) * deriv v₂ (conj z)) := by
      dsimp only [l333_E, v₁, v₂]
      rw [h₁.1, h₂.1]
      rw [t203_c1_mobius_ratio (a := α) (b := β) (c := κ) (d := δ)
        (σ := 1) one_ne_zero
        (l333_mux_pair_ne (u := z - conj z) (hode (conj z) hzL).2.2)]
      simp only [div_one]
      congr 1
      · ring
      · ring
    have he := (hEH z hz).symm.trans hME
    have hden : v₂ (conj z) + (z - conj z) * deriv v₂ (conj z) ≠ 0 :=
      t203_c1_ratio_ne (he ▸ OnePoint.coe_ne_infty (H z))
    refine ⟨hden, ?_⟩
    have hv := congrArg extToC he
    rw [t203_c1_extToC_ratio hden] at hv
    exact hv

/-- The actual normalized Ahlfors-Weill map retains real analyticity on H. -/
theorem ahlforsWeill_core_realAnalytic {φ : ℂ → ℂ} {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s < 1 / 2)
    (hφd : DifferentiableOn ℂ φ lowerHalf)
    (hφ : ∀ z ∈ lowerHalf, ‖φ z‖ * z.im ^ 2 ≤ s) :
    ∃ (H : ℂ → ℂ) (K : ℝ), IsKQC H univ K ∧ H '' univ = univ ∧
      H 0 = 0 ∧ H 1 = 1 ∧ DifferentiableOn ℂ H lowerHalf ∧
      (∀ z ∈ lowerHalf, schwarzian H z = φ z) ∧
      (∀ z ∈ upperHalf, complexDilatation H z = -2 * (z.im : ℂ) ^ 2 * φ (conj z)) ∧
      AnalyticOnNhd ℝ H upperHalf := by
  obtain ⟨H, K, hK, hHs, hH0, hH1, hHd, hHS, hHμ, hHa, _⟩ :=
    ahlforsWeill_core_normalizedPair hs0 hs hφd hφ
  exact ⟨H, K, hK, hHs, hH0, hH1, hHd, hHS, hHμ, hHa⟩

/-- The full small Bers ball has an actual canonical asymmetric normalized
solution real analytic on H, in its unique original Bers inverse class. -/
theorem exists_small_bers_realAnalytic
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (φ : BersWeighted.Automorphic Γ) (hφ : ‖φ‖ < 1 / 2) :
    ∃ μ : BeltramiGamma Γ,
      AnalyticOnNhd ℝ (normalizedSolution μ.val.val) upperHalf ∧
      bersMapGamma Γ (Quotient.mk _ μ) = (φ.toSource : ℂ → ℂ) ∧
      ∀ a : TeichGamma Γ, bersMapGamma Γ a = (φ.toSource : ℂ → ℂ) →
        a = Quotient.mk _ μ := by
  let ψ : ℂ → ℂ := φ.toSource
  have hψ : ψ ∈ automorphicQD Γ := φ.toSource.property
  have hn : bersNormL ψ < ENNReal.ofReal (1 / 2 : ℝ) :=
    (BersWeighted.Automorphic.bersNormL_toSource_le φ).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : 0 < (1 / 2 : ℝ))).mpr hφ)
  obtain ⟨hle, hs0, hs⟩ := t203_t_toReal hn
  have hψs : ∀ z ∈ lowerHalf, ‖ψ z‖ * z.im ^ 2 ≤ (bersNormL ψ).toReal := by
    intro z hz
    have h1 : ENNReal.ofReal (‖ψ z‖ * z.im ^ 2) ≤ bersNormL ψ := by
      unfold bersNormL
      exact le_iSup₂_of_le z hz le_rfl
    exact (ENNReal.ofReal_le_ofReal_iff hs0).1 (h1.trans hle)
  obtain ⟨hψd, hψ0, -⟩ := id hψ
  obtain ⟨H, K, hH, hHs, hH0, hH1, hHd, hHS, hHμ, hHa⟩ :=
    ahlforsWeill_core_realAnalytic hs0 hs hψd hψs
  have hmem := l333_mu_mem hs0 hs hψd hψs
  let μ : BeltramiGamma Γ := ⟨⟨l333_mu ψ, hmem⟩, l333_mu_compat hψ⟩
  have hsol : normalizedSolution (l333_mu ψ) = H := by
    obtain ⟨hq, hsq, hq0, hq1, hd⟩ := ut_spec μ.val
    refine thm13_5_uniqueness_plane hq ⟨K, hH⟩ hsq hHs ?_ hq0 hq1 hH0 hH1
    have hnull : ∀ᵐ z : ℂ, z ∉ {w : ℂ | w.im = 0} :=
      measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
    filter_upwards [hd, hnull] with z h1 h2
    rw [h1]
    show l333_mu ψ z = complexDilatation H z
    rcases lt_or_gt_of_ne (h2 : z.im ≠ 0) with hlt | hgt
    · have hd' : DifferentiableAt ℂ H z :=
        hHd.differentiableAt (isOpen_lowerHalf.mem_nhds hlt)
      have hbar : dzbar H z = 0 := (cauchyRiemann_iff.1 hd').2
      rw [complexDilatation, hbar, zero_div]
      exact hmem.2 z hlt.le
    · rw [hHμ z hgt]
      exact indicator_of_mem (show z ∈ upperHalf from hgt) _
  have hB : bersMapGamma Γ (Quotient.mk _ μ) = ψ := by
    rw [bg_bersMapGamma_eq (μ := μ) rfl]
    funext z
    show lowerHalf.indicator (schwarzian (normalizedSolution (l333_mu ψ))) z = ψ z
    rw [hsol]
    by_cases hz : z ∈ lowerHalf
    · rw [indicator_of_mem hz, hHS z hz]
    · rw [indicator_of_notMem hz, hψ0 z hz]
  refine ⟨μ, ?_, hB, fun a ha => bersMapGamma_injective hΓ (ha.trans hB.symm)⟩
  change AnalyticOnNhd ℝ (normalizedSolution (l333_mu ψ)) upperHalf
  rw [hsol]
  exact hHa

end LowDimensionalTopology.Geometry.Teichmuller
