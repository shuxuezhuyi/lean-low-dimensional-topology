/-
Portions of the normalized cone-potential computation are adapted from
Wu Xiaobin's Li-Zhong-QC-formalization (Copyright 2026), Apache-2.0.
See THIRD_PARTY_NOTICES.md for the pinned source and retained license.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticSegmentLocalGeodesic
public import LowDimensionalTopology.Geometry.Teichmuller.HorizontalZeroJoinProngSeparation

/-!
# The exact weighted cost of two actual horizontal ray tails

The original Lipschitz parameter supplies both radial integrals. The existing
cone potential bounds every model competitor, and an existing broken radial
curve supplies the matching upper bound for the model distance.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open LiZhongQC

/-- The same embedded horizontal parameter has the sum of its endpoint radial
costs as weighted length, and realizes the actual normalized model distance. -/
theorem horizontal_zero_join_model_cost
    (m : ℕ) (hm : 0 < m) {s τ t : ℝ} (hs : s < τ) (ht : τ < t)
    {f : ℝ → ℂ} {K : NNReal} (hf : LipschitzOnWith K f (Icc s t))
    (hi : InjOn f (Icc s t)) (hτ : f τ = 0)
    (vL vR : ℂ) (hvL : ‖vL‖ = 1) (hvR : ‖vR‖ = 1)
    (hL : IsHorizontalArc
      (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) f s τ)
    (hR : IsHorizontalArc
      (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) f τ t)
    (hrL : ∀ u ∈ Icc s τ, ∃ r : ℝ, 0 ≤ r ∧ f u = (r : ℂ) * vL)
    (hrR : ∀ u ∈ Icc τ t, ∃ r : ℝ, 0 ≤ r ∧ f u = (r : ℂ) * vR) :
    let cost := ∫⁻ u in Ioo s t,
      phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) (f u) * ‖deriv f u‖ₑ
    cost = ENNReal.ofReal (‖f s‖ ^ (((m : ℝ) + 2) / 2) +
        ‖f t‖ ^ (((m : ℝ) + 2) / 2)) ∧
      cost = metricDist univ
        (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m)) (f s) (f t) := by
  classical
  let c : ℝ := ((m : ℝ) + 2) / 2
  let Q : ℂ → ℂ := fun w => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m
  let D : ℝ → ENNReal := fun u => phiDensity Q (f u) * ‖deriv f u‖ₑ
  have hc : 1 < c := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    dsimp only [c]
    linarith
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hsI : s ∈ Icc s t := ⟨le_rfl, (hs.trans ht).le⟩
  have hτI : τ ∈ Icc s t := ⟨hs.le, ht.le⟩
  have htI : t ∈ Icc s t := ⟨(hs.trans ht).le, le_rfl⟩
  have hfs0 : f s ≠ 0 := by
    intro h
    exact hs.ne (hi hsI hτI (h.trans hτ.symm))
  have hft0 : f t ≠ 0 := by
    intro h
    exact ht.ne' (hi htI hτI (h.trans hτ.symm))
  have hleft := model_ray_integral_eq_radial_increment_of_rayImage m hm hs
    (hf.mono (Icc_subset_Icc le_rfl ht.le)) (hi.mono (Icc_subset_Icc le_rfl ht.le)) vL hvL hrL
  have hright := model_ray_integral_eq_radial_increment_of_rayImage m hm ht
    (hf.mono (Icc_subset_Icc hs.le le_rfl)) (hi.mono (Icc_subset_Icc hs.le le_rfl)) vR hvR hrR
  have hcostL : (∫⁻ u in Ioo s τ, D u) = ENNReal.ofReal (‖f s‖ ^ c) := by
    change (∫⁻ u in Ioo s τ, D u) = ENNReal.ofReal (|‖f τ‖ ^ c - ‖f s‖ ^ c|) at hleft
    simpa only [hτ, norm_zero, Real.zero_rpow hc0.ne', zero_sub, abs_neg,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (f s)) c)] using hleft
  have hcostR : (∫⁻ u in Ioo τ t, D u) = ENNReal.ofReal (‖f t‖ ^ c) := by
    change (∫⁻ u in Ioo τ t, D u) = ENNReal.ofReal (|‖f t‖ ^ c - ‖f τ‖ ^ c|) at hright
    simpa only [hτ, norm_zero, Real.zero_rpow hc0.ne', sub_zero,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (f t)) c)] using hright
  have hsplit : (∫⁻ u in Ioo s t, D u) =
      (∫⁻ u in Ioo s τ, D u) + ∫⁻ u in Ioo τ t, D u := by
    rw [setLIntegral_congr Ioo_ae_eq_Ioc, setLIntegral_congr Ioo_ae_eq_Ioc,
      setLIntegral_congr Ioo_ae_eq_Ioc, ← Ioc_union_Ioc_eq_Ioc hs.le ht.le,
      lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
  have hcost : (∫⁻ u in Ioo s t, D u) = ENNReal.ofReal (‖f s‖ ^ c + ‖f t‖ ^ c) := by
    have hns := Real.rpow_nonneg (norm_nonneg (f s)) c
    rw [hsplit, hcostL, hcostR]
    exact (ENNReal.ofReal_add hns (by positivity)).symm
  have hprong := horizontal_zero_join_prong_separation m hm hs ht hf.continuousOn hi hτ
    vL vR hvL hvR hL hR hrL hrR
  obtain ⟨ρL, hρL, hfa⟩ := hrL s (left_mem_Icc.mpr hs.le)
  obtain ⟨ρR, hρR, hfb⟩ := hrR t (right_mem_Icc.mpr ht.le)
  have hratio0 : 0 ≤ ρR / ρL := div_nonneg hρR hρL
  have hratio : f t / f s = ((ρR / ρL : ℝ) : ℂ) * (vR / vL) := by
    rw [hfb, hfa]
    simpa only [Complex.ofReal_div] using
      (mul_div_mul_comm (ρR : ℂ) vR (ρL : ℂ) vL)
  have hnormV : ‖vR / vL‖ = 1 := by rw [norm_div, hvR, hvL, one_div_one]
  have hnormRatio : ‖f t / f s‖ = ρR / ρL := by
    calc
      ‖f t / f s‖ = ‖ρR / ρL‖ * ‖vR / vL‖ := by rw [hratio, norm_mul, Complex.norm_real]
      _ = (ρR / ρL) * 1 := by rw [Real.norm_of_nonneg hratio0, hnormV]
      _ = ρR / ρL := mul_one _
  have hreRatio : (f t / f s).re = (ρR / ρL) * (vR / vL).re := by
    rw [hratio, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hangle : Real.pi / c = 2 * Real.pi / ((m : ℝ) + 2) := by
    dsimp only [c]
    rw [div_div_eq_mul_div]
    ring
  have hsep : (f t / f s).re ≤ Real.cos (Real.pi / c) * ‖f t / f s‖ := by
    calc
      (f t / f s).re = (ρR / ρL) * (vR / vL).re := hreRatio
      _ ≤ (ρR / ρL) * Real.cos (2 * Real.pi / ((m : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hprong.2.2.2 hratio0
      _ = Real.cos (Real.pi / c) * ‖f t / f s‖ := by rw [hangle, hnormRatio]; ring
  let G : ℂ → ℝ := fun w =>
    if Real.cos (Real.pi / c) * ‖w / f s‖ ≤ (w / f s).re then
      ‖f s‖ ^ c * ‖(w / f s) ^ (c : ℂ) - 1‖ else ‖f s‖ ^ c + ‖w‖ ^ c
  have hGa : G (f s) = 0 := by
    have hsec : Real.cos (Real.pi / c) * ‖f s / f s‖ ≤ (f s / f s).re := by
      simpa only [div_self hfs0, norm_one, mul_one, Complex.one_re] using Real.cos_le_one (Real.pi / c)
    simp only [G, ite_eq_left hsec, div_self hfs0, Complex.one_cpow, sub_self, norm_zero, mul_zero]
  have hGb : G (f t) = ‖f s‖ ^ c + ‖f t‖ ^ c := by
    change (if Real.cos (Real.pi / c) * ‖f t / f s‖ ≤ (f t / f s).re then
      ‖f s‖ ^ c * ‖(f t / f s) ^ (c : ℂ) - 1‖ else ‖f s‖ ^ c + ‖f t‖ ^ c) = _
    by_cases hsec : Real.cos (Real.pi / c) * ‖f t / f s‖ ≤ (f t / f s).re
    · rw [ite_eq_left hsec]
      exact s25e_cone_boundary_val hc hfs0 hft0 (le_antisymm hsec hsep)
    · exact ite_eq_right hsec
  have hG : ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      |G y - G x| ≤ (c * ‖x‖ ^ (c - 1) + ε) * ‖y - x‖ := by
    intro x ε hε
    exact s25e_cone_pt hc hfs0 (G := G) (fun _ => rfl) x hε
  have hlower : ENNReal.ofReal (‖f s‖ ^ c + ‖f t‖ ^ c) ≤
      metricDist univ (phiDensity Q) (f s) (f t) := by
    unfold metricDist
    refine le_iInf₂ fun γ hγ => ?_
    have h := s25e_cone_lower m hG hGa hγ
    rw [hGb] at h
    exact h
  let r : ℝ := ‖f s‖ + ‖f t‖ + 1
  have hsa : f s ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff]
    dsimp only [r]
    linarith [norm_nonneg (f t)]
  have hta : f t ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff]
    dsimp only [r]
    linarith [norm_nonneg (f s)]
  obtain ⟨γ, hγ, hlen⟩ := s25e_apex_curve m (Nat.succ_le_of_lt hm) hsa hta
  have hγU : IsPathIn univ (f s) (f t) γ :=
    ⟨hγ.1, hγ.2.1, hγ.2.2.1, subset_univ _⟩
  have hupper : metricDist univ (phiDensity Q) (f s) (f t) ≤
      ENNReal.ofReal (‖f s‖ ^ c + ‖f t‖ ^ c) := by
    have hle : metricDist univ (phiDensity Q) (f s) (f t) ≤ phiLength Q γ :=
      iInf₂_le_of_le γ hγU le_rfl
    rw [hlen] at hle
    exact hle
  change (∫⁻ u in Ioo s t, D u) = ENNReal.ofReal (‖f s‖ ^ c + ‖f t‖ ^ c) ∧
    (∫⁻ u in Ioo s t, D u) = metricDist univ (phiDensity Q) (f s) (f t)
  exact ⟨hcost, hcost.trans (le_antisymm hlower hupper)⟩

end LowDimensionalTopology.Geometry.Teichmuller
