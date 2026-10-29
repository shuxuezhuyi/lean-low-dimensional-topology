/-
Portions of the positive-phase ray argument are adapted from Wu Xiaobin's
Li-Zhong-QC-formalization (Copyright 2026), released under Apache-2.0.
See THIRD_PARTY_NOTICES.md for the pinned source and retained license.
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch07.S25_QuadraticDifferentials
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Separation of the two actual horizontal rays at a zero

The same continuous embedded curve has two horizontal ray tails in one
normalized ordinary coordinate. Their positive phase and non-backtracking
force distinct characteristic directions and the concrete sector bound.
No length, minimizing property or change of parameter is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open LiZhongQC

private theorem ray_radius_data {f : ℝ → ℂ} {a b : ℝ} {v : ℂ} (hv : v ≠ 0)
    (hray : ∀ u ∈ Icc a b, ∃ ρ : ℝ, 0 ≤ ρ ∧ f u = (ρ : ℂ) * v) :
    ∀ u ∈ Icc a b, 0 ≤ (f u / v).re ∧ f u = (((f u / v).re : ℝ) : ℂ) * v := by
  intro u hu
  obtain ⟨ρ, hρ, hfu⟩ := hray u hu
  have hdiv : f u / v = (ρ : ℂ) := by
    rw [hfu, mul_div_cancel_right₀ _ hv]
  simpa only [hdiv, Complex.ofReal_re] using And.intro hρ hfu

private theorem unit_ray_pow_eq_one
    (m : ℕ) (hm : 0 < m) {a b : ℝ} (hab : a < b) {f : ℝ → ℂ}
    (hh : IsHorizontalArc (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) f a b)
    (v : ℂ) (hv : ‖v‖ = 1)
    (hray : ∀ u ∈ Icc a b, ∃ ρ : ℝ, 0 ≤ ρ ∧ f u = (ρ : ℂ) * v) :
    v ^ (m + 2) = 1 := by
  have hv0 : v ≠ 0 := by
    intro h
    have hbad : (0 : ℝ) = 1 := by simpa only [h, norm_zero] using hv
    exact zero_ne_one hbad
  let x : ℝ := (a + b) / 2
  have hx : x ∈ Ioo a b := by dsimp only [x]; constructor <;> linarith
  have hxc : x ∈ Icc a b := Ioo_subset_Icc_self hx
  obtain ⟨hfd, hfd0, hq0, him, hre⟩ := hh x hx
  let ρ : ℝ → ℝ := fun u => (f u / v).re
  have hline := ray_radius_data hv0 hray
  have hρ0 : 0 ≤ ρ x := (hline x hxc).1
  have hfx0 : f x ≠ 0 := by
    intro h
    apply hq0
    simp only [h, zero_pow hm.ne', mul_zero]
  have hρne : ρ x ≠ 0 := by
    intro h
    apply hfx0
    have hf := (hline x hxc).2
    change f x = (ρ x : ℂ) * v at hf
    simpa only [h, Complex.ofReal_zero, zero_mul] using hf
  have hρpos : 0 < ρ x := lt_of_le_of_ne hρ0 (Ne.symm hρne)
  have hfxline : f x = (ρ x : ℂ) * v := (hline x hxc).2
  let d : ℝ := (deriv f x / v).re
  have hρd : HasDerivAt ρ d x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hfd.hasDerivAt.div_const v)
  have hlineEq : f =ᶠ[𝓝 x] (fun u : ℝ => (ρ u : ℂ) * v) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with u hu
    exact (hline u (Ioo_subset_Icc_self hu)).2
  have hfdEq : deriv f x = (d : ℂ) * v := by
    rw [hlineEq.deriv_eq]
    exact (hρd.ofReal_comp.mul_const v).deriv
  have hd0 : d ≠ 0 := by
    intro h
    apply hfd0
    rw [hfdEq, h, Complex.ofReal_zero, zero_mul]
  have hdpos : 0 < d ^ 2 := sq_pos_of_ne_zero hd0
  have hA : 0 < (((m : ℝ) + 2) / 2) ^ 2 * ρ x ^ m * d ^ 2 := by positivity
  have hprod :
      (((m : ℂ) + 2) / 2) ^ 2 * f x ^ m * deriv f x ^ 2 =
        (((((m : ℝ) + 2) / 2) ^ 2 * ρ x ^ m * d ^ 2 : ℝ) : ℂ) * v ^ (m + 2) := by
    rw [hfxline, hfdEq, pow_add, mul_pow, mul_pow]
    push_cast
    ring
  have hphase : (v ^ (m + 2)).im = 0 ∧ 0 < (v ^ (m + 2)).re := by
    apply (ofReal_mul_horizontal_iff hA _).mp
    rw [← hprod]
    exact ⟨him, hre⟩
  exact eq_one_of_norm_one_of_im_zero_of_re_pos
    (by rw [norm_pow, hv, one_pow]) hphase.1 hphase.2

private theorem opposite_side_ray_directions_ne
    {s τ t : ℝ} (hs : s < τ) (ht : τ < t) {f : ℝ → ℂ}
    (hc : ContinuousOn f (Icc s t)) (hi : InjOn f (Icc s t)) (hτ : f τ = 0)
    (vL vR : ℂ) (hvL : ‖vL‖ = 1)
    (hrL : ∀ u ∈ Icc s τ, ∃ ρ : ℝ, 0 ≤ ρ ∧ f u = (ρ : ℂ) * vL)
    (hrR : ∀ u ∈ Icc τ t, ∃ ρ : ℝ, 0 ≤ ρ ∧ f u = (ρ : ℂ) * vR) :
    vL ≠ vR := by
  intro hsame
  have hv0 : vL ≠ 0 := by
    intro h
    have hbad : (0 : ℝ) = 1 := by simpa only [h, norm_zero] using hvL
    exact zero_ne_one hbad
  have hray : ∀ u ∈ Icc s t, ∃ ρ : ℝ, 0 ≤ ρ ∧ f u = (ρ : ℂ) * vL := by
    intro u hu
    rcases le_total u τ with hlu | hru
    · exact hrL u ⟨hu.1, hlu⟩
    · simpa only [hsame] using hrR u ⟨hru, hu.2⟩
  have hline := ray_radius_data hv0 hray
  let ρ : ℝ → ℝ := fun u => (f u / vL).re
  have hρc : ContinuousOn ρ (Icc s t) :=
    Complex.continuous_re.comp_continuousOn (hc.div_const vL)
  have hρi : InjOn ρ (Icc s t) := by
    intro u hu w hw heq
    apply hi hu hw
    rw [(hline u hu).2, (hline w hw).2]
    change (ρ u : ℂ) * vL = (ρ w : ℂ) * vL
    rw [heq]
  have hρτ : ρ τ = 0 := by simp only [ρ, hτ, zero_div, Complex.zero_re]
  have hsI : s ∈ Icc s t := left_mem_Icc.mpr (hs.le.trans ht.le)
  have hτI : τ ∈ Icc s t := ⟨hs.le, ht.le⟩
  have htI : t ∈ Icc s t := right_mem_Icc.mpr (hs.le.trans ht.le)
  rcases hρc.strictMonoOn_of_injOn_Icc' (hs.le.trans ht.le) hρi with hm | ha
  · have hlt := hm hsI hτI hs
    rw [hρτ] at hlt
    exact (not_lt_of_ge (hline s hsI).1) hlt
  · have hlt := ha hτI htI ht
    rw [hρτ] at hlt
    exact (not_lt_of_ge (hline t htI).1) hlt

private theorem nontrivial_root_re_le_cos (n : ℕ) (hn : 3 ≤ n) (w : ℂ)
    (hw : w ^ n = 1) (hw1 : w ≠ 1) :
    w.re ≤ Real.cos (2 * Real.pi / (n : ℝ)) := by
  let : NeZero n := ⟨by omega⟩
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨k, hk, heq⟩ := (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).eq_pow_of_pow_eq_one hw
  have hk0 : 0 < k := by
    by_contra h
    have hkz : k = 0 := by omega
    apply hw1
    simpa only [hkz, pow_zero] using heq.symm
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.succ_le_of_lt hk0)
  have hknR : (k : ℝ) ≤ (n : ℝ) - 1 := by
    have h : k + 1 ≤ n := by omega
    have h' : (k : ℝ) + 1 ≤ n := by exact_mod_cast h
    linarith
  let θ : ℝ := 2 * Real.pi * k / n
  have hwexp : w = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← heq, ← Complex.exp_nat_mul]
    congr 1
    dsimp only [θ]
    push_cast
    ring
  have hwre : w.re = Real.cos θ := by
    rw [hwexp, Complex.exp_re]
    simp
  have hlo : 2 * Real.pi / (n : ℝ) ≤ θ := by
    dsimp only [θ]
    exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hnR.le
  have hhi : θ ≤ 2 * Real.pi - 2 * Real.pi / (n : ℝ) := by
    calc
      θ ≤ 2 * Real.pi * ((n : ℝ) - 1) / n := by
        dsimp only [θ]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hknR (by positivity)) hnR.le
      _ = 2 * Real.pi - 2 * Real.pi / (n : ℝ) := by
        field_simp [hnR.ne']
  rw [hwre]
  by_cases hθ : θ ≤ Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hθ hlo
  · have hreflect : 2 * Real.pi / (n : ℝ) ≤ 2 * Real.pi - θ := by linarith
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
      (by positivity : 0 ≤ 2 * Real.pi / (n : ℝ))
      (show 2 * Real.pi - θ ≤ Real.pi by linarith) hreflect
    simpa only [Real.cos_two_pi_sub] using hcos

/-- The two actual horizontal tails of an embedded curve have distinct
characteristic ray directions and satisfy the normalized sector bound. -/
theorem horizontal_zero_join_prong_separation
    (m : ℕ) (hm : 0 < m) {s τ t : ℝ} (hs : s < τ) (ht : τ < t)
    {f : ℝ → ℂ} (hc : ContinuousOn f (Icc s t))
    (hi : InjOn f (Icc s t)) (hτ : f τ = 0)
    (vL vR : ℂ) (hvL : ‖vL‖ = 1) (hvR : ‖vR‖ = 1)
    (hL : IsHorizontalArc
      (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) f s τ)
    (hR : IsHorizontalArc
      (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) f τ t)
    (hrL : ∀ u ∈ Icc s τ, ∃ ρ : ℝ, 0 ≤ ρ ∧ f u = (ρ : ℂ) * vL)
    (hrR : ∀ u ∈ Icc τ t, ∃ ρ : ℝ, 0 ≤ ρ ∧ f u = (ρ : ℂ) * vR) :
    vL ^ (m + 2) = 1 ∧ vR ^ (m + 2) = 1 ∧ vL ≠ vR ∧
      (vR / vL).re ≤ Real.cos (2 * Real.pi / ((m : ℝ) + 2)) := by
  have hpL := unit_ray_pow_eq_one m hm hs hL vL hvL hrL
  have hpR := unit_ray_pow_eq_one m hm ht hR vR hvR hrR
  have hne := opposite_side_ray_directions_ne hs ht hc hi hτ vL vR hvL hrL hrR
  refine ⟨hpL, hpR, hne, ?_⟩
  have hvL0 : vL ≠ 0 := by
    intro h
    have hbad : (0 : ℝ) = 1 := by simpa only [h, norm_zero] using hvL
    exact zero_ne_one hbad
  have hw : (vR / vL) ^ (m + 2) = 1 := by rw [div_pow, hpR, hpL, one_div_one]
  have hw1 : vR / vL ≠ 1 := by
    intro h
    apply hne
    exact ((div_eq_one_iff_eq hvL0).mp h).symm
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    nontrivial_root_re_le_cos (m + 2) (by omega) (vR / vL) hw hw1

end LowDimensionalTopology.Geometry.Teichmuller
