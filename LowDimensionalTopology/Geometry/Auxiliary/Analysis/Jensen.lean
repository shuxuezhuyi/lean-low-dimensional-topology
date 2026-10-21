/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Jensen’s inequality

The finite real-integral version on an open interval. Convexity alone supplies a
supporting line at the expectation; differentiability is not assumed. Integrability
of the composed function is explicit because the Bochner integral is totalized.
-/

public section

open MeasureTheory Set Filter

namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis

private theorem integral_pos_of_ae_pos {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) : 0 < ∫ x, f x ∂μ := by
  have hn : 0 ≤ᵐ[μ] f := hpos.mono fun _ h => h.le
  refine lt_of_le_of_ne (integral_nonneg_of_ae hn) ?_
  intro he
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hf).mp he.symm
  obtain ⟨x, hx, hzero⟩ := (hpos.and hz).exists
  exact hx.ne' hzero

private theorem convex_supporting_line {a b m : ℝ} {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ (Ioo a b) φ) (hm : m ∈ Ioo a b) :
    ∀ y ∈ Ioo a b, φ m + derivWithin φ (Iio m) m * (y - m) ≤ φ y := by
  intro y hy
  have hm' : m ∈ interior (Ioo a b) := by simpa only [interior_Ioo] using hm
  rcases lt_trichotomy y m with hym | rfl | hmy
  · have h := hφ.slope_le_leftDeriv_of_mem_interior hy hm' hym
    rw [slope_def_field] at h
    have h' := (div_le_iff₀ (sub_pos.mpr hym)).mp h
    nlinarith
  · simp
  · have h := (hφ.leftDeriv_le_rightDeriv_of_mem_interior hm').trans
      (hφ.rightDeriv_le_slope_of_mem_interior hm' hy hmy)
    rw [slope_def_field] at h
    have h' := (le_div_iff₀ (sub_pos.mpr hmy)).mp h
    nlinarith

/-- equation, with finite integrals made explicit. -/
theorem jensen_on_open_interval {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {a b : ℝ} {f : X → ℝ} {φ : ℝ → ℝ}
    (hf : Integrable f μ) (hφf : Integrable (fun x => φ (f x)) μ)
    (hmem : ∀ᵐ x ∂μ, f x ∈ Ioo a b) (hφ : ConvexOn ℝ (Ioo a b) φ) :
    φ (∫ x, f x ∂μ) ≤ ∫ x, φ (f x) ∂μ := by
  let m := ∫ x, f x ∂μ
  have hm : m ∈ Ioo a b := by
    constructor
    · have hp := integral_pos_of_ae_pos (hf.sub (integrable_const a))
        (hmem.mono fun x hx => sub_pos.mpr hx.1)
      simp only [Pi.sub_apply] at hp
      rw [integral_sub hf (integrable_const a)] at hp
      simpa [m] using hp
    · have hp := integral_pos_of_ae_pos ((integrable_const b).sub hf)
        (hmem.mono fun x hx => sub_pos.mpr hx.2)
      simp only [Pi.sub_apply] at hp
      rw [integral_sub (integrable_const b) hf] at hp
      simpa [m] using hp
  let k := derivWithin φ (Iio m) m
  have hd : Integrable (fun x => f x - m) μ := by
    simpa only [Pi.sub_def] using hf.sub (integrable_const m)
  have hk := hd.const_mul k
  have hl : Integrable (fun x => φ m + k * (f x - m)) μ :=
    (integrable_const _).add hk
  have hle := integral_mono_ae hl hφf (hmem.mono fun x hx => convex_supporting_line hφ hm _ hx)
  rw [integral_add (integrable_const _) hk,
    integral_const_mul, integral_sub hf (integrable_const _)] at hle
  simpa [m] using hle

end LowDimensionalTopology.Geometry.Auxiliary.Analysis
