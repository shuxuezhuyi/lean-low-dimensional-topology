module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticC1ChartLength
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Finiteness of the original quadratic length for supplied finite C1 chart pieces. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

universe u
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- A supplied C1 chart piece has finite quadratic length, including at coefficient zeros. -/
theorem phiChartIntegral_lt_top_of_c1 {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {a b : S} (γ : Path a b) (x : S) {s t : ℝ}
    (hsrc : γ.extend '' Icc s t ⊆ (chartAt ℂ x).source)
    (hC1 : ContDiffOn ℝ 1 (fun v : ℝ => chartAt ℂ x (γ.extend v)) (Icc s t)) :
    (∫⁻ v in Ioo s t,
      phiDensity (q x) (chartAt ℂ x (γ.extend v)) *
        ‖deriv (fun w : ℝ => chartAt ℂ x (γ.extend w)) v‖ₑ) < ⊤ := by
  let c : ℝ → ℂ := fun v => chartAt ℂ x (γ.extend v)
  have hc : ContDiffOn ℝ 1 c (Icc s t) := hC1
  have hq' : IsDiffFamily 2 0 q ∧
      ∀ y : S, DifferentiableOn ℂ (q y) (chartAt ℂ y).target := hq
  have htarget : c '' Icc s t ⊆ (chartAt ℂ x).target := by
    rintro _ ⟨v, hv, rfl⟩
    exact (chartAt ℂ x).map_source (hsrc ⟨v, hv, rfl⟩)
  obtain ⟨K, hK⟩ := hc.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hcont : ContinuousOn (fun z : ℂ => ‖q x z‖) (c '' Icc s t) :=
    ((hq'.2 x).continuousOn.mono htarget).norm
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.image_of_continuousOn hc.continuousOn).exists_bound_of_continuousOn hcont
  change (∫⁻ v in Ioo s t, phiDensity (q x) (c v) * ‖deriv c v‖ₑ) < ⊤
  calc
    (∫⁻ v in Ioo s t, phiDensity (q x) (c v) * ‖deriv c v‖ₑ) ≤
        ∫⁻ _v in Ioo s t, ENNReal.ofReal (Real.sqrt (max C 0) * (K : ℝ)) := by
      refine setLIntegral_mono measurable_const ?_
      intro v hv
      have hd : ‖deriv c v‖ ≤ K :=
        norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hv.1 hv.2) hK
      have hρ : Real.sqrt ‖q x (c v)‖ ≤ Real.sqrt (max C 0) := by
        apply Real.sqrt_le_sqrt
        have hb := hC (c v) ⟨v, Ioo_subset_Icc_self hv, rfl⟩
        rw [Real.norm_of_nonneg (norm_nonneg _)] at hb
        exact hb.trans (le_max_left _ _)
      rw [phiDensity, ← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul hρ hd (norm_nonneg _) (Real.sqrt_nonneg _))
    _ < ⊤ := by
      rw [setLIntegral_const, Real.volume_Ioo]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- Every supplied finite C1 chart subdivision gives a finite original path length. -/
theorem phiLengthPath_lt_top_of_c1_chartSubdivision
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) {a b : S} (γ : Path a b)
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (x : Fin n → S)
    (h0 : τ 0 = 0) (hn : τ (Fin.last n) = 1) (hτ : Monotone τ)
    (hsrc : ∀ i : Fin n,
      γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source)
    (hC1 : ∀ i : Fin n, ContDiffOn ℝ 1 (fun v : ℝ => chartAt ℂ (x i) (γ.extend v))
      (Icc (τ i.castSucc) (τ i.succ))) :
    phiLengthPath q γ < ⊤ := by
  have hadm := c1_chartSubdivision_admissible γ τ x h0 hn hτ hsrc hC1
  have hle : phiLengthPath q γ ≤
      ∑ i : Fin n, ∫⁻ v in Ioo (τ i.castSucc) (τ i.succ),
        phiDensity (q (x i)) (chartAt ℂ (x i) (γ.extend v)) *
          ‖deriv (fun w : ℝ => chartAt ℂ (x i) (γ.extend w)) v‖ₑ := by
    unfold phiLengthPath phiLengthOn
    exact iInf_le_of_le n (iInf_le_of_le τ (iInf_le_of_le x (iInf_le _ hadm)))
  refine hle.trans_lt (ENNReal.sum_lt_top.2 ?_)
  intro i _
  exact phiChartIntegral_lt_top_of_c1 hq γ (x i) (hsrc i) (hC1 i)

/-- Finiteness for the native differential and original selected atlas of the given surface. -/
theorem quadraticLengthPath_lt_top_of_c1_chartSubdivision
    {X : Type u} [TopologicalSpace X] (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) {a b : X} (γ : Path a b)
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (x : Fin n → X) :
    letI := R.toRiemannAtlas.toChartedSpace
    τ 0 = 0 → τ (Fin.last n) = 1 → Monotone τ →
      (∀ i : Fin n,
        γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source) →
      (∀ i : Fin n, ContDiffOn ℝ 1 (fun v : ℝ => chartAt ℂ (x i) (γ.extend v))
        (Icc (τ i.castSucc) (τ i.succ))) →
      phiLengthPath (q : X → ℂ → ℂ) γ < ⊤ := by
  let := R.toRiemannAtlas.toChartedSpace
  intro h0 hn hτ hsrc hC1
  exact phiLengthPath_lt_top_of_c1_chartSubdivision q.property γ τ x h0 hn hτ hsrc hC1

end LowDimensionalTopology.Geometry.Teichmuller
