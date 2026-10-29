module

public import LowDimensionalTopology.Geometry.Teichmuller.HorizontalZeroJoinModelCost

/-!
# The same native path across a horizontal zero join

The original parameter and its own Lipschitz bound are retained. A genuine
normalized coordinate transports both positive horizontal phases, and the
model cost is compared with every actual native path competitor.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

/-- Two embedded horizontal ray tails of the same original native path realize
the native distance on every sufficiently small interval crossing their zero. -/
theorem native_zero_join_cost_transfer
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
      let qH := upperHalfNativeQuadratic ψ
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (δ : Path a b) {l τ r : ℝ},
        0 ≤ l → l < τ → τ < r → r ≤ 1 →
        (∃ K : NNReal, LipschitzOnWith K (fun u : ℝ => (δ.extend u : ℂ)) (Icc l r)) →
        InjOn (fun u : ℝ => (δ.extend u : ℂ)) (Icc l r) →
        ∀ (m : ℕ), 0 < m → ∀ ξ : ℂ → ℂ,
          (AnalyticAt ℂ ξ (δ.extend τ : ℂ) ∧ ξ (δ.extend τ : ℂ) = 0 ∧
            deriv ξ (δ.extend τ : ℂ) ≠ 0 ∧
            ∀ᶠ z in 𝓝 (δ.extend τ : ℂ),
              ψ z = (((m : ℂ) + 2) / 2) ^ 2 * ξ z ^ m * deriv ξ z ^ 2) →
          ∀ vL vR : ℂ, ‖vL‖ = 1 → ‖vR‖ = 1 →
            IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ)) l τ →
            IsHorizontalArc ψ (fun u : ℝ => (δ.extend u : ℂ)) τ r →
            (∀ u ∈ Icc l τ, ∃ ρ : ℝ, 0 ≤ ρ ∧
              ξ (δ.extend u : ℂ) = (ρ : ℂ) * vL) →
            (∀ u ∈ Icc τ r, ∃ ρ : ℝ, 0 ≤ ρ ∧
              ξ (δ.extend u : ℂ) = (ρ : ℂ) * vR) →
            ∃ ε > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
              τ - ε < s → s < τ → τ < t → t < τ + ε →
                phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) δ s t =
                  phiDistRS (qH : UpperHalfPlane → ℂ → ℂ) (δ.extend s) (δ.extend t) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b δ l τ r _hl hlτ hτr _hr hLip hi m hm ξ hξ vL vR hvL hvR hL hR hrL hrR
  let F : ℝ → ℂ := fun u => (δ.extend u : ℂ)
  let g : ℝ → ℂ := fun u => ξ (F u)
  let Q : ℂ → ℂ := fun w => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m
  let z₀ : UpperHalfPlane := δ.extend τ
  obtain ⟨hξa, hξ0, hξd, hξq⟩ := hξ
  obtain ⟨ρ, W, hρ, hW, hsub, han, hinj, hlower⟩ :=
    native_quadratic_model_neighborhood R q hq hp z₀ m ξ hξa hξ0 hξd hξq
  have hN : {u : ℝ | δ.extend u ∈ W ∧ F u ∈ ball (z₀ : ℂ) ρ} ∈ 𝓝 τ := by
    have hNW : {u : ℝ | δ.extend u ∈ W} ∈ 𝓝 τ :=
      δ.continuous_extend.continuousAt.preimage_mem_nhds hW
    have hNB : {u : ℝ | F u ∈ ball (z₀ : ℂ) ρ} ∈ 𝓝 τ :=
      (UpperHalfPlane.continuous_coe.comp δ.continuous_extend).continuousAt.preimage_mem_nhds
        (isOpen_ball.mem_nhds (mem_ball_self hρ))
    exact inter_mem hNW hNB
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.1 hN
  let ε : ℝ := min ε₀ (min (τ - l) (r - τ)) / 2
  have hε : 0 < ε :=
    div_pos (lt_min hε₀ (lt_min (sub_pos.mpr hlτ) (sub_pos.mpr hτr))) (by norm_num)
  have hε₀' : ε < ε₀ := by
    dsimp only [ε]
    linarith [min_le_left ε₀ (min (τ - l) (r - τ))]
  have hεl : ε ≤ τ - l := by
    have hmin := (min_le_right ε₀ (min (τ - l) (r - τ))).trans
      (min_le_left (τ - l) (r - τ))
    dsimp only [ε]
    linarith
  have hεr : ε ≤ r - τ := by
    have hmin := (min_le_right ε₀ (min (τ - l) (r - τ))).trans
      (min_le_right (τ - l) (r - τ))
    dsimp only [ε]
    linarith
  obtain ⟨K, hK⟩ := hLip
  refine ⟨ε, hε, ?_⟩
  intro s hs t ht hleft hsτ hτt hright
  have hst : s < t := hsτ.trans hτt
  have hsl : l ≤ s := by linarith
  have htr : t ≤ r := by linarith
  have hnear (u : ℝ) (hu : u ∈ Icc s t) : |u - τ| < ε := by
    apply abs_lt.mpr
    constructor <;> linarith [hu.1, hu.2]
  have hdata (u : ℝ) (hu : u ∈ Icc s t) :
      δ.extend u ∈ W ∧ F u ∈ ball (z₀ : ℂ) ρ := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    exact (hnear u hu).trans hε₀'
  have hKst : LipschitzOnWith K F (Icc s t) :=
    hK.mono (Icc_subset_Icc hsl htr)
  obtain ⟨Kξ, hKξ⟩ := s25e_comp_lipschitz isOpen_ball
    (fun z hz => (han z (ball_subset_closedBall hz)).1.differentiableAt.differentiableWithinAt)
    hKst (fun u hu => (hdata u hu).2)
  have hgi : InjOn g (Icc s t) := by
    intro u hu v hv huv
    have hF : F u = F v := hinj (ball_subset_closedBall (hdata u hu).2)
      (ball_subset_closedBall (hdata v hv).2) huv
    exact hi (Icc_subset_Icc hsl htr hu) (Icc_subset_Icc hsl htr hv) hF
  have hphase (u : ℝ) (hu : u ∈ Icc s t)
      (h : DifferentiableAt ℝ F u ∧ deriv F u ≠ 0 ∧ ψ (F u) ≠ 0 ∧
        (ψ (F u) * deriv F u ^ 2).im = 0 ∧ 0 < (ψ (F u) * deriv F u ^ 2).re) :
      DifferentiableAt ℝ g u ∧ deriv g u ≠ 0 ∧ Q (g u) ≠ 0 ∧
        (Q (g u) * deriv g u ^ 2).im = 0 ∧ 0 < (Q (g u) * deriv g u ^ 2).re := by
    obtain ⟨ha, hd, hqξ⟩ := han (F u) (ball_subset_closedBall (hdata u hu).2)
    change ψ (F u) = Q (g u) * deriv ξ (F u) ^ 2 at hqξ
    have hgd : HasDerivAt g (deriv F u * deriv ξ (F u)) u :=
      ha.differentiableAt.hasDerivAt.scomp u h.1.hasDerivAt
    have hchain : Q (g u) * deriv g u ^ 2 = ψ (F u) * deriv F u ^ 2 := by
      rw [hgd.deriv, hqξ]
      dsimp only [Q, g]
      ring
    have hQ : Q (g u) ≠ 0 := by
      intro hz
      apply h.2.2.1
      rw [hqξ]
      rw [hz, zero_mul]
    refine ⟨hgd.differentiableAt, ?_, hQ, ?_, ?_⟩
    · rw [hgd.deriv]
      exact mul_ne_zero h.2.1 hd
    · rw [hchain]
      exact h.2.2.2.1
    · rw [hchain]
      exact h.2.2.2.2
  have hML : IsHorizontalArc Q g s τ := by
    intro u hu
    exact hphase u ⟨hu.1.le, hu.2.le.trans hτt.le⟩
      (hL u ⟨hsl.trans_lt hu.1, hu.2⟩)
  have hMR : IsHorizontalArc Q g τ t := by
    intro u hu
    exact hphase u ⟨hsτ.le.trans hu.1.le, hu.2.le⟩
      (hR u ⟨hu.1, hu.2.trans_le htr⟩)
  have hrL' : ∀ u ∈ Icc s τ, ∃ d : ℝ, 0 ≤ d ∧ g u = (d : ℂ) * vL := by
    intro u hu
    exact hrL u ⟨hsl.trans hu.1, hu.2⟩
  have hrR' : ∀ u ∈ Icc τ t, ∃ d : ℝ, 0 ≤ d ∧ g u = (d : ℂ) * vR := by
    intro u hu
    exact hrR u ⟨hu.1, hu.2.trans htr⟩
  have hcost := horizontal_zero_join_model_cost m hm hsτ hτt hKξ hgi hξ0
    vL vR hvL hvR hML hMR hrL' hrR'
  apply le_antisymm
  · rw [native_quadratic_lengthOn_eq_model_integral R q hp z₀ m ξ ρ hρ hsub han hinj
      δ s t hs.1 hst ht.2 ⟨K, hKst⟩ (fun u hu => (hdata u hu).2)]
    exact hcost.2.le.trans (le_iInf fun η =>
      hlower (δ.extend s) (hdata s (left_mem_Icc.mpr hst.le)).1
        (δ.extend t) (hdata t (right_mem_Icc.mpr hst.le)).1 η)
  · obtain ⟨η, _, hη⟩ :=
      s25i_subpath_length (q := (qH : UpperHalfPlane → ℂ → ℂ)) δ hs.1 hst ht.2
    exact (iInf_le _ η).trans hη

end LowDimensionalTopology.Geometry.Teichmuller
