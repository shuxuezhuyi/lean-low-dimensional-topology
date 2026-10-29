module

public import LowDimensionalTopology.Geometry.Teichmuller.BookTeichmullerMaps

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open LiZhongQC
universe u v
variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- At a regular source point the map and initial coefficient fix the terminal coefficient. -/
theorem terminalCoefficient_eq {f : X ≃ₜ Y} {q : X → ℂ → ℂ}
    {r₁ r₂ : Y → ℂ → ℂ} {k : ℝ}
    (h₁ : IsTeichmullerMap f q r₁ k) (h₂ : IsTeichmullerMap f q r₂ k)
    (x : X) {z : ℂ} (hz : z ∈ localMapDomain f x) (hq : q x z ≠ 0) :
    r₁ (f x) (localMapExpr f x z) = r₂ (f x) (localMapExpr f x z) := by
  let L := localMapExpr f x
  have hLc : ContinuousAt L z := by
    have hfc : ContinuousAt f ((chartAt ℂ x).symm z) := f.continuous.continuousAt
    exact ((chartAt ℂ (f x)).continuousAt hz.2).comp
      (f := fun w => f ((chartAt ℂ x).symm w))
      (hfc.comp (f := (chartAt ℂ x).symm) ((chartAt ℂ x).continuousAt_symm hz.1))
  have haux (r : Y → ℂ → ℂ) (hr : IsTeichmullerMap f q r k) :
      r (f x) (L z) * dz L z ^ 2 = (1 - (k : ℂ))⁻¹ ^ 2 * q x z := by
    obtain ⟨A, B, hA, hAd, hB, hB0, hBd, hrel⟩ := s26d_b_local hr x hz hq
    have hA0 : deriv A z ≠ 0 := by
      intro h0
      exact hq (by rw [← hAd.self_of_nhds, h0]; simp)
    have hAs := hA.hasStrictDerivAt
    have hBs := hB.hasStrictDerivAt
    have hleft := (s23_wirtinger_comp_left hLc hB.differentiableAt
      (HasStrictDerivAt.hasDerivAt (hBs.to_localInverse hB0)).differentiableAt
      (hBs.eventually_left_inverse hB0)).1
    have hright := (s23_wirtinger_comp_right (g := teichStretch k) hA.differentiableAt
      (HasStrictDerivAt.hasDerivAt (hAs.to_localInverse hA0)).differentiableAt
      (hAs.eventually_left_inverse hA0) (hAs.eventually_right_inverse hA0)).1
    have he : B ∘ L =ᶠ[𝓝 z] teichStretch k ∘ A := hrel
    have hdz : dz (B ∘ L) z = dz (teichStretch k ∘ A) z := by
      simp only [dz, he.fderiv_eq (𝕜 := ℝ)]
    have hlin : deriv B (L z) * dz L z = (1 - (k : ℂ))⁻¹ * deriv A z := by
      rw [← hleft, hdz, hright, (s26b_teichStretch_dz_dzbar k (A z)).1]
    calc
      r (f x) (L z) * dz L z ^ 2 = (deriv B (L z) * dz L z) ^ 2 := by
        rw [mul_pow, hBd.self_of_nhds]
      _ = (1 - (k : ℂ))⁻¹ ^ 2 * q x z := by rw [hlin, mul_pow, hAd.self_of_nhds]
  have hc : (1 - (k : ℂ))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast (sub_pos.mpr h₁.k_lt_one).ne'
  have hd : dz L z ≠ 0 := by
    intro h0
    have he := haux r₁ h₁
    rw [h0, zero_pow two_ne_zero, mul_zero] at he
    exact (mul_ne_zero (pow_ne_zero 2 hc) hq) he.symm
  exact mul_right_cancel₀ (pow_ne_zero 2 hd) ((haux r₁ h₁).trans (haux r₂ h₂).symm)

/-- On the original connected surfaces a fixed Teichmüller map has a unique terminal differential. -/
theorem terminalDifferential_unique [ConnectedSpace X] [T1Space X]
    [ConnectedSpace Y] [T1Space Y] {f : X ≃ₜ Y} {q : X → ℂ → ℂ}
    {r₁ r₂ : Y → ℂ → ℂ} {k : ℝ}
    (h₁ : IsTeichmullerMap f q r₁ k) (h₂ : IsTeichmullerMap f q r₂ k) : r₁ = r₂ := by
  classical
  by_contra hne
  have hδ : IsHolQuadDiff (r₁ - r₂) :=
    (holQuadDiffSubmodule Y).sub_mem h₁.terminal h₂.terminal
  obtain ⟨p₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨p, hp⟩ := (s26d_a_frequently_regular h₁.initial h₁.initial_ne p₀).exists
  have hqhol : IsDiffFamily 2 0 q ∧ ∀ x, DifferentiableOn ℂ (q x) (chartAt ℂ x).target :=
    h₁.initial
  have hqc : ContinuousAt (q p) (chartAt ℂ p p) :=
    ((hqhol.2 p).differentiableAt ((chartAt ℂ p).open_target.mem_nhds
      ((chartAt ℂ p).map_source (mem_chart_source ℂ p)))).continuousAt
  have hback : Tendsto f.symm (𝓝 (f p)) (𝓝 p) := by
    have hsc : ContinuousAt f.symm (f p) := f.symm.continuous.continuousAt
    simpa only [f.symm_apply_apply] using hsc.tendsto
  have hchart := ((chartAt ℂ p).continuousAt (mem_chart_source ℂ p)).tendsto.comp hback
  have hev : ∀ᶠ y in 𝓝 (f p), IsRegularPoint q (f.symm y) := by
    filter_upwards [hchart.eventually (hqc.eventually_ne hp),
      hback.eventually ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))]
      with y hy hs
    have hr := (s26d_a_isRegularPoint_iff h₁.initial p ((chartAt ℂ p).map_source hs)).2 hy
    simpa only [(chartAt ℂ p).left_inv hs] using hr
  obtain ⟨y, hy, hqy⟩ := ((s26d_a_frequently_regular hδ (sub_ne_zero.mpr hne) (f p)).and_eventually hev).exists
  have he := terminalCoefficient_eq h₁ h₂ (f.symm y) (s23_h_center f (f.symm y)).1 hqy
  rw [(s23_h_center f (f.symm y)).2, f.apply_symm_apply] at he
  exact hy (sub_eq_zero.mpr he)

omit [ChartedSpace ℂ X] [ChartedSpace ℂ Y] in
/-- The uniqueness conclusion for actual differentials on the unchanged book target. -/
theorem bookTerminalDifferential_unique
    (R : Surfaces.ClosedRiemannSurface X) (S : Surfaces.ClosedRiemannSurface Y)
    (φ : Surfaces.HolomorphicQuadraticDifferential R.toRiemannAtlas) (f : X ≃ₜ Y)
    (ψ₁ ψ₂ : Surfaces.HolomorphicQuadraticDifferential S.toRiemannAtlas) (k : ℝ)
    (h₁ :
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      IsTeichmullerMap f φ ψ₁ k)
    (h₂ :
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      IsTeichmullerMap f φ ψ₂ k) : ψ₁ = ψ₂ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.connectedSpace
  let := S.connectedSpace
  let := R.t2Space
  let := S.t2Space
  apply Subtype.ext
  exact terminalDifferential_unique h₁ h₂

end LowDimensionalTopology.Geometry.Teichmuller
