/-
Copyright (c) 2026 Wu Xiaobin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeRootHorizontalFlowAction

/-!
# Root-oriented tube translations and continuity of the actual time maps

The domain retains the full complement of the critical-trajectory set with
its subtype topology. No openness of that complement is required.

The fixed-chart calculation and natural-map local inverse adapt the actual
chart-transition and inverse-function arguments of Wu Xiaobin's
Li-Zhong-QC-formalization, LiZhongQC/Ch07/S26_TeichmullerUniqueness.lean,
s26v_a_natAt_chart and s26v_flowBox_line, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

private def natRootVelocity
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (β : X → ℂ → ℂ) (G : ℂ → X) (u : ℂ) : ℂ :=
  letI := R.toRiemannAtlas.toChartedSpace
  β (G u) (chartAt ℂ (G u) (G u)) *
    deriv (fun z => chartAt ℂ (G u) (G z)) u

private theorem natRootVelocity_chart
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) (hβ : IsGlobalQuadraticRoot R q β) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ (G : ℂ → X) (u : ℂ), s26v_a_IsNatAt (q : X → ℂ → ℂ) G u →
      ∀ x : X, G u ∈ (chartAt ℂ x).source →
        natRootVelocity R β G u = β x (chartAt ℂ x (G u)) *
          deriv (fun z => chartAt ℂ x (G z)) u := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro G u hG x hx
  obtain ⟨hcont, v, hv, _⟩ := hG
  have hyy : G u ∈ (chartAt ℂ (G u)).source := mem_chart_source ℂ (G u)
  have hw : chartAt ℂ (G u) (G u) ∈ (chartAt ℂ (G u)).target :=
    (chartAt ℂ (G u)).map_source hyy
  have hws : (chartAt ℂ (G u)).symm (chartAt ℂ (G u) (G u)) = G u :=
    (chartAt ℂ (G u)).left_inv hyy
  obtain ⟨hT, _⟩ := s23_transition x (G u) hw (by rw [hws]; exact hx)
  have hlaw := hβ.1.2 x (G u) (chartAt ℂ (G u) (G u)) hw
    (by rw [hws]; exact hx)
  simp only [zpow_one, zpow_zero, mul_one] at hlaw
  have hTw : chartTransition x (G u) (chartAt ℂ (G u) (G u)) =
      chartAt ℂ x (G u) := by
    change chartAt ℂ x ((chartAt ℂ (G u)).symm (chartAt ℂ (G u) (G u))) = _
    rw [hws]
  have hev : (fun z => chartAt ℂ x (G z)) =ᶠ[𝓝 u]
      chartTransition x (G u) ∘ fun z => chartAt ℂ (G u) (G z) := by
    filter_upwards [hcont.preimage_mem_nhds ((chartAt ℂ (G u)).open_source.mem_nhds hyy)] with z hz
    change chartAt ℂ x (G z) = chartAt ℂ x ((chartAt ℂ (G u)).symm (chartAt ℂ (G u) (G z)))
    rw [(chartAt ℂ (G u)).left_inv hz]
  have hfixed : HasDerivAt (fun z => chartAt ℂ x (G z))
      (deriv (chartTransition x (G u)) (chartAt ℂ (G u) (G u)) * v) u :=
    (hT.hasDerivAt.comp u hv).congr_of_eventuallyEq hev
  dsimp only [natRootVelocity]
  rw [hv.deriv, hfixed.deriv, hlaw, hTw]
  ring

private theorem natRootVelocity_const
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) (hβ : IsGlobalQuadraticRoot R q β) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ (G : ℂ → X) (D : Set ℂ), IsOpen D → IsPreconnected D →
      (∀ u ∈ D, s26v_a_IsNatAt (q : X → ℂ → ℂ) G u) →
      ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ u ∈ D, natRootVelocity R β G u = ε := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro G D hDo hD hNat
  have hGc : ContinuousOn G D := fun u hu => (hNat u hu).1.continuousWithinAt
  have hcont : ContinuousOn (natRootVelocity R β G) D := by
    intro u₀ hu₀
    let x : X := G u₀
    have hx : G u₀ ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    let O : Set ℂ := D ∩ G ⁻¹' (chartAt ℂ x).source
    have hOo : IsOpen O := hGc.isOpen_inter_preimage hDo (chartAt ℂ x).open_source
    let g : ℂ → ℂ := fun u => chartAt ℂ x (G u)
    have hd : DifferentiableOn ℂ g O := fun u hu =>
      (s26v_a_natAt_differentiableAt q.property (hNat u hu.1) x hu.2).differentiableWithinAt
    have hga : AnalyticAt ℂ g u₀ := hd.analyticAt (hOo.mem_nhds ⟨hu₀, hx⟩)
    have hβa : AnalyticAt ℂ (β x) (g u₀) :=
      (hβ.2.1 x).analyticAt ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hx))
    have hmodel : ContinuousAt (fun u => β x (g u) * deriv g u) u₀ :=
      (hβa.continuousAt.comp hga.continuousAt).mul hga.deriv.continuousAt
    have hev : natRootVelocity R β G =ᶠ[𝓝 u₀] fun u => β x (g u) * deriv g u := by
      filter_upwards [hOo.mem_nhds ⟨hu₀, hx⟩] with u hu
      exact natRootVelocity_chart R q β hβ G u (hNat u hu.1) x hu.2
    exact (hmodel.congr hev.symm).continuousWithinAt
  have hroot : ∀ u ∈ D, natRootVelocity R β G u ^ 2 = (1 : ℂ) ^ 2 := by
    intro u hu
    obtain ⟨_, v, hv, hqv⟩ := hNat u hu
    dsimp only [natRootVelocity]
    rw [hv.deriv, mul_pow, hβ.2.2 (G u) (chartAt ℂ (G u) (G u))]
    simpa only [one_pow] using hqv
  obtain ⟨ε, hε, hval⟩ := s26d_b_eq_root_mul (G := natRootVelocity R β G)
    (H := fun _ => (1 : ℂ)) hD (show 0 < (2 : ℕ) by decide) hcont continuousOn_const
    (fun _ _ => one_ne_zero) hroot
  exact ⟨ε, hε, fun u hu => by simpa only [mul_one] using hval u hu⟩

private theorem rootGerm_unique
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ (c d : ℝ → X),
      (∀ᶠ t in 𝓝 (0 : ℝ), s26v_IsTrajAt (q : X → ℂ → ℂ) c t) →
      (∀ᶠ t in 𝓝 (0 : ℝ), s26v_IsTrajAt (q : X → ℂ → ℂ) d t) →
      c 0 = d 0 → IsRootHorizontalAt R β c 0 → IsRootHorizontalAt R β d 0 →
      c =ᶠ[𝓝 (0 : ℝ)] d := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro c d hc hd h0 hrc hrd
  obtain ⟨σ, hσ, hev⟩ := s26v_a_local_unique q.property hc hd h0
  rcases hσ with rfl | rfl
  · filter_upwards [hev] with r hr
    simpa only [zero_add, one_mul] using hr.symm
  · have hev' : d =ᶠ[𝓝 (0 : ℝ)] fun r => c (-r) := by
      filter_upwards [hev] with r hr
      simpa only [zero_add, neg_one_mul] using hr
    obtain ⟨_, v, hv, hβv⟩ := hrc
    obtain ⟨_, w, hw, hβw⟩ := hrd
    rw [← h0] at hw hβw
    have hvneg : HasDerivAt (fun r => chartAt ℂ (c 0) (c (-r))) (-v) 0 := by
      have h := HasDerivAt.scomp_of_eq (0 : ℝ) hv (hasDerivAt_neg (0 : ℝ))
        (by simp only [neg_zero])
      simpa [Function.comp_def] using h
    have heq : (fun r => chartAt ℂ (c 0) (d r)) =ᶠ[𝓝 (0 : ℝ)]
        fun r => chartAt ℂ (c 0) (c (-r)) :=
      hev'.mono fun r hr => congrArg (chartAt ℂ (c 0)) hr
    have hvel : w = -v := hw.unique (hvneg.congr_of_eventuallyEq heq)
    rw [hvel, mul_neg, hβv] at hβw
    norm_num at hβw

/-- The actual root fixes one translation sign on an entire natural tube. -/
theorem nativeRootHorizontalTimeMap_tube_sign
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) (hβ : IsGlobalQuadraticRoot R q β) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ (T : ℝ), 0 ≤ T → ∀ (p₀ : X) (ρ : ℝ) (G : ℂ → X),
      s26v_a_IsTube (q : X → ℂ → ℂ) T p₀ ρ G →
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        ∀ w ∈ ball (0 : ℂ) ρ, ∀ t ∈ Icc (-T) T,
          ∀ hw : G w ∉ s26v_E (q : X → ℂ → ℂ),
            (nativeRootHorizontalTimeMap R q β t ⟨G w, hw⟩ : X) =
              G (w + ((σ * t : ℝ) : ℂ)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.t2Space
  let := R.toRiemannAtlas.isManifold
  intro T hT p₀ ρ G hG
  let D : Set ℂ := {u | u.re ∈ Ioo (-T - 2 * ρ) (T + 2 * ρ) ∧
    u.im ∈ Ioo (-(2 * ρ)) (2 * ρ)}
  have hDo : IsOpen D := s26v_a_isOpen_rect (-T) T (2 * ρ)
  have hDc : IsPreconnected D := (s26v_a_convex_rect (-T) T (2 * ρ)).isPreconnected
  have hNat : ∀ u ∈ D, s26v_a_IsNatAt (q : X → ℂ → ℂ) G u :=
    fun u hu => hG.2.2.1 u hu.1 hu.2
  obtain ⟨ε, hε, hval⟩ := natRootVelocity_const R q β hβ G D hDo hDc hNat
  have hσex : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ε * (σ : ℂ) = 1 := by
    rcases sq_eq_one_iff.mp hε with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; norm_num⟩
  obtain ⟨σ, hσ, hεσ⟩ := hσex
  refine ⟨σ, hσ, ?_⟩
  intro w hw t ht hwE
  have hwNorm : ‖w‖ < ρ := by simpa using hw
  have hre : -ρ < w.re ∧ w.re < ρ := abs_lt.mp ((Complex.abs_re_le_norm w).trans_lt hwNorm)
  have him : -ρ < w.im ∧ w.im < ρ := abs_lt.mp ((Complex.abs_im_le_norm w).trans_lt hwNorm)
  have hwD : w ∈ D := by constructor <;> constructor <;> linarith [hG.1, hre.1, hre.2, him.1, him.2]
  let J : Set ℝ := Ioo (-T - ρ) (T + ρ)
  have hJ0 : (0 : ℝ) ∈ J := by constructor <;> linarith [hG.1]
  let g : ℝ → X := fun r => G (w + (σ : ℂ) * (r : ℂ))
  have hNatLine : ∀ r ∈ J, s26v_a_IsNatAt (q : X → ℂ → ℂ) G (w + (σ : ℂ) * (r : ℂ)) := by
    intro r hr
    apply hG.2.2.1
    · rcases hσ with rfl | rfl
      · simp only [Complex.ofReal_one, one_mul, Complex.add_re, Complex.ofReal_re]
        constructor <;> linarith [hre.1, hre.2, hr.1, hr.2]
      · simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, Complex.add_re,
          Complex.neg_re, Complex.ofReal_re]
        constructor <;> linarith [hre.1, hre.2, hr.1, hr.2]
    · rcases hσ with rfl | rfl <;>
        simp only [Complex.ofReal_one, one_mul, Complex.ofReal_neg, neg_one_mul,
          Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero, add_zero] <;>
        constructor <;> linarith [hG.1, him.1, him.2]
  have hgT : ∀ r ∈ J, s26v_IsTrajAt (q : X → ℂ → ℂ) g r :=
    fun r hr => s26v_a_trajAt_of_natAt hσ (hNatLine r hr)
  have hg0 : g 0 = G w := by simp only [g, Complex.ofReal_zero, mul_zero, add_zero]
  obtain ⟨_, v, hv, _⟩ := hNat w hwD
  have hβv : β (G w) (chartAt ℂ (G w) (G w)) * v = ε := by
    simpa only [natRootVelocity, hv.deriv] using hval w hwD
  have hlin : HasDerivAt (fun r : ℝ => w + (σ : ℂ) * (r : ℂ)) (σ : ℂ) 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (σ : ℂ)).const_add w
  have hv' : HasDerivAt (fun z => chartAt ℂ (G w) (G z)) v
      (w + (σ : ℂ) * ((0 : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_zero, mul_zero, add_zero] using hv
  have hcomp := hv'.comp (0 : ℝ) hlin
  have hrootg : IsRootHorizontalAt R β g 0 := by
    refine ⟨(hgT 0 hJ0).1, v * (σ : ℂ), ?_, ?_⟩
    · rw [hg0]
      simpa only [Function.comp_def, g] using hcomp
    · rw [hg0, ← mul_assoc, hβv, hεσ]
  let p : {p : X // p ∉ s26v_E (q : X → ℂ → ℂ)} := ⟨G w, hwE⟩
  let c : ℝ → X := fun r => (nativeRootHorizontalTimeMap R q β r p : X)
  have hcT : ∀ r, s26v_IsTrajAt (q : X → ℂ → ℂ) c r := by
    have h := (nativeRootHorizontalTimeMap_trajectory R q β hβ p).1
    exact fun r => h.2.2.2.2.1 r (mem_univ r)
  have hc0 : c 0 = G w := (nativeRootHorizontalTimeMap_trajectory R q β hβ p).1.2.2.2.1
  have hrootc : IsRootHorizontalAt R β c 0 := nativeRootHorizontalTimeMap_rootAt R q β hβ p 0
  have hgerm : c =ᶠ[𝓝 (0 : ℝ)] g := rootGerm_unique R q β c g
    (Eventually.of_forall hcT)
    (Filter.Eventually.mono (isOpen_Ioo.mem_nhds hJ0) (fun r hr => hgT r hr))
    (hc0.trans hg0.symm) hrootc hrootg
  have heq := s26v_a_eqOn_of_eventuallyEq q.property isOpen_Ioo isPreconnected_Ioo
    (fun r _ => hcT r) hgT hJ0 hgerm
  have htJ : t ∈ J := by constructor <;> linarith [ht.1, ht.2, hG.1]
  simpa only [c, g, Complex.ofReal_mul] using heq t htJ

private theorem tube_inverseCoordinate
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ (T : ℝ), 0 ≤ T → ∀ (p₀ : X) (ρ : ℝ) (G : ℂ → X),
      s26v_a_IsTube (q : X → ℂ → ℂ) T p₀ ρ G →
      ∃ W : X → ℂ, ContinuousAt W p₀ ∧ W p₀ = 0 ∧
        ∀ᶠ p in 𝓝 p₀, W p ∈ ball (0 : ℂ) ρ ∧ G (W p) = p := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro T hT p₀ ρ G hG
  have h0T : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  have hNat : ∀ u ∈ ball (0 : ℂ) ρ, s26v_a_IsNatAt (q : X → ℂ → ℂ) G u := by
    simpa only [Complex.ofReal_zero] using (s26v_a_tube_ball hG h0T).1
  have hNat0 := hNat 0 (mem_ball_self hG.1)
  have hx0 : G 0 ∈ (chartAt ℂ p₀).source := by
    rw [hG.2.1]
    exact mem_chart_source ℂ p₀
  have hsrc : {u : ℂ | G u ∈ (chartAt ℂ p₀).source} ∈ 𝓝 (0 : ℂ) :=
    hNat0.1.preimage_mem_nhds ((chartAt ℂ p₀).open_source.mem_nhds hx0)
  have hnear : ∀ᶠ u : ℂ in 𝓝 0,
      G u ∈ (chartAt ℂ p₀).source ∧ u ∈ ball (0 : ℂ) ρ :=
    Filter.Eventually.and hsrc (ball_mem_nhds (0 : ℂ) hG.1)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnear
  let g : ℂ → ℂ := fun u => chartAt ℂ p₀ (G u)
  have hd : DifferentiableOn ℂ g (ball (0 : ℂ) r) := fun u hu =>
    (s26v_a_natAt_differentiableAt q.property (hNat u (hball u hu).2) p₀
      (hball u hu).1).differentiableWithinAt
  have hstrict : HasStrictDerivAt g (deriv g 0) 0 :=
    (hd.analyticAt (ball_mem_nhds (0 : ℂ) hr)).hasStrictDerivAt
  obtain ⟨v, hv, hqv⟩ := s26v_a_natAt_chart q.property hNat0 p₀ hx0
  have hv0 : deriv g 0 ≠ 0 := by
    rw [hv.deriv]
    intro hzero
    norm_num [hzero] at hqv
  let K : ℂ → ℂ := hstrict.localInverse g (deriv g 0) 0 hv0
  have hKd : HasStrictDerivAt K (deriv g 0)⁻¹ (g 0) := hstrict.to_localInverse hv0
  have hKr : ∀ᶠ z in 𝓝 (g 0), g (K z) = z := hstrict.eventually_right_inverse hv0
  have hKl : ∀ᶠ u in 𝓝 (0 : ℂ), K (g u) = u := hstrict.eventually_left_inverse hv0
  have hK0 : K (g 0) = 0 := hKl.self_of_nhds
  have hg0 : g 0 = chartAt ℂ p₀ p₀ := by dsimp only [g]; rw [hG.2.1]
  let W : X → ℂ := fun p => K (chartAt ℂ p₀ p)
  have hWc : ContinuousAt W p₀ := by
    have hKc : ContinuousAt K (chartAt ℂ p₀ p₀) := by
      rw [← hg0]
      exact hKd.hasDerivAt.continuousAt
    exact hKc.comp ((chartAt ℂ p₀).continuousAt (mem_chart_source ℂ p₀))
  have hW0 : W p₀ = 0 := by
    change K (chartAt ℂ p₀ p₀) = 0
    rw [← hg0]
    exact hK0
  have hWT : Tendsto W (𝓝 p₀) (𝓝 (0 : ℂ)) := by simpa only [hW0] using hWc.tendsto
  have hgood : ∀ᶠ p in 𝓝 p₀, W p ∈ ball (0 : ℂ) ρ ∧ G (W p) ∈ (chartAt ℂ p₀).source :=
    hWT.eventually (Filter.Eventually.and (ball_mem_nhds (0 : ℂ) hG.1) hsrc)
  have hchartT : Tendsto (chartAt ℂ p₀) (𝓝 p₀) (𝓝 (g 0)) := by
    rw [hg0]
    exact ((chartAt ℂ p₀).continuousAt (mem_chart_source ℂ p₀)).tendsto
  refine ⟨W, hWc, hW0, ?_⟩
  filter_upwards [hgood, hchartT.eventually hKr,
    (chartAt ℂ p₀).open_source.mem_nhds (mem_chart_source ℂ p₀)] with p hp hright hps
  refine ⟨hp.1, (chartAt ℂ p₀).injOn hp.2 hps ?_⟩
  exact hright

/-- The same root-oriented time maps are jointly continuous on ℝ × Ω,
where Ω has its actual subtype topology and removes all critical trajectories. -/
theorem nativeRootHorizontalTimeMap_continuous
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) (hβ : IsGlobalQuadraticRoot R q β) :
    letI := R.toRiemannAtlas.toChartedSpace
    let Ω := {p : X // p ∉ s26v_E (q : X → ℂ → ℂ)}
    Continuous (fun v : ℝ × Ω => nativeRootHorizontalTimeMap R q β v.1 v.2) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.t2Space
  let := R.toRiemannAtlas.isManifold
  let Ω := {p : X // p ∉ s26v_E (q : X → ℂ → ℂ)}
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t₀, p⟩
  let T : ℝ := |t₀| + 1
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have ht₀ : t₀ ∈ Ioo (-T) T := by
    dsimp only [T]
    constructor <;> linarith [le_abs_self t₀, neg_abs_le t₀]
  obtain ⟨ρ, G, hG⟩ := s26v_a_tube_exists q.property p.property hT
  obtain ⟨σ, hσ, hformula⟩ := nativeRootHorizontalTimeMap_tube_sign R q β hβ T hT (p : X) ρ G hG
  obtain ⟨W, hWc, hW0, hWinv⟩ := tube_inverseCoordinate R q T hT (p : X) ρ G hG
  have hproj : ContinuousAt (fun v : ℝ × Ω => (v.2 : X)) (t₀, p) :=
    (continuous_subtype_val.comp continuous_snd).continuousAt
  have hWcomp : ContinuousAt (fun v : ℝ × Ω => W (v.2 : X)) (t₀, p) :=
    hWc.comp (f := fun v : ℝ × Ω => (v.2 : X)) (x := (t₀, p)) hproj
  have harg : ContinuousAt (fun v : ℝ × Ω => W (v.2 : X) + ((σ * v.1 : ℝ) : ℂ)) (t₀, p) :=
    hWcomp.add (Complex.continuous_ofReal.continuousAt.comp (continuous_fst.continuousAt.const_mul σ))
  have harg0 : W (p : X) + ((σ * t₀ : ℝ) : ℂ) = ((σ * t₀ : ℝ) : ℂ) := by rw [hW0, zero_add]
  have hnat0 : s26v_a_IsNatAt (q : X → ℂ → ℂ) G ((σ * t₀ : ℝ) : ℂ) := by
    apply hG.2.2.1
    · rcases hσ with rfl | rfl <;>
        simp only [one_mul, neg_one_mul, Complex.ofReal_re] <;>
        constructor <;> linarith [hG.1, ht₀.1, ht₀.2]
    · simp only [Complex.ofReal_im]
      constructor <;> linarith [hG.1]
  have hGc : ContinuousAt G (W (p : X) + ((σ * t₀ : ℝ) : ℂ)) := by
    rw [harg0]
    exact hnat0.1
  have hmodel := hGc.comp
    (f := fun v : ℝ × Ω => W (v.2 : X) + ((σ * v.1 : ℝ) : ℂ)) (x := (t₀, p)) harg
  have hTime : ∀ᶠ v : ℝ × Ω in 𝓝 (t₀, p), v.1 ∈ Ioo (-T) T :=
    continuous_fst.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ht₀)
  have hSpace : ∀ᶠ v : ℝ × Ω in 𝓝 (t₀, p),
      W (v.2 : X) ∈ ball (0 : ℂ) ρ ∧ G (W (v.2 : X)) = (v.2 : X) :=
    hproj.tendsto.eventually hWinv
  have heq : (fun v : ℝ × Ω => (nativeRootHorizontalTimeMap R q β v.1 v.2 : X)) =ᶠ[𝓝 (t₀, p)]
      fun v => G (W (v.2 : X) + ((σ * v.1 : ℝ) : ℂ)) := by
    filter_upwards [hTime, hSpace] with v ht hp
    have hnot : G (W (v.2 : X)) ∉ s26v_E (q : X → ℂ → ℂ) := by rw [hp.2]; exact v.2.property
    have hpEq : (⟨G (W (v.2 : X)), hnot⟩ : Ω) = v.2 := Subtype.ext hp.2
    have h := hformula (W (v.2 : X)) hp.1 v.1 ⟨ht.1.le, ht.2.le⟩ hnot
    rw [hpEq] at h
    exact h
  have hactual := hmodel.congr heq.symm
  exact tendsto_subtype_rng.2 hactual

end LowDimensionalTopology.Geometry.Teichmuller
