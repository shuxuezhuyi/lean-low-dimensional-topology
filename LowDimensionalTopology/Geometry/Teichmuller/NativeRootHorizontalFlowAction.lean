/-
Copyright (c) 2026 Wu Xiaobin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeRootHorizontalTimeMap
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Root orientation and addition for the actual horizontal time maps

The same global Abelian root orients the concrete time maps on the complement
of all critical trajectories. Measurability and area preservation are separate.

The fixed-chart contraction calculation adapts the chart transition and
chain-rule argument of Wu Xiaobin's Li-Zhong-QC-formalization,
LiZhongQC/Ch07/S26_TeichmullerUniqueness.lean, s26v_trajAt_chart,
fixed commit 1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

private def rootVelocity
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (β : X → ℂ → ℂ) (c : ℝ → X) (t : ℝ) : ℂ :=
  letI := R.toRiemannAtlas.toChartedSpace
  β (c t) (chartAt ℂ (c t) (c t)) *
    deriv (fun s => chartAt ℂ (c t) (c s)) t

private theorem rootVelocity_chart
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) (hβ : IsGlobalQuadraticRoot R q β) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ c : C(ℝ, X), s26v_IsTraj (q : X → ℂ → ℂ) c →
      ∀ (t : ℝ) (x : X), c t ∈ (chartAt ℂ x).source →
        rootVelocity R β c t = β x (chartAt ℂ x (c t)) *
          deriv (fun s => chartAt ℂ x (c s)) t := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro c hc t x hx
  obtain ⟨hcont, v, hv, _⟩ := hc t
  have hyy : c t ∈ (chartAt ℂ (c t)).source := mem_chart_source ℂ (c t)
  have hw : chartAt ℂ (c t) (c t) ∈ (chartAt ℂ (c t)).target :=
    (chartAt ℂ (c t)).map_source hyy
  have hws : (chartAt ℂ (c t)).symm (chartAt ℂ (c t) (c t)) = c t :=
    (chartAt ℂ (c t)).left_inv hyy
  obtain ⟨hT, _⟩ := s23_transition x (c t) hw (by rw [hws]; exact hx)
  have hlaw := hβ.1.2 x (c t) (chartAt ℂ (c t) (c t)) hw
    (by rw [hws]; exact hx)
  simp only [zpow_one, zpow_zero, mul_one] at hlaw
  have hTw : chartTransition x (c t) (chartAt ℂ (c t) (c t)) =
      chartAt ℂ x (c t) := by
    change chartAt ℂ x ((chartAt ℂ (c t)).symm (chartAt ℂ (c t) (c t))) = _
    rw [hws]
  have hev : (fun s => chartAt ℂ x (c s)) =ᶠ[𝓝 t]
      chartTransition x (c t) ∘ fun s => chartAt ℂ (c t) (c s) := by
    filter_upwards [hcont.preimage_mem_nhds ((chartAt ℂ (c t)).open_source.mem_nhds hyy)] with s hs
    change chartAt ℂ x (c s) = chartAt ℂ x ((chartAt ℂ (c t)).symm (chartAt ℂ (c t) (c s)))
    rw [(chartAt ℂ (c t)).left_inv hs]
  have hfixed : HasDerivAt (fun s => chartAt ℂ x (c s))
      (deriv (chartTransition x (c t)) (chartAt ℂ (c t) (c t)) * v) t :=
    (hT.hasDerivAt.comp t hv).congr_of_eventuallyEq hev
  dsimp only [rootVelocity]
  rw [hv.deriv, hfixed.deriv, hlaw, hTw]
  ring

private theorem rootVelocity_locallyConstant
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) (hβ : IsGlobalQuadraticRoot R q β) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ c : C(ℝ, X), s26v_IsTraj (q : X → ℂ → ℂ) c →
      IsLocallyConstant (rootVelocity R β c) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro c hc
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro t₀
  let x : X := c t₀
  have hx : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hreg : (q : X → ℂ → ℂ) x (chartAt ℂ x x) ≠ 0 :=
    s26v_a_trajAt_regular (hc t₀)
  obtain ⟨B, Z, hxB, hsub, hB⟩ := s26v_exists_flowBox q.property hreg
    ((chartAt ℂ x).open_source.mem_nhds hx)
  let O : Set ℂ := (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' B
  obtain ⟨hO, hdiff⟩ := s26v_a_flowBox_differentiableOn q.property hB x
  have hwO : chartAt ℂ x x ∈ O :=
    ⟨(chartAt ℂ x).map_source hx, by
      change (chartAt ℂ x).symm (chartAt ℂ x x) ∈ B
      simpa only [(chartAt ℂ x).left_inv hx] using hxB⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO (chartAt ℂ x x) hwO
  let D : Set ℂ := ball (chartAt ℂ x x) r
  let G : ℂ → ℂ := fun z => Z ((chartAt ℂ x).symm z)
  let H : ℂ → ℂ := deriv G
  have hH : ∀ z ∈ D, HasDerivAt G (H z) z ∧ H z ≠ 0 ∧
      H z ^ 2 = (q : X → ℂ → ℂ) x z := by
    intro z hz
    obtain ⟨v, hv, hv0, hv2⟩ := s26v_a_flowBox_chart q.property hB x
      (hball hz).1 (hball hz).2
    have hval : H z = v := hv.deriv
    exact ⟨hval.symm ▸ hv, hval.symm ▸ hv0, hval.symm ▸ hv2⟩
  have hHc : ContinuousOn H D := by
    intro z hz
    have han : AnalyticAt ℂ G z := hdiff.analyticAt (hO.mem_nhds (hball hz))
    exact han.deriv.continuousAt.continuousWithinAt
  have hβc : ContinuousOn (β x) D :=
    (hβ.2.1 x).continuousOn.mono fun z hz => (hball hz).1
  obtain ⟨ε, _hε, hβH⟩ := s26d_b_eq_root_mul (convex_ball _ _).isPreconnected
    (show 0 < (2 : ℕ) by decide) hβc hHc (fun z hz => (hH z hz).2.1)
    (fun z hz => (hβ.2.2 x z).trans (hH z hz).2.2.symm)
  have hNB : {s : ℝ | c s ∈ B} ∈ 𝓝 t₀ :=
    c.continuous.continuousAt.preimage_mem_nhds (hB.1.mem_nhds hxB)
  have hchartc : ContinuousAt (fun s => chartAt ℂ x (c s)) t₀ :=
    ((chartAt ℂ x).continuousAt hx).comp c.continuous.continuousAt
  have hND : {s : ℝ | chartAt ℂ x (c s) ∈ D} ∈ 𝓝 t₀ :=
    hchartc.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))
  obtain ⟨a, b, ht₀, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp (inter_mem hNB hND)
  obtain ⟨σ, _hσ, hline⟩ := s26v_a_line_of_box hB
    (fun s hs => ⟨hc s, (hI hs).1⟩) ht₀
  have hval : ∀ s ∈ Ioo a b, rootVelocity R β c s = ε * (σ : ℂ) := by
    intro s hs
    have hsB : c s ∈ B := (hI hs).1
    have hsD : chartAt ℂ x (c s) ∈ D := (hI hs).2
    have hsx : c s ∈ (chartAt ℂ x).source := hsub hsB
    obtain ⟨v, hv, _⟩ := s26v_trajAt_chart q.property (hc s) x hsx
    have hev : (fun u => Z (c u)) =ᶠ[𝓝 s]
        G ∘ fun u => chartAt ℂ x (c u) := by
      filter_upwards [c.continuous.continuousAt.preimage_mem_nhds
        ((chartAt ℂ x).open_source.mem_nhds hsx)] with u hu
      change Z (c u) = Z ((chartAt ℂ x).symm (chartAt ℂ x (c u)))
      rw [(chartAt ℂ x).left_inv hu]
    have hcomp : HasDerivAt (fun u => Z (c u)) (H (chartAt ℂ x (c s)) * v) s :=
      ((hH _ hsD).1.comp s hv).congr_of_eventuallyEq hev
    have hlinear : HasDerivAt (fun u : ℝ => Z (c t₀) + ((σ * (u - t₀) : ℝ) : ℂ))
        (σ : ℂ) s := by
      have h := ((hasDerivAt_id s).sub_const t₀).const_mul σ
      simpa using h.ofReal_comp.const_add (Z (c t₀))
    have heq : (fun u => Z (c u)) =ᶠ[𝓝 s]
        fun u => Z (c t₀) + ((σ * (u - t₀) : ℝ) : ℂ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu using hline u hu
    have hprod : H (chartAt ℂ x (c s)) * v = (σ : ℂ) :=
      hcomp.unique (hlinear.congr_of_eventuallyEq heq)
    calc
      rootVelocity R β c s = β x (chartAt ℂ x (c s)) * v := by
        rw [rootVelocity_chart R q β hβ c hc s x hsx, hv.deriv]
      _ = ε * (H (chartAt ℂ x (c s)) * v) := by rw [hβH _ hsD]; ring
      _ = ε * (σ : ℂ) := by rw [hprod]
  filter_upwards [isOpen_Ioo.mem_nhds ht₀] with s hs
  exact (hval s hs).trans (hval t₀ ht₀).symm

private theorem rootAt_all
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) (hβ : IsGlobalQuadraticRoot R q β) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ c : C(ℝ, X), s26v_IsTraj (q : X → ℂ → ℂ) c →
      IsRootHorizontalAt R β c 0 → ∀ t : ℝ, IsRootHorizontalAt R β c t := by
  let := R.toRiemannAtlas.toChartedSpace
  intro c hc h0 t
  have hloc := rootVelocity_locallyConstant R q β hβ c hc
  have hvel0 : rootVelocity R β c 0 = 1 := by
    obtain ⟨_, v, hv, hβv⟩ := h0
    dsimp only [rootVelocity]
    rw [hv.deriv]
    exact hβv
  have hvel : rootVelocity R β c t = 1 :=
    (hloc.apply_eq_of_preconnectedSpace t 0).trans hvel0
  obtain ⟨hcont, v, hv, _⟩ := hc t
  refine ⟨hcont, v, hv, ?_⟩
  simpa only [rootVelocity, hv.deriv] using hvel

private theorem rootAt_shift
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (β : X → ℂ → ℂ) (c : ℝ → X) (s t : ℝ) :
    letI := R.toRiemannAtlas.toChartedSpace
    IsRootHorizontalAt R β c (s + t) →
      IsRootHorizontalAt R β (fun r => c (r + t)) s := by
  let := R.toRiemannAtlas.toChartedSpace
  rintro ⟨hcont, v, hv, hβv⟩
  have hshift : ContinuousAt (fun r : ℝ => r + t) s := by fun_prop
  refine ⟨hcont.comp (f := fun r : ℝ => r + t) (x := s) hshift,
    v, HasDerivAt.comp_add_const s t hv, hβv⟩

/-- The same concrete time curves have the root's positive velocity at every time. -/
theorem nativeRootHorizontalTimeMap_rootAt
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) (hβ : IsGlobalQuadraticRoot R q β) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ p : {p : X // p ∉ s26v_E (q : X → ℂ → ℂ)}, ∀ t : ℝ,
      IsRootHorizontalAt R β
        (fun u => (nativeRootHorizontalTimeMap R q β u p : X)) t := by
  let := R.toRiemannAtlas.toChartedSpace
  intro p
  have h := nativeRootHorizontalTimeMap_trajectory R q β hβ p
  obtain ⟨_, _, _, _, hunit, _⟩ := h.1
  let c : C(ℝ, X) := ⟨(fun t => (nativeRootHorizontalTimeMap R q β t p : X)),
    continuous_iff_continuousAt.mpr (fun t => (hunit t (mem_univ t)).1)⟩
  exact rootAt_all R q β hβ c (fun t => hunit t (mem_univ t)) h.2

/-- The actual root-oriented time maps satisfy the zero and addition laws on Ω. -/
theorem nativeRootHorizontalTimeMap_action
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) (hβ : IsGlobalQuadraticRoot R q β) :
    letI := R.toRiemannAtlas.toChartedSpace
    let Ω := {p : X // p ∉ s26v_E (q : X → ℂ → ℂ)}
    (∀ p : Ω, nativeRootHorizontalTimeMap R q β 0 p = p) ∧
      ∀ (s t : ℝ) (p : Ω),
        nativeRootHorizontalTimeMap R q β (s + t) p =
          nativeRootHorizontalTimeMap R q β s (nativeRootHorizontalTimeMap R q β t p) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.t2Space
  let := R.toRiemannAtlas.isManifold
  let Ω := {p : X // p ∉ s26v_E (q : X → ℂ → ℂ)}
  have hunit (p : Ω) : ∀ t : ℝ,
      s26v_IsTrajAt (q : X → ℂ → ℂ)
        (fun u => (nativeRootHorizontalTimeMap R q β u p : X)) t := by
    have h := (nativeRootHorizontalTimeMap_trajectory R q β hβ p).1
    exact fun t => h.2.2.2.2.1 t (mem_univ t)
  have hzero (p : Ω) : nativeRootHorizontalTimeMap R q β 0 p = p := by
    apply Subtype.ext
    exact (nativeRootHorizontalTimeMap_trajectory R q β hβ p).1.2.2.2.1
  refine ⟨hzero, ?_⟩
  intro s t p
  let c₁ : C(ℝ, X) := ⟨fun r => (nativeRootHorizontalTimeMap R q β (r + t) p : X),
    continuous_iff_continuousAt.mpr (fun r => (s26v_trajAt_shift (hunit p (r + t))).1)⟩
  let c₂ : C(ℝ, X) := ⟨fun r => (nativeRootHorizontalTimeMap R q β r
      (nativeRootHorizontalTimeMap R q β t p) : X),
    continuous_iff_continuousAt.mpr (fun r => (hunit (nativeRootHorizontalTimeMap R q β t p) r).1)⟩
  have hc₁ : s26v_IsTraj (q : X → ℂ → ℂ) c₁ :=
    fun r => s26v_trajAt_shift (hunit p (r + t))
  have hc₂ : s26v_IsTraj (q : X → ℂ → ℂ) c₂ :=
    hunit (nativeRootHorizontalTimeMap R q β t p)
  have h0 : c₁ 0 = c₂ 0 := by
    change (nativeRootHorizontalTimeMap R q β (0 + t) p : X) =
      (nativeRootHorizontalTimeMap R q β 0 (nativeRootHorizontalTimeMap R q β t p) : X)
    rw [zero_add, hzero]
  have hr₁ : IsRootHorizontalAt R β c₁ 0 :=
    rootAt_shift R β (fun u => (nativeRootHorizontalTimeMap R q β u p : X)) 0 t
      (by simpa only [zero_add] using nativeRootHorizontalTimeMap_rootAt R q β hβ p t)
  have hr₂ : IsRootHorizontalAt R β c₂ 0 :=
    nativeRootHorizontalTimeMap_rootAt R q β hβ (nativeRootHorizontalTimeMap R q β t p) 0
  rcases s26v_traj_unique q.property hc₁ hc₂ h0 with heq | hrev
  · apply Subtype.ext
    exact (heq s).symm
  · obtain ⟨_, v₁, hv₁, hβ₁⟩ := hr₁
    obtain ⟨_, v₂, hv₂, hβ₂⟩ := hr₂
    have hpt : c₂ 0 = c₁ 0 := h0.symm
    rw [hpt] at hv₂ hβ₂
    have hfun : (c₂ : ℝ → X) = fun r => c₁ (-r) := funext hrev
    have hv₂' : HasDerivAt (fun r => chartAt ℂ (c₁ 0) (c₁ (-r))) v₂ 0 := by
      simpa only [hfun] using hv₂
    have hvneg : HasDerivAt (fun r => chartAt ℂ (c₁ 0) (c₁ (-r))) (-v₁) 0 := by
      have h := HasDerivAt.scomp_of_eq (0 : ℝ) hv₁ (hasDerivAt_neg (0 : ℝ))
        (by simp only [neg_zero])
      simpa [Function.comp_def] using h
    have hvel : v₂ = -v₁ := hv₂'.unique hvneg
    rw [hvel, mul_neg, hβ₁] at hβ₂
    norm_num at hβ₂

end LowDimensionalTopology.Geometry.Teichmuller
