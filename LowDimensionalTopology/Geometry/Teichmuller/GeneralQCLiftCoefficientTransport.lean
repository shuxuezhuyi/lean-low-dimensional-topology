/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch07.S27_TeichmullerExistence

/-!
# The literal lifted coefficient under a conformal target change

The two target carriers may lie in independent universes. At every point,
including a point where the inner map is not differentiable, the genuine
holomorphic local inverse permits the public Wirtinger composition rule.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC

universe u v w

private theorem chart_dilatation_postcompose
    {Y : Type v} {Z : Type w} [TopologicalSpace Y] [TopologicalSpace Z]
    [ChartedSpace ℂ Y] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) ω Y] [IsManifold 𝓘(ℂ) ω Z]
    {q : ℂ → Y} {z : ℂ} (hq : ContinuousAt q z)
    (c : Y ≃ₜ Z) (hc : IsBiholomorphic (c : Y → Z)) :
    complexDilatation (fun a => chartAt ℂ (c (q z)) (c (q a))) z =
      complexDilatation (fun a => chartAt ℂ (q z) (q a)) z := by
  let y : Y := q z
  let g : ℂ → ℂ := fun a => chartAt ℂ y (q a)
  let h : ℂ → ℂ := localMapExpr c y
  let k : ℂ → ℂ := fun a => chartAt ℂ y (c.symm ((chartAt ℂ (c y)).symm a))
  have hg : ContinuousAt g z :=
    ((chartAt ℂ y).continuousAt (mem_chart_source ℂ y)).comp hq
  have hh : DifferentiableAt ℂ h (g z) := by
    change DifferentiableAt ℂ
      (fun a => chartAt ℂ (c y) (c ((chartAt ℂ y).symm a))) (chartAt ℂ y y)
    exact ((s23_mdifferentiableAt_iff (f := c)
      (mem_chart_source ℂ y) (mem_chart_source ℂ (c y))).mp (hc.1 y)).2
  have hvalue : h (g z) = chartAt ℂ (c y) (c y) := by
    simpa only [h, g, y] using (s23_h_center c y).2
  have hk : DifferentiableAt ℂ k (h (g z)) := by
    rw [hvalue]
    have hy : c.symm (c y) ∈ (chartAt ℂ y).source := by
      rw [c.symm_apply_apply]
      exact mem_chart_source ℂ y
    exact ((s23_mdifferentiableAt_iff (f := c.symm)
      (mem_chart_source ℂ (c y)) hy).mp (hc.homeomorph_symm.1 (c y))).2
  have hkh : ∀ᶠ a in 𝓝 (g z), k (h a) = a := by
    have hmem : g z ∈ localMapDomain c y := by
      simpa only [g, y] using (s23_h_center c y).1
    filter_upwards [(s23_localMapDomain_isOpen c.continuous y).mem_nhds hmem] with a ha
    dsimp only [k, h, localMapExpr]
    rw [(chartAt ℂ (c y)).left_inv ha.2, c.symm_apply_apply,
      (chartAt ℂ y).right_inv ha.1]
  have heq : (fun a => chartAt ℂ (c y) (c (q a))) =ᶠ[𝓝 z] h ∘ g := by
    filter_upwards [hq.eventually
      ((chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))] with a ha
    dsimp only [h, g, localMapExpr, Function.comp_apply]
    rw [(chartAt ℂ y).left_inv ha]
  calc
    complexDilatation (fun a => chartAt ℂ (c (q z)) (c (q a))) z =
        complexDilatation (h ∘ g) z := by
      have hd : fderiv ℝ (fun a => chartAt ℂ (c (q z)) (c (q a))) z =
          fderiv ℝ (h ∘ g) z := by
        simpa only [y] using heq.fderiv_eq (𝕜 := ℝ)
      simp only [complexDilatation, dz, dzbar, hd]
    _ = complexDilatation (fun a => chartAt ℂ (q z) (q a)) z :=
      s23_dilatation_comp_left hg hh hk hkh

/-- A genuine biholomorphic change of target preserves the literal original
lifted Beltrami coefficient at every complex point. No quasiconformality or
same-universe condition is needed for this equality. -/
theorem liftCoeff_postcompose_biholomorphic
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [ChartedSpace ℂ Y] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) ω Y] [IsManifold 𝓘(ℂ) ω Z]
    {p : UpperHalfPlane → X} (hp : Continuous p)
    {f : X → Y} (hf : Continuous f)
    (c : Y ≃ₜ Z) (hc : IsBiholomorphic (c : Y → Z)) :
    s27u_liftCoeff p (c ∘ f) = s27u_liftCoeff p f := by
  funext z
  by_cases hz : z ∈ upperHalf
  · rw [s27u_liftCoeff_of_mem p (c ∘ f) hz, s27u_liftCoeff_of_mem p f hz]
    exact chart_dilatation_postcompose (hf.continuousAt.comp (utm_a_continuousAt hp hz)) c hc
  · rw [s27u_liftCoeff_of_not_mem p (c ∘ f) hz, s27u_liftCoeff_of_not_mem p f hz]

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
