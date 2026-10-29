module

public import LowDimensionalTopology.Geometry.Teichmuller.AnalyticCoverDescent
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicCovering
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Differentiability of lifts in the original surface atlases

An analytic covering has analytic local inverse sheets. Composing with these
sheets proves that a continuous lift of a real differentiable map is real
differentiable. No continuously differentiable hypothesis is substituted for
pointwise differentiability. The based universal-cover lift also preserves
holomorphicity, using the original complex structures throughout.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

private theorem realDifferentiableAt_chartMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} {f : X → Y}
    (hf : let := A.toChartedSpace; let := B.toChartedSpace;
      MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ A.charts)
    (g : OpenPartialHomeomorph Y ℂ) (hg : g ∈ B.charts)
    (x : X) (hx : x ∈ e.source) (hy : f x ∈ g.source) :
    DifferentiableAt ℝ (riemannChartMap e f g) (e x) := by
  let := A.toChartedSpace
  let := B.toChartedSpace
  let := A.isRealManifold
  let := B.isRealManifold
  have heMax : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 X :=
    IsManifold.subset_maximalAtlas he
  have hgMax : g ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 Y :=
    IsManifold.subset_maximalAtlas hg
  have h := (mdifferentiableWithinAt_iff_of_mem_maximalAtlas
    (s := Set.univ) heMax hgMax hx hy).mp
    (hf x).mdifferentiableWithinAt
  simpa only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.range_id, Set.preimage_univ,
    Set.univ_inter, differentiableWithinAt_univ, riemannChartMap] using h.2

/-- A continuous lift through an analytic local homeomorphism preserves real
differentiability, without any continuity assumption on its derivative. -/
theorem realMDifferentiable_of_comp_analytic_localHomeomorph
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} {C : RiemannAtlas Z}
    {f : X → Y} {p : Y → Z}
    (hp : RiemannAnalyticMap B C p) (hpl : IsLocalHomeomorph p) (hf : Continuous f)
    (hcomp : let := A.toChartedSpace; let := C.toChartedSpace;
      MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (p ∘ f)) :
    let := A.toChartedSpace; let := B.toChartedSpace;
      MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f := by
  let := A.toChartedSpace
  let := B.toChartedSpace
  let := C.toChartedSpace
  let := A.isRealManifold
  let := B.isRealManifold
  let := C.isRealManifold
  change MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f
  intro x
  obtain ⟨e, he, hx⟩ := A.cover x
  obtain ⟨g, hg, hy⟩ := B.cover (f x)
  obtain ⟨b, hb, hz⟩ := C.cover (p (f x))
  obtain ⟨P, hPfun, hxP, hP, _⟩ := analyticLocalHomeomorph_coordinateSheet
    hp hpl g hg b hb (f x) hy hz
  have hPv (y : Y) (hyg : y ∈ g.source) : P (g y) = b (p y) := by
    rw [hPfun]
    change b (p (g.symm (g y))) = b (p y)
    rw [g.left_inv hyg]
  have htP : b (p (f x)) ∈ P.target := hPv (f x) hy ▸ P.map_source hxP
  have hi : DifferentiableAt ℝ P.symm (b (p (f x))) :=
    ((openPartialHomeomorph_analytic_inverse P hP) _ htP).differentiableAt.restrictScalars ℝ
  have hforward := realDifferentiableAt_chartMap hcomp e he b hb x hx hz
  have hi' : DifferentiableAt ℝ P.symm (riemannChartMap e (p ∘ f) b (e x)) := by
    simpa only [riemannChartMap, Function.comp_apply, e.left_inv hx] using hi
  have hcompose := hi'.comp (e x) hforward
  have heq : riemannChartMap e f g =ᶠ[𝓝 (e x)] P.symm ∘ riemannChartMap e (p ∘ f) b := by
    have ht : Tendsto (f ∘ e.symm) (𝓝 (e x)) (𝓝 (f x)) := by
      have ht' := hf.continuousAt.comp (e.continuousAt_symm (e.map_source hx))
      change Tendsto (f ∘ e.symm) (𝓝 (e x)) (𝓝 (f (e.symm (e x)))) at ht'
      simpa only [e.left_inv hx] using ht'
    have htcoord := (g.continuousAt hy).tendsto.comp ht
    filter_upwards [ht.eventually (g.open_source.mem_nhds hy),
      htcoord.eventually (P.open_source.mem_nhds hxP)] with w hwg hwp
    change g (f (e.symm w)) = P.symm (b (p (f (e.symm w))))
    rw [← hPv (f (e.symm w)) hwg]
    exact (P.left_inv hwp).symm
  have hlocal := hcompose.congr_of_eventuallyEq heq
  have heMax : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 X :=
    IsManifold.subset_maximalAtlas he
  have hgMax : g ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) 1 Y :=
    IsManifold.subset_maximalAtlas hg
  rw [← mdifferentiableWithinAt_univ]
  apply (mdifferentiableWithinAt_iff_of_mem_maximalAtlas heMax hgMax hx hy).2
  refine ⟨hf.continuousAt.continuousWithinAt, ?_⟩
  simpa only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.range_id, Set.preimage_univ,
    Set.univ_inter, differentiableWithinAt_univ, riemannChartMap] using hlocal

/-- Every continuous map lifts uniquely between the two actual universal
covers after one point is specified. A differentiable or holomorphic base map
has a respectively differentiable or holomorphic lift. -/
theorem universalCover_existsUnique_regular_lift
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    (C : RiemannUniversalCover R) (D : RiemannUniversalCover S)
    (f : C(X, Y)) (c₀ : C.space) (d₀ : D.space)
    (h₀ : D.projection d₀ = f (C.projection c₀)) :
    let := C.topology; let := D.topology;
    ∃! F : C(C.space, D.space), F c₀ = d₀ ∧
      D.projection ∘ F = f ∘ C.projection ∧
      (RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f →
        RiemannAnalyticMap C.surface.toRiemannAtlas D.surface.toRiemannAtlas F) ∧
      ((let := R.toRiemannAtlas.toChartedSpace; let := S.toRiemannAtlas.toChartedSpace;
          MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f) →
        let := C.surface.toRiemannAtlas.toChartedSpace;
        let := D.surface.toRiemannAtlas.toChartedSpace;
          MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F) := by
  let := C.topology
  let := D.topology
  let := C.simplyConnected
  let := C.surface.toRiemannAtlas.toChartedSpace
  let := D.surface.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  obtain ⟨F, ⟨hF₀, hFq, hFa⟩, _⟩ :=
    RiemannAnalyticMap.existsUnique_continuous_lift C.surface.toRiemannAtlas
      D.surface.toRiemannAtlas S.toRiemannAtlas D.covering D.analytic_projection
      ⟨f ∘ C.projection, f.continuous.comp C.covering.continuous⟩ c₀ d₀ h₀
  refine ⟨F, ⟨hF₀, hFq, ?_, ?_⟩, ?_⟩
  · intro hf
    exact hFa.mpr (hf.comp C.analytic_projection)
  · intro hf
    apply realMDifferentiable_of_comp_analytic_localHomeomorph
      D.analytic_projection D.covering.isLocalHomeomorph F.continuous
    rw [hFq]
    exact hf.comp (C.analytic_projection.contMDiff_real.mdifferentiable (by simp))
  · intro G hG
    apply ContinuousMap.ext
    intro c
    exact congrFun (D.covering.eq_of_comp_eq G.continuous F.continuous
      (hG.2.1.trans hFq.symm) c₀ (hG.1.trans hF₀.symm)) c

end LowDimensionalTopology.Geometry.Teichmuller
