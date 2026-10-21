module
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannManifold
public import Mathlib.Geometry.Manifold.Diffeomorph
@[expose] public section
noncomputable section
open Set Topology
open scoped Manifold ContDiff
namespace LowDimensionalTopology.Geometry.Surfaces

/-- A bijective analytic map in the original atlas language gives a genuine analytic
Mathlib diffeomorphism, with no nonvanishing derivative added as a hypothesis. -/
def RiemannAnalyticMap.toDiffeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} {f : X → Y}
    (hf : RiemannAnalyticMap A B f) (hbij : Function.Bijective f) :
    let := A.toChartedSpace
    let := B.toChartedSpace
    X ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ Y := by
  let := A.toChartedSpace
  let := B.toChartedSpace
  let E := hf.toHomeomorph hbij
  exact
    { toEquiv := E.toEquiv
      contMDiff_toFun := hf.contMDiff
      contMDiff_invFun := (riemannAnalyticMap_homeomorph_symm E hf).contMDiff }

@[simp] theorem RiemannAnalyticMap.toDiffeomorph_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} {f : X → Y}
    (hf : RiemannAnalyticMap A B f) (hbij : Function.Bijective f) (x : X) :
    (hf.toDiffeomorph hbij) x = f x := rfl

/-- A genuine analytic diffeomorphism between the original atlas-derived manifolds is
an analytic map in the original, all-chart language. -/
theorem riemannAnalyticMap_of_diffeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : RiemannAtlas X) (B : RiemannAtlas Y)
    (E : let := A.toChartedSpace
      let := B.toChartedSpace
      X ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ Y) : RiemannAnalyticMap A B E := by
  let := A.toChartedSpace
  let := B.toChartedSpace
  exact riemannAnalyticMap_of_contMDiff A B E E.contMDiff_toFun

/-- The source definition of conformal equivalence is exactly existence of a genuine
complex analytic Mathlib diffeomorphism in the original atlas structures. -/
theorem riemannConformallyEquivalent_iff_nonempty_diffeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (R : RiemannSurface X) (S : RiemannSurface Y) :
    RiemannConformallyEquivalent R S ↔
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      Nonempty (X ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ Y) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  constructor
  · rintro ⟨f, hf, hbij⟩
    exact ⟨hf.toDiffeomorph hbij⟩
  · rintro ⟨E⟩
    exact ⟨E, riemannAnalyticMap_of_diffeomorph R.toRiemannAtlas S.toRiemannAtlas E, E.bijective⟩


/-- On a given Mathlib analytic manifold, original all-chart analyticity recovers the
native manifold map predicate, without replacing its chosen chartAt function. -/
theorem RiemannAnalyticMap.contMDiff_ofManifold {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] {f : X → Y}
    (hf : RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas.ofManifold X)
      (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas.ofManifold Y) f) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  rw [contMDiff_iff]
  refine ⟨hf.continuous, ?_⟩
  intro x y
  have h := (hf.2 (chartAt ℂ x) (chart_mem_atlas ℂ x)
    (chartAt ℂ y) (chart_mem_atlas ℂ y)).contDiffOn (n := ω)
      (riemannChartMapDomain_isOpen _ f _ hf.continuous).uniqueDiffOn
  simpa only [extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_target,
    OpenPartialHomeomorph.extend_source, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    Set.preimage_id, Set.range_id, Set.inter_univ, riemannChartMap, riemannChartMapDomain] using h

/-- Native analytic manifold maps satisfy the original Riemann-atlas map definition,
using the actual original charts of the given manifolds. -/
theorem riemannAnalyticMap_of_contMDiff_ofManifold {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas.ofManifold X) (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas.ofManifold Y) f := by
  apply (riemannAnalyticMap_iff_locally (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas.ofManifold X)
    (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas.ofManifold Y) f).mpr
  refine ⟨hf.continuous, ?_⟩
  intro x
  refine ⟨chartAt ℂ x, chart_mem_atlas ℂ x, mem_chart_source ℂ x,
    chartAt ℂ (f x), chart_mem_atlas ℂ (f x), mem_chart_source ℂ (f x), ?_⟩
  have hc := (contMDiffAt_iff.mp (hf.contMDiffAt (x := x))).2
  have h : ContDiffAt ℂ ω (riemannChartMap (chartAt ℂ x) f (chartAt ℂ (f x)))
      (chartAt ℂ x x) := by
    simpa only [extChartAt, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
      Set.range_id, contDiffWithinAt_univ, riemannChartMap] using hc
  exact h.analyticAt

/-- The original and native analytic map predicates agree for given manifold structures;
there is no equality assumption on chartAt after an atlas round trip. -/
theorem riemannAnalyticMap_ofManifold_iff_contMDiff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) :
    RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas.ofManifold
      X) (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas.ofManifold Y) f ↔
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f :=
  ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.contMDiff_ofManifold,
    riemannAnalyticMap_of_contMDiff_ofManifold⟩

/-- A source-language analytic bijection between given analytic manifolds gives a
native analytic diffeomorphism in those very manifold structures. -/
def RiemannAnalyticMap.toManifoldDiffeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] {f : X → Y}
    (hf : RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas.ofManifold X)
      (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas.ofManifold Y) f)
    (hbij : Function.Bijective f) : X ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ Y := by
  let E := hf.toHomeomorph hbij
  exact
    { toEquiv := E.toEquiv
      contMDiff_toFun := hf.contMDiff_ofManifold
      contMDiff_invFun := (riemannAnalyticMap_homeomorph_symm E hf).contMDiff_ofManifold }

/-- Conformal equivalence of the surfaces of two given analytic manifolds is exactly
existence of an analytic diffeomorphism in their native manifold structures. -/
theorem riemannConformallyEquivalent_ofManifold_iff_nonempty_diffeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [T2Space X] [ConnectedSpace X] [T2Space Y] [ConnectedSpace Y] :
    RiemannConformallyEquivalent (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold
      X) (_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface.ofManifold Y) ↔
      Nonempty (X ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ Y) := by
  constructor
  · rintro ⟨f, hf, hbij⟩
    exact ⟨hf.toManifoldDiffeomorph hbij⟩
  · rintro ⟨E⟩
    exact ⟨E, riemannAnalyticMap_of_contMDiff_ofManifold E.contMDiff_toFun, E.bijective⟩

end LowDimensionalTopology.Geometry.Surfaces
