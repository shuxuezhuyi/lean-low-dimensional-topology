module
public import LowDimensionalTopology.Geometry.Surfaces.Covering.UniversalCover
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import LowDimensionalTopology.External.LeanPool.Rado.Main
@[expose] public section
noncomputable section
open Set Topology
open scoped Manifold ContDiff
namespace LowDimensionalTopology.Geometry.Surfaces

theorem RiemannAtlas.isManifold {X : Type*} [TopologicalSpace X] (A : RiemannAtlas X) :
    let := A.toChartedSpace
    IsManifold 𝓘(ℂ) ω X := by
  let := A.toChartedSpace
  apply isManifold_of_contDiffOn 𝓘(ℂ) ω X
  intro e f he hf
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ] using
    (A.compatible e he f hf).contDiffOn (n := ω) (e.symm.trans f).open_source.uniqueDiffOn

theorem RiemannSurface.secondCountableTopology {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) : SecondCountableTopology X := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let : IsManifold 𝓘(ℂ) 1 X := IsManifold.of_le (by simp : (1 : ℕ∞ω) ≤ ω)
  exact rado_riemannSurface

theorem RiemannUniversalCover.secondCountableTopology {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} (C : RiemannUniversalCover R) :
    @SecondCountableTopology C.space C.topology := by
  let := C.topology
  exact C.surface.secondCountableTopology


/-- The source definition of analytic maps is the analytic Mathlib manifold-map
property for the charted spaces supplied by the original atlases. -/
theorem RiemannAnalyticMap.contMDiff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} {f : X → Y}
    (hf : RiemannAnalyticMap A B f) :
    let := A.toChartedSpace
    let := B.toChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  let := A.toChartedSpace
  let := B.toChartedSpace
  let := A.isManifold
  let := B.isManifold
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


/-- Analyticity in the manifold language recovers the original, all-chart surface definition. -/
theorem riemannAnalyticMap_of_contMDiff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : RiemannAtlas X) (B : RiemannAtlas Y) (f : X → Y)
    (hf : let := A.toChartedSpace
      let := B.toChartedSpace
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : RiemannAnalyticMap A B f := by
  let := A.toChartedSpace
  let := B.toChartedSpace
  apply (riemannAnalyticMap_iff_locally A B f).mpr
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

/-- The atlas-based and manifold-based analytic map predicates agree exactly. -/
theorem riemannAnalyticMap_iff_contMDiff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : RiemannAtlas X) (B : RiemannAtlas Y) (f : X → Y) :
    RiemannAnalyticMap A B f ↔ let := A.toChartedSpace
      let := B.toChartedSpace
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f :=
  ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.contMDiff, riemannAnalyticMap_of_contMDiff A B f⟩


/-- The atlas of a genuine complex analytic manifold, read in the geometric chart language. -/
def RiemannAtlas.ofManifold (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : RiemannAtlas X where
  charts := atlas ℂ X
  cover x := ⟨chartAt ℂ x, chart_mem_atlas ℂ x, mem_chart_source ℂ x⟩
  compatible e he f hf := by
    have h := ((contDiffGroupoid ω 𝓘(ℂ)).compatible he hf).1
    have hc : ContDiffOn ℂ ω (e.symm.trans f) (e.symm.trans f).source := by
      simpa only [contDiffPregroupoid, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
        Set.preimage_id, Set.range_id, Set.inter_univ] using h
    intro z hz
    exact (hc.contDiffAt ((e.symm.trans f).open_source.mem_nhds hz)).analyticAt

/-- The original Hausdorff connected surface associated with an analytic complex manifold. -/
def RiemannSurface.ofManifold (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [T2Space X] [ConnectedSpace X] : RiemannSurface X where
  toRiemannAtlas := _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAtlas.ofManifold X
  t2Space := inferInstance
  connectedSpace := inferInstance

end LowDimensionalTopology.Geometry.Surfaces
