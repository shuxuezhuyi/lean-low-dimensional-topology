module
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Atlas
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Covering.PathLifting

/-!
# Pulling back complex atlases along covering maps.

A local homeomorphism pulls back a complex atlas. The projection and commuting lifted maps
are analytic in these atlases, and connected coverings inherit Riemann surface structures.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology unitInterval

namespace LowDimensionalTopology.Geometry.Surfaces

/-- The pulled-back chart family: every local inverse sheet followed by a base chart. -/
def coveringLiftedCharts {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    (A : RiemannAtlas X) (p : Y → X) : Set (OpenPartialHomeomorph Y ℂ) :=
  {e | ∃ l : OpenPartialHomeomorph Y X, p = l ∧ ∃ b ∈ A.charts, e = l.trans b}

/-- The pulled-back chart domains truly cover the total space in its given topology. -/
theorem coveringLiftedCharts_cover {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    (A : RiemannAtlas X) (p : Y → X) (hp : IsLocalHomeomorph p) (y : Y) :
    ∃ e ∈ coveringLiftedCharts A p, y ∈ e.source := by
  obtain ⟨l, hyl, hl⟩ := hp y
  obtain ⟨b, hb, hyb⟩ := A.cover (p y)
  refine ⟨l.trans b, ⟨l, hl, b, hb, rfl⟩, hyl, ?_⟩
  change l y ∈ b.source
  rwa [← hl]

/-- Projection of an actual inverse lifted chart is exactly the inverse base chart. -/
theorem coveringLiftedChart_project_symm {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    (p : Y → X) (l : OpenPartialHomeomorph Y X) (hl : p = l)
    (b : OpenPartialHomeomorph X ℂ) (z : ℂ) (hz : z ∈ (l.trans b).target) :
    p ((l.trans b).symm z) = b.symm z := by
  change p (l.symm (b.symm z)) = b.symm z
  rw [hl, l.right_inv hz.2]

/-- Lifted chart transitions agree locally with genuine base transitions and are therefore analytic. -/
theorem coveringLiftedCharts_compatible {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    (A : RiemannAtlas X) (p : Y → X)
    (e : OpenPartialHomeomorph Y ℂ) (he : e ∈ coveringLiftedCharts A p)
    (f : OpenPartialHomeomorph Y ℂ) (hf : f ∈ coveringLiftedCharts A p) :
    AnalyticOnNhd ℂ (e.symm.trans f) (e.symm.trans f).source := by
  obtain ⟨l₁, hl₁, b₁, hb₁, rfl⟩ := he
  obtain ⟨l₂, hl₂, b₂, hb₂, rfl⟩ := hf
  have hsub : ((l₁.trans b₁).symm.trans (l₂.trans b₂)).source ⊆ (b₁.symm.trans b₂).source := by
    intro z hz
    have hproj := coveringLiftedChart_project_symm p l₁ hl₁ b₁ z hz.1
    refine ⟨hz.1.1, ?_⟩
    change b₁.symm z ∈ b₂.source
    rw [← hproj, hl₂]
    exact hz.2.2
  apply AnalyticOnNhd.congr ((l₁.trans b₁).symm.trans (l₂.trans b₂)).open_source
    ((A.compatible b₁ hb₁ b₂ hb₂).mono hsub)
  intro z hz
  change b₂ (b₁.symm z) = b₂ (l₂ ((l₁.trans b₁).symm z))
  rw [← hl₂, coveringLiftedChart_project_symm p l₁ hl₁ b₁ z hz.1]

/-- Every local homeomorphism over a Riemann atlas canonically pulls back its true complex atlas. -/
def RiemannAtlas.liftLocalHomeomorph {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    (A : RiemannAtlas X) (p : Y → X) (hp : IsLocalHomeomorph p) : RiemannAtlas Y where
  charts := coveringLiftedCharts A p
  cover := coveringLiftedCharts_cover A p hp
  compatible := coveringLiftedCharts_compatible A p

/-- The projection is genuinely analytic in the pulled-back atlas and the original base atlas. -/
theorem RiemannAtlas.liftLocalHomeomorph_projection_analytic {Y X : Type*}
    [TopologicalSpace Y] [TopologicalSpace X] (A : RiemannAtlas X) (p : Y → X)
    (hp : IsLocalHomeomorph p) : RiemannAnalyticMap (A.liftLocalHomeomorph p hp) A p := by
  refine ⟨hp.continuous, ?_⟩
  intro e he g hg
  obtain ⟨l, hl, b, hb, rfl⟩ := he
  have hsub : riemannChartMapDomain (l.trans b) p g ⊆ (b.symm.trans g).source := by
    intro z hz
    refine ⟨hz.1.1, ?_⟩
    change b.symm z ∈ g.source
    rw [← coveringLiftedChart_project_symm p l hl b z hz.1]
    exact hz.2
  apply AnalyticOnNhd.congr (riemannChartMapDomain_isOpen (l.trans b) p g hp.continuous)
    ((A.compatible b hb g hg).mono hsub)
  intro z hz
  change g (b.symm z) = g (p ((l.trans b).symm z))
  rw [coveringLiftedChart_project_symm p l hl b z hz.1]

/-- A genuine covering of a Hausdorff base has a Hausdorff total space, with no extra separation hypothesis. -/
theorem covering_t2Space {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X] [T2Space X]
    {p : Y → X} (hp : IsCoveringMap p) : T2Space Y := by
  constructor
  intro y z hyz
  by_cases heq : p y = p z
  · exact hp.isSeparatedMap y z heq hyz
  · obtain ⟨U, V, hU, hV, hyU, hzV, hUV⟩ := t2_separation heq
    exact ⟨p ⁻¹' U, p ⁻¹' V, hU.preimage hp.continuous, hV.preimage hp.continuous,
      hyU, hzV, hUV.preimage p⟩

/-- A connected actual topological covering of a Riemann surface inherits a true Riemann surface structure. -/
def coveringRiemannSurface {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    [ConnectedSpace Y] (A : RiemannSurface X) (p : Y → X) (hp : IsCoveringMap p) : RiemannSurface Y where
  toRiemannAtlas := A.toRiemannAtlas.liftLocalHomeomorph p hp.isLocalHomeomorph
  t2Space := by
    let := A.t2Space
    exact covering_t2Space hp
  connectedSpace := inferInstance

/-- A connected covering inherits a complex surface structure with analytic projection
and the local-homeomorphism and path-lifting properties. -/
theorem covering_exists_riemannSurface {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    [ConnectedSpace Y] (A : RiemannSurface X) (p : Y → X) (hp : IsCoveringMap p) :
    ∃ B : RiemannSurface Y, RiemannAnalyticMap B.toRiemannAtlas A.toRiemannAtlas p ∧
      Auxiliary.Topology.IsSmoothUnlimitedCovering p := by
  exact ⟨coveringRiemannSurface A p hp,
    A.toRiemannAtlas.liftLocalHomeomorph_projection_analytic p hp.isLocalHomeomorph,
    Auxiliary.Topology.covering_isSmoothUnlimited hp⟩

/-- A genuine complex atlas makes its original topological carrier locally compact. -/
theorem RiemannAtlas.locallyCompactSpace {X : Type*} [TopologicalSpace X] (A : RiemannAtlas X) :
    LocallyCompactSpace X := by
  let := A.toChartedSpace
  exact ChartedSpace.locallyCompactSpace ℂ X

/-- The source atlas gives local path connectedness without a countability hypothesis. -/
theorem RiemannAtlas.locallyPathConnectedSpace {X : Type*} [TopologicalSpace X] (A : RiemannAtlas X) :
    LocallyPathConnectedSpace X := by
  let := A.toChartedSpace
  exact ChartedSpace.locallyPathConnectedSpace ℂ X

/-- A connected Riemann surface is actually path connected, as required for covering theory. -/
theorem RiemannSurface.pathConnectedSpace {X : Type*} [TopologicalSpace X] (A : RiemannSurface X) :
    PathConnectedSpace X := by
  let := A.connectedSpace
  let := A.toRiemannAtlas.locallyPathConnectedSpace
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-- A nonempty covering of a Riemann surface is surjective. -/
theorem covering_surjective_of_riemann_base {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    [Nonempty Y] (A : RiemannSurface X) {p : Y → X} (hp : IsCoveringMap p) : Function.Surjective p := by
  let := A.pathConnectedSpace
  let y : Y := Classical.choice inferInstance
  intro x
  obtain ⟨z, hz⟩ := hp.comp_subtypeVal_pathComponent_surjective y x
  exact ⟨z.val, hz⟩

/-- Analytic maps commuting with genuine local-homeomorphic projections lift analytically
in the actual pulled-back atlases. -/
theorem RiemannAnalyticMap.liftLocalHomeomorph
    {X Y X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    {A : RiemannAtlas X} {B : RiemannAtlas Y}
    (p : X' → X) (q : Y' → Y) (hp : IsLocalHomeomorph p) (hq : IsLocalHomeomorph q)
    (F : X → Y) (f : X' → Y') (hF : RiemannAnalyticMap A B F)
    (hf : Continuous f) (hcomm : ∀ x, q (f x) = F (p x)) :
    RiemannAnalyticMap (A.liftLocalHomeomorph p hp) (B.liftLocalHomeomorph q hq) f := by
  refine ⟨hf, ?_⟩
  intro e he g hg
  obtain ⟨l₁, hl₁, b₁, hb₁, rfl⟩ := he
  obtain ⟨l₂, hl₂, b₂, hb₂, rfl⟩ := hg
  have hsub : riemannChartMapDomain (l₁.trans b₁) f (l₂.trans b₂) ⊆
      riemannChartMapDomain b₁ F b₂ := by
    intro z hz
    refine ⟨hz.1.1, ?_⟩
    change F (b₁.symm z) ∈ b₂.source
    rw [← coveringLiftedChart_project_symm p l₁ hl₁ b₁ z hz.1, ← hcomm, hl₂]
    exact hz.2.2
  apply AnalyticOnNhd.congr
    (riemannChartMapDomain_isOpen (l₁.trans b₁) f (l₂.trans b₂) hf)
    ((hF.2 b₁ hb₁ b₂ hb₂).mono hsub)
  intro z hz
  change b₂ (F (b₁.symm z)) = b₂ (l₂ (f ((l₁.trans b₁).symm z)))
  rw [← hl₂, hcomm, coveringLiftedChart_project_symm p l₁ hl₁ b₁ z hz.1]

end LowDimensionalTopology.Geometry.Surfaces
