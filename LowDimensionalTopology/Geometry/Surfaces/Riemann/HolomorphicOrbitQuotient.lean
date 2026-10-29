module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicCovering
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.Discontinuity
public import Mathlib.Topology.Covering.Quotient

/-!
# Riemann surfaces from free properly discontinuous holomorphic actions

The carrier is the actual orbit quotient with its quotient topology. Its charts
are original complex charts following genuine local inverse sheets of the orbit
projection. On overlaps, the two sheets differ locally by an actual group
element. Holomorphicity of that action proves compatibility of the quotient
charts, without a pre-existing quotient complex structure or a special model
for the original surface. The projection has identity local coordinate maps in
both directions and is an open holomorphic covering.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology

namespace LowDimensionalTopology.Geometry.Surfaces

universe u v
variable {X : Type u} [TopologicalSpace X]
variable (G : Type v) [Group G] [MulAction G X]

/-- Original charts following actual local inverse sheets of the orbit map. -/
def holomorphicOrbitCharts (A : RiemannAtlas X) :
    Set (OpenPartialHomeomorph (Quotient (MulAction.orbitRel G X)) ℂ) :=
  {e | ∃ l : OpenPartialHomeomorph X (Quotient (MulAction.orbitRel G X)),
    (Quotient.mk (MulAction.orbitRel G X) : X → _) = l ∧
      ∃ b ∈ A.charts, e = l.symm.trans b}

/-- Local inverse sheets and original coordinates cover the actual quotient. -/
theorem holomorphicOrbitCharts_cover (A : RiemannAtlas X)
    (hq : IsLocalHomeomorph (Quotient.mk (MulAction.orbitRel G X)))
    (y : Quotient (MulAction.orbitRel G X)) :
    ∃ e ∈ holomorphicOrbitCharts G A, y ∈ e.source := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep y
  obtain ⟨l, hxl, hl⟩ := hq x
  obtain ⟨b, hb, hxb⟩ := A.cover x
  refine ⟨l.symm.trans b, ⟨l, hl, b, hb, rfl⟩, ?_, ?_⟩
  · rw [hl]
    exact l.map_source hxl
  · change b.source (l.symm (Quotient.mk (MulAction.orbitRel G X) x))
    rw [hl, l.left_inv hxl]
    exact hxb

/-- Quotient chart transitions are locally the coordinate expressions of an
actual action element. No smoothness of the group as a parameter is assumed. -/
theorem holomorphicOrbitCharts_compatible (A : RiemannAtlas X)
    (ha : ∀ g : G, RiemannAnalyticMap A A (fun x : X => g • x))
    (e : OpenPartialHomeomorph (Quotient (MulAction.orbitRel G X)) ℂ)
    (he : e ∈ holomorphicOrbitCharts G A)
    (f : OpenPartialHomeomorph (Quotient (MulAction.orbitRel G X)) ℂ)
    (hf : f ∈ holomorphicOrbitCharts G A) :
    AnalyticOnNhd ℂ (e.symm.trans f) (e.symm.trans f).source := by
  obtain ⟨l₁, hl₁, b₁, hb₁, rfl⟩ := he
  obtain ⟨l₂, hl₂, b₂, hb₂, rfl⟩ := hf
  intro z hz
  let q : X → Quotient (MulAction.orbitRel G X) := Quotient.mk _
  let x := b₁.symm z
  let y := l₂.symm (l₁ x)
  have hqy : q y = q x := by
    calc
      q y = l₂ y := congrFun hl₂ y
      _ = l₁ x := l₂.right_inv hz.2.1
      _ = q x := (congrFun hl₁ x).symm
  obtain ⟨g, hg⟩ := (Quotient.exact hqy : MulAction.orbitRel G X y x)
  change g • x = y at hg
  have hgb : g • b₁.symm z ∈ b₂.source := by
    change g • x ∈ b₂.source
    rw [hg]
    exact hz.2.2
  have han : AnalyticAt ℂ (riemannChartMap b₁ (fun t : X => g • t) b₂) z :=
    (ha g).2 b₁ hb₁ b₂ hb₂ z ⟨hz.1.1, hgb⟩
  have hnear : ∀ᶠ w in 𝓝 z, g • b₁.symm w ∈ l₂.source := by
    have hy : y ∈ l₂.source := l₂.map_target hz.2.1
    have hy' : g • b₁.symm z ∈ l₂.source := by
      change g • x ∈ l₂.source
      rwa [hg]
    exact ((ha g).1.continuousAt.comp
      (b₁.continuousAt_symm hz.1.1)).eventually (l₂.open_source.mem_nhds hy')
  apply han.congr
  filter_upwards [hnear] with w hw
  have hqg : q (g • b₁.symm w) = q (b₁.symm w) := Quotient.sound ⟨g, rfl⟩
  have hsheet : l₂ (g • b₁.symm w) = l₁ (b₁.symm w) :=
    (congrFun hl₂ _).symm.trans (hqg.trans (congrFun hl₁ _))
  change b₂ (g • b₁.symm w) = b₂ (l₂.symm (l₁ (b₁.symm w)))
  rw [← hsheet, l₂.left_inv hw]

/-- The original complex atlas descends through the actual free orbit cover. -/
def holomorphicOrbitAtlas (A : RiemannAtlas X)
    (ha : ∀ g : G, RiemannAnalyticMap A A (fun x : X => g • x))
    (hq : IsLocalHomeomorph (Quotient.mk (MulAction.orbitRel G X))) :
    RiemannAtlas (Quotient (MulAction.orbitRel G X)) where
  charts := holomorphicOrbitCharts G A
  cover := holomorphicOrbitCharts_cover G A hq
  compatible := holomorphicOrbitCharts_compatible G A ha

/-- The projection is analytic in the original atlas and the constructed
quotient atlas, rather than in an assumed replacement source atlas. -/
theorem holomorphicOrbitAtlas_projection_analytic (A : RiemannAtlas X)
    (ha : ∀ g : G, RiemannAnalyticMap A A (fun x : X => g • x))
    (hq : IsLocalHomeomorph (Quotient.mk (MulAction.orbitRel G X))) :
    RiemannAnalyticMap A (holomorphicOrbitAtlas G A ha hq)
      (Quotient.mk (MulAction.orbitRel G X)) := by
  apply (riemannAnalyticMap_iff_locally A (holomorphicOrbitAtlas G A ha hq) _).mpr
  refine ⟨continuous_quot_mk, ?_⟩
  intro x
  obtain ⟨l, hxl, hl⟩ := hq x
  obtain ⟨b, hb, hxb⟩ := A.cover x
  have hxq : Quotient.mk (MulAction.orbitRel G X) x ∈ (l.symm.trans b).source := by
    refine ⟨?_, ?_⟩
    · rw [hl]
      exact l.map_source hxl
    · change l.symm (Quotient.mk (MulAction.orbitRel G X) x) ∈ b.source
      rw [hl, l.left_inv hxl]
      exact hxb
  refine ⟨b, hb, hxb, l.symm.trans b, ⟨l, hl, b, hb, rfl⟩, hxq, ?_⟩
  have hls : l.source ∈ 𝓝 (b.symm (b x)) := by
    rw [b.left_inv hxb]
    exact l.open_source.mem_nhds hxl
  have hsource : {w : ℂ | b.symm w ∈ l.source} ∈ 𝓝 (b x) :=
    (b.continuousAt_symm (b.map_source hxb)).eventually hls
  have hnear : ∀ᶠ w in 𝓝 (b x), w ∈ b.target ∧ b.symm w ∈ l.source :=
    inter_mem (b.open_target.mem_nhds (b.map_source hxb)) hsource
  apply analyticAt_id.congr
  filter_upwards [hnear] with w hw
  change w = b (l.symm (Quotient.mk (MulAction.orbitRel G X) (b.symm w)))
  rw [hl, l.left_inv hw.2, b.right_inv hw.1]

/-- In paired original/quotient coordinates the actual projection and its
actual local inverse are both the identity. This records local biholomorphicity
without adding a nonzero-derivative premise. -/
theorem holomorphicOrbitAtlas_local_coordinates (A : RiemannAtlas X)
    (ha : ∀ g : G, RiemannAnalyticMap A A (fun x : X => g • x))
    (hq : IsLocalHomeomorph (Quotient.mk (MulAction.orbitRel G X))) (x : X) :
    ∃ l : OpenPartialHomeomorph X (Quotient (MulAction.orbitRel G X)),
      (Quotient.mk (MulAction.orbitRel G X) : X → _) = l ∧ x ∈ l.source ∧
      ∃ b ∈ A.charts, x ∈ b.source ∧
        l.symm.trans b ∈ (holomorphicOrbitAtlas G A ha hq).charts ∧
        EqOn (riemannChartMap b (Quotient.mk (MulAction.orbitRel G X)) (l.symm.trans b))
          id (l.symm.trans b).target ∧
        EqOn (riemannChartMap (l.symm.trans b) l.symm b) id (l.symm.trans b).target := by
  obtain ⟨l, hxl, hl⟩ := hq x
  obtain ⟨b, hb, hxb⟩ := A.cover x
  refine ⟨l, hl, hxl, b, hb, hxb, ⟨l, hl, b, hb, rfl⟩, ?_, ?_⟩
  · intro z hz
    change z ∈ b.target ∧ b.symm z ∈ l.source at hz
    change b (l.symm (Quotient.mk (MulAction.orbitRel G X) (b.symm z))) = z
    rw [hl, l.left_inv hz.2, b.right_inv hz.1]
  · intro z hz
    change z ∈ b.target ∧ b.symm z ∈ l.source at hz
    change b (l.symm (l (b.symm z))) = z
    rw [l.left_inv hz.2, b.right_inv hz.1]

/-- The book's single-compact-set properness and absence of nontrivial fixed
points give the actual quotient covering. Holomorphicity supplies continuity. -/
theorem holomorphicOrbitProjection_quotientCovering (R : RiemannSurface X)
    (ha : ∀ g : G, RiemannAnalyticMap R.toRiemannAtlas R.toRiemannAtlas (fun x : X => g • x))
    (hproper : DiscreteGroups.Action.IsDiscontinuous G X)
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel G X)) G := by
  let : T2Space X := R.t2Space
  let : LocallyCompactSpace X := R.toRiemannAtlas.locallyCompactSpace
  let : ContinuousConstSMul G X := ⟨fun g => (ha g).1⟩
  let : ProperlyDiscontinuousSMul G X :=
    (DiscreteGroups.Action.isDiscontinuous_iff_properlyDiscontinuousSMul G X).mp hproper
  let : IsCancelSMul G X := isCancelSMul_iff_eq_one_of_smul_eq.mpr hfree
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- The Hausdorff connected Riemann surface on the actual orbit quotient of the
given original surface. No standard-domain or simply-connectedness assumption is used. -/
def holomorphicOrbitSurface (R : RiemannSurface X)
    (ha : ∀ g : G, RiemannAnalyticMap R.toRiemannAtlas R.toRiemannAtlas (fun x : X => g • x))
    (hproper : DiscreteGroups.Action.IsDiscontinuous G X)
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) :
    RiemannSurface (Quotient (MulAction.orbitRel G X)) := by
  let : T2Space X := R.t2Space
  let : LocallyCompactSpace X := R.toRiemannAtlas.locallyCompactSpace
  let : ConnectedSpace X := R.connectedSpace
  let : ContinuousConstSMul G X := ⟨fun g => (ha g).1⟩
  let : ProperlyDiscontinuousSMul G X :=
    (DiscreteGroups.Action.isDiscontinuous_iff_properlyDiscontinuousSMul G X).mp hproper
  exact
    { toRiemannAtlas := holomorphicOrbitAtlas G R.toRiemannAtlas ha
        (holomorphicOrbitProjection_quotientCovering G R ha hproper hfree).isLocalHomeomorph
      t2Space := inferInstance
      connectedSpace := inferInstance }

/-- The actual orbit projection is an open holomorphic covering in the original
source surface and the constructed quotient surface. -/
theorem holomorphicOrbitSurface_projection (R : RiemannSurface X)
    (ha : ∀ g : G, RiemannAnalyticMap R.toRiemannAtlas R.toRiemannAtlas (fun x : X => g • x))
    (hproper : DiscreteGroups.Action.IsDiscontinuous G X)
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) :
    IsRiemannCovering R (holomorphicOrbitSurface G R ha hproper hfree)
      (Quotient.mk (MulAction.orbitRel G X)) ∧
      IsOpenMap (Quotient.mk (MulAction.orbitRel G X)) := by
  have hq := holomorphicOrbitProjection_quotientCovering G R ha hproper hfree
  refine ⟨⟨Quotient.mk_surjective, hq.isCoveringMap, ?_⟩, hq.isCoveringMap.isOpenMap⟩
  exact holomorphicOrbitAtlas_projection_analytic G R.toRiemannAtlas ha hq.isLocalHomeomorph

end LowDimensionalTopology.Geometry.Surfaces
