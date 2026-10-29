module
public import LowDimensionalTopology.Geometry.Surfaces.Covering.UniversalCover
public import LowDimensionalTopology.Geometry.Surfaces.Covering.UniversalDeck
@[expose] public section
noncomputable section
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Surfaces

/-- A continuous lift through an analytic local homeomorphism is analytic in the given
complex atlases, without changing either atlas or assuming an unramified derivative. -/
theorem RiemannAnalyticMap.of_comp_localHomeomorph
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} {C : RiemannAtlas Z}
    {f : X → Y} {q : Y → Z} (hq : RiemannAnalyticMap B C q)
    (hql : IsLocalHomeomorph q) (hf : Continuous f)
    (ha : RiemannAnalyticMap A C (q ∘ f)) : RiemannAnalyticMap A B f := by
  rw [riemannAnalyticMap_iff_locally]
  refine ⟨hf, ?_⟩
  intro x
  obtain ⟨e, he, hx⟩ := A.cover x
  obtain ⟨g, hg, hy⟩ := B.cover (f x)
  obtain ⟨b, hb, hz⟩ := C.cover (q (f x))
  obtain ⟨l, hlx, hl⟩ := hql (f x)
  let P := g.symm.trans (l.trans b)
  have hsub : P.source ⊆ riemannChartMapDomain g q b := by
    intro w hw
    change w ∈ g.target ∧ g.symm w ∈ l.source ∧ l (g.symm w) ∈ b.source at hw
    refine ⟨hw.1, ?_⟩
    change q (g.symm w) ∈ b.source
    rw [hl]
    exact hw.2.2
  have hP : AnalyticOnNhd ℂ P P.source := by
    apply AnalyticOnNhd.congr P.open_source
      ((hq.2 g hg b hb).mono hsub)
    intro w _hw
    change b (q (g.symm w)) = b (l (g.symm w))
    rw [hl]
  have hPs : g (f x) ∈ P.source := by
    change g (f x) ∈ g.target ∧ g.symm (g (f x)) ∈ l.source ∧
      l (g.symm (g (f x))) ∈ b.source
    rw [g.left_inv hy, ← hl]
    exact ⟨g.map_source hy, hlx, hz⟩
  have hPv (y : Y) (hyg : y ∈ g.source) : P (g y) = b (q y) := by
    change b (l (g.symm (g y))) = b (q y)
    rw [g.left_inv hyg, ← hl]
  have hi := openPartialHomeomorph_analytic_inverse P hP
  have hai : AnalyticAt ℂ P.symm (b (q (f x))) := by
    rw [← hPv (f x) hy]
    exact hi _ (P.map_source hPs)
  have hforward : AnalyticAt ℂ (riemannChartMap e (q ∘ f) b) (e x) :=
    ha.2 e he b hb (e x) (riemannChartMapDomain_mem e (q ∘ f) b x hx hz)
  have hcompose : AnalyticAt ℂ (P.symm ∘ riemannChartMap e (q ∘ f) b) (e x) := by
    apply AnalyticAt.comp (f := riemannChartMap e (q ∘ f) b) (x := e x) ?_ hforward
    simpa only [riemannChartMap, Function.comp_apply, e.left_inv hx] using hai
  refine ⟨e, he, hx, g, hg, hy, hcompose.congr ?_⟩
  have hnear : ∀ᶠ w in 𝓝 (e x),
      f (e.symm w) ∈ g.source ∧ f (e.symm w) ∈ l.source ∧
        q (f (e.symm w)) ∈ b.source := by
    have ht : Tendsto (f ∘ e.symm) (𝓝 (e x)) (𝓝 (f x)) := by
      have hc := hf.continuousAt.comp (e.continuousAt_symm (e.map_source hx))
      change Tendsto (f ∘ e.symm) (𝓝 (e x)) (𝓝 (f (e.symm (e x)))) at hc
      simpa only [e.left_inv hx] using hc
    exact ht.eventually ((g.open_source.inter (l.open_source.inter
      (b.open_source.preimage hq.1))).mem_nhds ⟨hy, hlx, hz⟩)
  filter_upwards [hnear] with w hw
  let y := f (e.symm w)
  have hgy : g y ∈ P.source := by
    change g y ∈ g.target ∧ g.symm (g y) ∈ l.source ∧ l (g.symm (g y)) ∈ b.source
    rw [g.left_inv hw.1, ← hl]
    exact ⟨g.map_source hw.1, hw.2.1, hw.2.2⟩
  change P.symm (b (q y)) = g y
  rw [← hPv y hw.1, P.left_inv hgy]

/-- Every deck transformation of an analytic cover is analytic in the original source atlas. -/
theorem covering_deck_analytic_of_analytic {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {A : RiemannAtlas E} {B : RiemannAtlas X} {p : E → X}
    (hp : IsCoveringMap p) (ha : RiemannAnalyticMap A B p) (g : deck p) :
    RiemannAnalyticMap A A g.val := by
  apply RiemannAnalyticMap.of_comp_localHomeomorph ha hp.isLocalHomeomorph g.val.continuous
  have he : (p ∘ (g.val : E → E)) = p := g.property
  rw [he]
  exact ha

/-- A continuous map from a simply connected complex atlas lifts uniquely through an
analytic covering, and the lift is analytic exactly when the original map is analytic. -/
theorem RiemannAnalyticMap.existsUnique_continuous_lift
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [SimplyConnectedSpace X] (A : RiemannAtlas X) (B : RiemannAtlas Y)
    (C : RiemannAtlas Z) {q : Y → Z} (hq : IsCoveringMap q)
    (haq : RiemannAnalyticMap B C q) (f : C(X, Z))
    (x₀ : X) (y₀ : Y) (hy₀ : q y₀ = f x₀) :
    ∃! F : C(X, Y), F x₀ = y₀ ∧ q ∘ F = f ∧
      (RiemannAnalyticMap A B F ↔ RiemannAnalyticMap A C f) := by
  let : LocallyPathConnectedSpace X := A.locallyPathConnectedSpace
  obtain ⟨F, ⟨hF₀, hFq⟩, hFu⟩ := hq.existsUnique_continuousMap_lifts f x₀ y₀ hy₀
  have hFa : RiemannAnalyticMap A B F ↔ RiemannAnalyticMap A C f := by
    constructor
    · intro hF
      have hcomp := haq.comp hF
      rwa [hFq] at hcomp
    · intro hf
      apply RiemannAnalyticMap.of_comp_localHomeomorph haq hq.isLocalHomeomorph F.continuous
      rwa [hFq]
  exact ⟨F, ⟨hF₀, hFq, hFa⟩, fun F' hF' => hFu F' ⟨hF'.1, hF'.2.1⟩⟩

/-- Two universal covering Riemann surfaces have a unique biholomorphic homeomorphism
commuting with their projections and carrying one prescribed point to the other. -/
theorem RiemannUniversalCover.existsUnique_analytic_homeomorph_over
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (C D : RiemannUniversalCover R) (c₀ : C.space) (d₀ : D.space)
    (h₀ : C.projection c₀ = D.projection d₀) :
    let := C.topology
    let := D.topology
    ∃! e : C.space ≃ₜ D.space,
      e c₀ = d₀ ∧ D.projection ∘ e = C.projection ∧
        RiemannAnalyticMap C.surface.toRiemannAtlas D.surface.toRiemannAtlas e ∧
        RiemannAnalyticMap D.surface.toRiemannAtlas C.surface.toRiemannAtlas e.symm := by
  let : TopologicalSpace C.space := C.topology
  let : TopologicalSpace D.space := D.topology
  let : SimplyConnectedSpace C.space := C.simplyConnected
  let : SimplyConnectedSpace D.space := D.simplyConnected
  obtain ⟨F, ⟨hF₀, hFq, hFa⟩, _⟩ :=
    RiemannAnalyticMap.existsUnique_continuous_lift C.surface.toRiemannAtlas
      D.surface.toRiemannAtlas R.toRiemannAtlas D.covering D.analytic_projection
      ⟨C.projection, C.covering.continuous⟩ c₀ d₀ h₀.symm
  obtain ⟨G, ⟨hG₀, hGq, hGa⟩, _⟩ :=
    RiemannAnalyticMap.existsUnique_continuous_lift D.surface.toRiemannAtlas
      C.surface.toRiemannAtlas R.toRiemannAtlas C.covering C.analytic_projection
      ⟨D.projection, D.covering.continuous⟩ d₀ c₀ h₀
  have hGF : (G ∘ F : C.space → C.space) = id :=
    C.covering.eq_of_comp_eq (G.continuous.comp F.continuous) continuous_id
      (by funext c; exact (congrFun hGq (F c)).trans (congrFun hFq c))
      c₀ (by simp only [Function.comp_apply, hF₀, hG₀, id_eq])
  have hFG : (F ∘ G : D.space → D.space) = id :=
    D.covering.eq_of_comp_eq (F.continuous.comp G.continuous) continuous_id
      (by funext d; exact (congrFun hFq (G d)).trans (congrFun hGq d))
      d₀ (by simp only [Function.comp_apply, hG₀, hF₀, id_eq])
  let e : C.space ≃ₜ D.space :=
    { toFun := F
      invFun := G
      left_inv := fun c => congrFun hGF c
      right_inv := fun d => congrFun hFG d
      continuous_toFun := F.continuous
      continuous_invFun := G.continuous }
  refine ⟨e, ⟨hF₀, hFq, hFa.mpr C.analytic_projection,
    hGa.mpr D.analytic_projection⟩, ?_⟩
  intro e' he'
  have heF : (e' : C.space → D.space) = F :=
    D.covering.eq_of_comp_eq e'.continuous F.continuous (he'.2.1.trans hFq.symm)
      c₀ (he'.1.trans hF₀.symm)
  exact Homeomorph.ext (fun c => congrFun heF c)

end LowDimensionalTopology.Geometry.Surfaces
