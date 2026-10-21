module
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Inverse
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Tactic

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.Conformal
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Conformal
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
@[expose] public section
noncomputable section
open scoped Topology
namespace LowDimensionalTopology.Geometry.Surfaces

universe u v

/-- A complex atlas is an open cover by genuine complex coordinate charts with analytic overlap maps. -/
structure RiemannAtlas (X : Type u) [TopologicalSpace X] where
  charts : Set (OpenPartialHomeomorph X ℂ)
  cover : ∀ x : X, ∃ e ∈ charts, x ∈ e.source
  compatible : ∀ e ∈ charts, ∀ f ∈ charts,
    AnalyticOnNhd ℂ (e.symm.trans f) (e.symm.trans f).source

/-- A Hausdorff connected space equipped with an analytic complex atlas. -/
structure RiemannSurface (X : Type u) [TopologicalSpace X] extends RiemannAtlas X where
  t2Space : T2Space X
  connectedSpace : ConnectedSpace X

/-- The geometric arbitrary covering atlas gives Mathlib's charted-space structure without imposing countability. -/
@[instance_reducible] def RiemannAtlas.toChartedSpace {X : Type u} [TopologicalSpace X] (A : RiemannAtlas X) :
    ChartedSpace ℂ X where
  atlas := A.charts
  chartAt x := (A.cover x).choose
  mem_chart_source x := (A.cover x).choose_spec.2
  chart_mem_atlas x := (A.cover x).choose_spec.1

/-- Both chart domains and coordinate ranges are genuinely open in the original topologies. -/
theorem RiemannAtlas.chart_open {X : Type u} [TopologicalSpace X] (A : RiemannAtlas X)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ A.charts) :
    IsOpen e.source ∧ IsOpen e.target := ⟨e.open_source, e.open_target⟩

/-- Coordinate compatibility is pointwise analyticity on the actual overlap domain. -/
theorem RiemannAtlas.transition_analyticAt {X : Type u} [TopologicalSpace X]
    (A : RiemannAtlas X) (e f : OpenPartialHomeomorph X ℂ)
    (he : e ∈ A.charts) (hf : f ∈ A.charts) (z : ℂ)
    (hz : z ∈ (e.symm.trans f).source) : AnalyticAt ℂ (e.symm.trans f) z :=
  A.compatible e he f hf z hz

/-- The actual coordinate domain on which a map is represented using two selected charts. -/
def riemannChartMapDomain {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X ℂ) (f : X → Y) (g : OpenPartialHomeomorph Y ℂ) : Set ℂ :=
  e.target ∩ e.symm ⁻¹' (f ⁻¹' g.source)

/-- The genuine local expression of a map between surfaces. -/
def riemannChartMap {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X ℂ) (f : X → Y) (g : OpenPartialHomeomorph Y ℂ) : ℂ → ℂ :=
  g ∘ f ∘ e.symm

/-- The continuity required by the source makes each local coordinate domain open. -/
theorem riemannChartMapDomain_isOpen {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X ℂ) (f : X → Y) (g : OpenPartialHomeomorph Y ℂ)
    (hf : Continuous f) : IsOpen (riemannChartMapDomain e f g) :=
  e.symm.continuousOn.isOpen_inter_preimage e.open_target (g.open_source.preimage hf)

/-- A continuous map is analytic when every actual local chart expression is complex analytic. -/
def RiemannAnalyticMap {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (A : RiemannAtlas X) (B : RiemannAtlas Y) (f : X → Y) : Prop :=
  Continuous f ∧ ∀ e ∈ A.charts, ∀ g ∈ B.charts,
    AnalyticOnNhd ℂ (riemannChartMap e f g) (riemannChartMapDomain e f g)

/-- Analytic surface maps are continuous in their original topologies. -/
theorem RiemannAnalyticMap.continuous {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {A : RiemannAtlas X} {B : RiemannAtlas Y}
    {f : X → Y} (hf : RiemannAnalyticMap A B f) : Continuous f := hf.1

/-- Checking a map using full atlases also checks any chosen subfamilies of those atlases. -/
theorem RiemannAnalyticMap.restrict_charts {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {A : RiemannAtlas X} {B : RiemannAtlas Y}
    {f : X → Y} (hf : RiemannAnalyticMap A B f)
    (S : Set (OpenPartialHomeomorph X ℂ)) (T : Set (OpenPartialHomeomorph Y ℂ))
    (hS : S ⊆ A.charts) (hT : T ⊆ B.charts) :
    ∀ e ∈ S, ∀ g ∈ T, AnalyticOnNhd ℂ (riemannChartMap e f g) (riemannChartMapDomain e f g) := by
  intro e he g hg
  exact hf.2 e (hS he) g (hT hg)

/-- conformal equivalence is existence of an analytic bijection. -/
def RiemannConformallyEquivalent {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : RiemannSurface X) (B : RiemannSurface Y) : Prop :=
  ∃ f : X → Y, RiemannAnalyticMap A.toRiemannAtlas B.toRiemannAtlas f ∧ Function.Bijective f

open scoped OnePoint
open Set Filter
/-- Reciprocal on the actual one-point compactification, interchanging zero and infinity. -/
def sphereReciprocal : OnePoint ℂ → OnePoint ℂ :=
  OnePoint.rec ((0 : ℂ) : OnePoint ℂ) (fun z => if z = 0 then ∞ else ((z⁻¹ : ℂ) : OnePoint ℂ))

@[simp] theorem sphereReciprocal_infty : sphereReciprocal ∞ = ((0 : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem sphereReciprocal_zero : sphereReciprocal ((0 : ℂ) : OnePoint ℂ) = ∞ := by
  simp only [sphereReciprocal, OnePoint.rec, ite_true]

/-- At every nonzero finite point, the reciprocal is the usual complex inverse. -/
theorem sphereReciprocal_coe (z : ℂ) (hz : z ≠ 0) :
    sphereReciprocal (z : OnePoint ℂ) = ((z⁻¹ : ℂ) : OnePoint ℂ) := by
  simp only [sphereReciprocal, OnePoint.rec, ite_eq_right hz]

/-- Reciprocal is an involution on the true sphere, including both exceptional points. -/
theorem sphereReciprocal_involutive : Function.Involutive sphereReciprocal := by
  intro z
  induction z using OnePoint.rec with
  | infty => exact sphereReciprocal_zero
  | coe z =>
      by_cases hz : z = 0
      · subst z
        rw [sphereReciprocal_zero, sphereReciprocal_infty]
      · rw [sphereReciprocal_coe z hz, sphereReciprocal_coe z⁻¹ (inv_ne_zero hz), inv_inv]

/-- Reciprocal is continuous in the compactification topology at zero and infinity as well. -/
theorem continuous_sphereReciprocal : Continuous sphereReciprocal := by
  rw [continuous_iff_continuousAt]
  intro z
  induction z using OnePoint.rec with
  | infty =>
      apply OnePoint.continuousAt_infty'.mpr
      rw [sphereReciprocal_infty]
      have ht : Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : OnePoint ℂ))
          (coclosedCompact ℂ) (𝓝 ((0 : ℂ) : OnePoint ℂ)) := by
        apply OnePoint.continuous_coe.continuousAt.tendsto.comp
        simpa [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
          using (Filter.tendsto_inv₀_cobounded : Tendsto (Inv.inv : ℂ → ℂ) _ _)
      apply ht.congr'
      have hn : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ≠ 0 := by
        simpa [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
          using (Bornology.eventually_ne_cobounded (0 : ℂ))
      filter_upwards [hn] with z hz
      exact (sphereReciprocal_coe z hz).symm
  | coe z =>
      apply OnePoint.continuousAt_coe.mpr
      by_cases hz : z = 0
      · subst z
        have ht : Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : OnePoint ℂ))
            (𝓝[≠] 0) (𝓝 (∞ : OnePoint ℂ)) := by
          apply OnePoint.tendsto_coe_infty.comp
          simpa [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
            using (Filter.tendsto_inv₀_nhdsNE_zero : Tendsto (Inv.inv : ℂ → ℂ) _ _)
        have hw : ContinuousWithinAt (fun z : ℂ => sphereReciprocal z) ({0}ᶜ) 0 := by
          rw [ContinuousWithinAt, sphereReciprocal_zero]
          apply ht.congr'
          filter_upwards [self_mem_nhdsWithin] with z hz
          exact (sphereReciprocal_coe z hz).symm
        have hu := hw.insert
        simpa [Function.comp_def] using hu
      · have ht : ContinuousAt (fun z : ℂ => ((z⁻¹ : ℂ) : OnePoint ℂ)) z :=
          OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)
        apply ht.congr
        filter_upwards [eventually_ne_nhds hz] with w hw
        exact (sphereReciprocal_coe w hw).symm

/-- The reciprocal extends across zero and infinity to a homeomorphism of the Riemann sphere. -/
def sphereReciprocalHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ where
  toFun := sphereReciprocal
  invFun := sphereReciprocal
  left_inv := sphereReciprocal_involutive
  right_inv := sphereReciprocal_involutive
  continuous_toFun := continuous_sphereReciprocal
  continuous_invFun := continuous_sphereReciprocal

/-- The actual finite-coordinate chart, inverse to the standard open embedding of the complex plane. -/
def sphereFiniteChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : ℂ → OnePoint ℂ)).symm

/-- The finite-coordinate chart reads every finite point as its original complex coordinate. -/
theorem sphereFiniteChart_coe (z : ℂ) : sphereFiniteChart (z : OnePoint ℂ) = z :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv

/-- The inverse finite-coordinate chart is the actual finite-point inclusion. -/
theorem sphereFiniteChart_symm (z : ℂ) : sphereFiniteChart.symm z = (z : OnePoint ℂ) := rfl

/-- The finite chart's source is exactly the complement of infinity. -/
theorem sphereFiniteChart_source : sphereFiniteChart.source = {∞}ᶜ := by
  change (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : ℂ → OnePoint ℂ)).target = _
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  exact OnePoint.compl_infty.symm

/-- The finite chart maps onto the full complex plane. -/
theorem sphereFiniteChart_target : sphereFiniteChart.target = univ := rfl

/-- The infinity-coordinate chart is reciprocal followed by the actual finite-coordinate chart. -/
def sphereInfinityChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  sphereReciprocalHomeomorph.toOpenPartialHomeomorph.trans sphereFiniteChart

/-- Infinity is a genuine coordinate-zero point in the second chart. -/
theorem sphereInfinityChart_infty : sphereInfinityChart ∞ = 0 := by
  change sphereFiniteChart (sphereReciprocal ∞) = 0
  rw [sphereReciprocal_infty, sphereFiniteChart_coe]

/-- The second chart agrees with the actual reciprocal at every nonzero finite point. -/
theorem sphereInfinityChart_coe (z : ℂ) (hz : z ≠ 0) : sphereInfinityChart (z : OnePoint ℂ) = z⁻¹ := by
  change sphereFiniteChart (sphereReciprocal (z : OnePoint ℂ)) = z⁻¹
  rw [sphereReciprocal_coe z hz, sphereFiniteChart_coe]

/-- The reciprocal has infinity as value exactly at the finite point zero. -/
theorem sphereReciprocal_eq_infty_iff (z : OnePoint ℂ) :
    sphereReciprocal z = ∞ ↔ z = ((0 : ℂ) : OnePoint ℂ) := by
  rw [← sphereReciprocal_zero]
  exact sphereReciprocal_involutive.injective.eq_iff

/-- The infinity chart has exactly the stated punctured-sphere source. -/
theorem sphereInfinityChart_source : sphereInfinityChart.source = {((0 : ℂ) : OnePoint ℂ)}ᶜ := by
  rw [sphereInfinityChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, sphereFiniteChart_source]
  ext z
  simp only [mem_inter_iff, mem_univ, true_and, mem_preimage, mem_compl_iff, mem_singleton_iff]
  change sphereReciprocal z ≠ ∞ ↔ z ≠ ((0 : ℂ) : OnePoint ℂ)
  exact not_congr (sphereReciprocal_eq_infty_iff z)

/-- Both sphere coordinate charts have full complex-plane target. -/
theorem sphereInfinityChart_target : sphereInfinityChart.target = univ := by
  simp only [sphereInfinityChart, OpenPartialHomeomorph.trans_target, sphereFiniteChart_target,
    Homeomorph.toOpenPartialHomeomorph_target, preimage_univ, inter_self]

/-- The inverse infinity chart sends zero to infinity and nonzero coordinates to their reciprocal. -/
theorem sphereInfinityChart_symm (z : ℂ) :
    sphereInfinityChart.symm z = sphereReciprocal (z : OnePoint ℂ) := rfl

/-- The two actual chart domains cover the compactified complex plane. -/
theorem sphereCharts_cover (z : OnePoint ℂ) : z ∈ sphereFiniteChart.source ∨ z ∈ sphereInfinityChart.source := by
  rw [sphereFiniteChart_source, sphereInfinityChart_source]
  by_cases hz : z = ∞
  · exact Or.inr (by simp only [hz, mem_compl_iff, mem_singleton_iff,
      OnePoint.infty_ne_coe, not_false_eq_true])
  · exact Or.inl hz

/-- The first overlap has exactly the punctured complex plane as its coordinate domain. -/
theorem sphereFiniteInfinity_transition_source :
    (sphereFiniteChart.symm.trans sphereInfinityChart).source = {z : ℂ | z ≠ 0} := by
  rw [OpenPartialHomeomorph.trans_source]
  ext z
  simp only [OpenPartialHomeomorph.symm_source, sphereFiniteChart_target, mem_inter_iff,
    mem_univ, true_and, mem_preimage, sphereFiniteChart_symm, sphereInfinityChart_source,
    mem_compl_iff, mem_singleton_iff, OnePoint.coe_eq_coe, mem_ofPred_eq]

/-- The reverse overlap has the same punctured complex-plane coordinate domain. -/
theorem sphereInfinityFinite_transition_source :
    (sphereInfinityChart.symm.trans sphereFiniteChart).source = {z : ℂ | z ≠ 0} := by
  rw [OpenPartialHomeomorph.trans_source]
  ext z
  simp only [OpenPartialHomeomorph.symm_source, sphereInfinityChart_target, mem_inter_iff,
    mem_univ, true_and, mem_preimage, sphereInfinityChart_symm, sphereFiniteChart_source,
    mem_compl_iff, mem_singleton_iff, sphereReciprocal_eq_infty_iff, OnePoint.coe_eq_coe, mem_ofPred_eq]

/-- On their true overlap, the first change of complex coordinates is reciprocal. -/
theorem sphereFiniteInfinity_transition (z : ℂ) (hz : z ≠ 0) :
    (sphereFiniteChart.symm.trans sphereInfinityChart) z = z⁻¹ := by
  change sphereInfinityChart (sphereFiniteChart.symm z) = z⁻¹
  rw [sphereFiniteChart_symm, sphereInfinityChart_coe z hz]

/-- The reverse change of complex coordinates is also reciprocal. -/
theorem sphereInfinityFinite_transition (z : ℂ) (hz : z ≠ 0) :
    (sphereInfinityChart.symm.trans sphereFiniteChart) z = z⁻¹ := by
  change sphereFiniteChart (sphereInfinityChart.symm z) = z⁻¹
  rw [sphereInfinityChart_symm, sphereReciprocal_coe z hz, sphereFiniteChart_coe]

/-- The first overlap map is analytic on a neighbourhood of every point of its actual domain. -/
theorem sphereFiniteInfinity_transition_analytic :
    AnalyticOnNhd ℂ (sphereFiniteChart.symm.trans sphereInfinityChart)
      (sphereFiniteChart.symm.trans sphereInfinityChart).source := by
  rw [sphereFiniteInfinity_transition_source]
  apply AnalyticOnNhd.congr isOpen_ne (analyticOnNhd_inv (𝕜 := ℂ))
  intro z hz
  exact (sphereFiniteInfinity_transition z hz).symm

/-- The reverse overlap map is analytic on a neighbourhood of every point of its actual domain. -/
theorem sphereInfinityFinite_transition_analytic :
    AnalyticOnNhd ℂ (sphereInfinityChart.symm.trans sphereFiniteChart)
      (sphereInfinityChart.symm.trans sphereFiniteChart).source := by
  rw [sphereInfinityFinite_transition_source]
  apply AnalyticOnNhd.congr isOpen_ne (analyticOnNhd_inv (𝕜 := ℂ))
  intro z hz
  exact (sphereInfinityFinite_transition z hz).symm

/-- A chart's self-transition is analytic on its genuine open domain, independently of its arbitrary off-domain values. -/
theorem openPartialHomeomorph_self_transition_analytic {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) : AnalyticOnNhd ℂ (e.symm.trans e) (e.symm.trans e).source := by
  apply AnalyticOnNhd.congr (e.symm.trans e).open_source analyticOnNhd_id
  intro z hz
  change z = e (e.symm z)
  rw [OpenPartialHomeomorph.trans_source] at hz
  exact (e.right_inv hz.1).symm

/-- The two charts stated in Riemann-sphere example. -/
def sphereCharts : Set (OpenPartialHomeomorph (OnePoint ℂ) ℂ) :=
  {sphereFiniteChart, sphereInfinityChart}

/-- The stated two-chart atlas is an actual open cover. -/
theorem sphereCharts_covering (z : OnePoint ℂ) : ∃ e ∈ sphereCharts, z ∈ e.source := by
  rcases sphereCharts_cover z with h | h
  · exact ⟨sphereFiniteChart, Set.mem_insert _ _, h⟩
  · exact ⟨sphereInfinityChart, Set.mem_insert_of_mem _ (Set.mem_singleton _), h⟩

/-- Every one of the four true chart transitions is complex analytic on its actual open overlap. -/
theorem sphereCharts_compatible (e : OpenPartialHomeomorph (OnePoint ℂ) ℂ) (he : e ∈ sphereCharts)
    (f : OpenPartialHomeomorph (OnePoint ℂ) ℂ) (hf : f ∈ sphereCharts) :
    AnalyticOnNhd ℂ (e.symm.trans f) (e.symm.trans f).source := by
  simp only [sphereCharts, Set.mem_insert_iff, Set.mem_singleton_iff] at he hf
  rcases he with rfl | rfl
  · rcases hf with rfl | rfl
    · exact openPartialHomeomorph_self_transition_analytic _
    · exact sphereFiniteInfinity_transition_analytic
  · rcases hf with rfl | rfl
    · exact sphereInfinityFinite_transition_analytic
    · exact openPartialHomeomorph_self_transition_analytic _

/-- The actual two-chart analytic atlas on the one-point compactification of the complex plane. -/
def sphereRiemannAtlas : RiemannAtlas (OnePoint ℂ) where
  charts := sphereCharts
  cover := sphereCharts_covering
  compatible := sphereCharts_compatible

/-- The topological Riemann sphere has the geometric genuine two-chart complex surface structure. -/
def sphereRiemannSurface : RiemannSurface (OnePoint ℂ) where
  toRiemannAtlas := sphereRiemannAtlas
  t2Space := inferInstance
  connectedSpace := inferInstance



/-- A source point represented in two charts lies in the exact coordinate domain. -/
theorem riemannChartMapDomain_mem {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X ℂ) (f : X → Y) (g : OpenPartialHomeomorph Y ℂ)
    (x : X) (hx : x ∈ e.source) (hg : f x ∈ g.source) :
    e x ∈ riemannChartMapDomain e f g := by
  exact ⟨e.map_source hx, by simpa only [Set.mem_preimage, e.left_inv hx] using hg⟩

/-- The identity is analytic in all of a complex atlas's actual charts. -/
theorem RiemannAnalyticMap.id {X : Type u} [TopologicalSpace X] (A : RiemannAtlas X) :
    RiemannAnalyticMap A A (id : X → X) := by
  refine ⟨continuous_id, ?_⟩
  intro e he g hg
  exact A.compatible e he g hg

/-- Any Riemann surface is conformally equivalent to itself. -/
theorem RiemannConformallyEquivalent.refl {X : Type u} [TopologicalSpace X]
    (A : RiemannSurface X) : RiemannConformallyEquivalent A A :=
  ⟨id, _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.id _, Function.bijective_id⟩

/-- Analyticity in a selected source and target chart implies analyticity in every other overlapping chart. -/
theorem riemann_chart_analyticAt_change {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : RiemannAtlas X) (B : RiemannAtlas Y) (f : X → Y) (hf : Continuous f)
    (e e₀ : OpenPartialHomeomorph X ℂ) (g g₀ : OpenPartialHomeomorph Y ℂ)
    (he : e ∈ A.charts) (he₀ : e₀ ∈ A.charts) (hg : g ∈ B.charts) (hg₀ : g₀ ∈ B.charts)
    (x : X) (hx : x ∈ e.source) (hx₀ : x ∈ e₀.source)
    (hy : f x ∈ g.source) (hy₀ : f x ∈ g₀.source)
    (ha : AnalyticAt ℂ (riemannChartMap e₀ f g₀) (e₀ x)) :
    AnalyticAt ℂ (riemannChartMap e f g) (e x) := by
  let L := e.symm.trans e₀
  let R := g₀.symm.trans g
  have hLx : L (e x) = e₀ x := by
    change e₀ (e.symm (e x)) = e₀ x
    rw [e.left_inv hx]
  have hRx : R (g₀ (f x)) = g (f x) := by
    change g (g₀.symm (g₀ (f x))) = g (f x)
    rw [g₀.left_inv hy₀]
  have hL : AnalyticAt ℂ L (e x) := by
    apply A.transition_analyticAt e e₀ he he₀
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ e₀.source
    rwa [e.left_inv hx]
  have hR : AnalyticAt ℂ R (g₀ (f x)) := by
    apply B.transition_analyticAt g₀ g hg₀ hg
    refine ⟨g₀.map_source hy₀, ?_⟩
    change g₀.symm (g₀ (f x)) ∈ g.source
    rwa [g₀.left_inv hy₀]
  have hmiddle : riemannChartMap e₀ f g₀ (L (e x)) = g₀ (f x) := by
    rw [hLx]
    change g₀ (f (e₀.symm (e₀ x))) = g₀ (f x)
    rw [e₀.left_inv hx₀]
  have hc : AnalyticAt ℂ (R ∘ riemannChartMap e₀ f g₀ ∘ L) (e x) := by
    apply AnalyticAt.comp
    · simp only [Function.comp_apply]
      rwa [hmiddle]
    · apply AnalyticAt.comp
      · rwa [hLx]
      · exact hL
  apply hc.congr
  have hleft : ∀ᶠ z in 𝓝 (e x), e.symm z ∈ e₀.source := by
    have h : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      simpa only [ContinuousAt, e.left_inv hx] using e.continuousAt_symm (e.map_source hx)
    exact h.eventually (e₀.open_source.mem_nhds hx₀)
  have hright : ∀ᶠ z in 𝓝 (e x), f (e.symm z) ∈ g₀.source := by
    have h : Tendsto (f ∘ e.symm) (𝓝 (e x)) (𝓝 (f x)) := by
      simpa only [ContinuousAt, Function.comp_apply, e.left_inv hx] using hf.continuousAt.comp (e.continuousAt_symm
        (e.map_source hx))
    exact h.eventually (g₀.open_source.mem_nhds hy₀)
  filter_upwards [hleft, hright] with z hz₀ hgz₀
  change g (g₀.symm (g₀ (f (e₀.symm (e₀ (e.symm z)))))) = g (f (e.symm z))
  rw [e₀.left_inv hz₀, g₀.left_inv hgz₀]

/-- Any subfamily which still covers the original space is itself a compatible complex atlas. -/
def RiemannAtlas.subatlas {X : Type u} [TopologicalSpace X] (A : RiemannAtlas X)
    (S : Set (OpenPartialHomeomorph X ℂ)) (hS : S ⊆ A.charts)
    (hcover : ∀ x : X, ∃ e ∈ S, x ∈ e.source) : RiemannAtlas X where
  charts := S
  cover := hcover
  compatible e he g hg := A.compatible e (hS he) g (hS hg)

/-- checking actual covering subatlases is equivalent to checking all chart pairs. -/
theorem riemannAnalyticMap_subatlas_iff {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : RiemannAtlas X) (B : RiemannAtlas Y) (f : X → Y)
    (S : Set (OpenPartialHomeomorph X ℂ)) (T : Set (OpenPartialHomeomorph Y ℂ))
    (hS : S ⊆ A.charts) (hT : T ⊆ B.charts)
    (hcoverS : ∀ x : X, ∃ e ∈ S, x ∈ e.source)
    (hcoverT : ∀ y : Y, ∃ g ∈ T, y ∈ g.source) :
    RiemannAnalyticMap (A.subatlas S hS hcoverS) (B.subatlas T hT hcoverT) f ↔
      RiemannAnalyticMap A B f := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    intro e he g hg z hz
    let x := e.symm z
    have hx : x ∈ e.source := e.map_target hz.1
    have hy : f x ∈ g.source := hz.2
    obtain ⟨e₀, he₀, hx₀⟩ := hcoverS x
    obtain ⟨g₀, hg₀, hy₀⟩ := hcoverT (f x)
    have hm : AnalyticAt ℂ (riemannChartMap e₀ f g₀) (e₀ x) :=
      hf.2 e₀ he₀ g₀ hg₀ (e₀ x) (riemannChartMapDomain_mem e₀ f g₀ x hx₀ hy₀)
    have ha := riemann_chart_analyticAt_change A B f hf.1 e e₀ g g₀
      he (hS he₀) hg (hT hg₀) x hx hx₀ hy hy₀ hm
    simpa only [x, e.right_inv hz.1] using ha
  · intro hf
    exact ⟨hf.1, hf.restrict_charts S T hS hT⟩


universe w

/-- Analytic maps between the actual complex atlases compose. -/
theorem RiemannAnalyticMap.comp {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} {C : RiemannAtlas Z}
    {f : X → Y} {g : Y → Z} (hg : RiemannAnalyticMap B C g) (hf : RiemannAnalyticMap A B f) :
    RiemannAnalyticMap A C (g ∘ f) := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro e he h hh z hz
  let x := e.symm z
  have hx : x ∈ e.source := e.map_target hz.1
  have hgh : g (f x) ∈ h.source := hz.2
  obtain ⟨k, hk, hy⟩ := B.cover (f x)
  have hfcoord : AnalyticAt ℂ (riemannChartMap e f k) z :=
    hf.2 e he k hk z ⟨hz.1, hy⟩
  have hgcoord : AnalyticAt ℂ (riemannChartMap k g h) (k (f x)) :=
    hg.2 k hk h hh (k (f x)) (riemannChartMapDomain_mem k g h (f x) hy hgh)
  have hcomp : AnalyticAt ℂ (riemannChartMap k g h ∘ riemannChartMap e f k) z :=
    AnalyticAt.comp (f := riemannChartMap e f k) (x := z) hgcoord hfcoord
  apply hcomp.congr
  have hev : ∀ᶠ t in 𝓝 z, f (e.symm t) ∈ k.source := by
    have ht : Tendsto (f ∘ e.symm) (𝓝 z) (𝓝 (f x)) :=
      hf.1.continuousAt.comp (e.continuousAt_symm hz.1)
    exact ht.eventually (k.open_source.mem_nhds hy)
  filter_upwards [hev] with t ht
  change h (g (k.symm (k (f (e.symm t))))) = h (g (f (e.symm t)))
  rw [k.left_inv ht]

/-- Analytic bijections compose, so conformal equivalence is transitive. -/
theorem RiemannConformallyEquivalent.trans {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {A : RiemannSurface X} {B : RiemannSurface Y} {C : RiemannSurface Z}
    (hAB : RiemannConformallyEquivalent A B) (hBC : RiemannConformallyEquivalent B C) :
    RiemannConformallyEquivalent A C := by
  obtain ⟨f, hf, hfb⟩ := hAB
  obtain ⟨g, hg, hgb⟩ := hBC
  exact ⟨g ∘ f, hg.comp hf, hgb.comp hfb⟩

/-- Analyticity can be checked in one source and target chart around each actual point. -/
theorem riemannAnalyticMap_iff_locally {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : RiemannAtlas X) (B : RiemannAtlas Y) (f : X → Y) :
    RiemannAnalyticMap A B f ↔ Continuous f ∧
      ∀ x : X, ∃ e ∈ A.charts, x ∈ e.source ∧ ∃ g ∈ B.charts, f x ∈ g.source ∧
        AnalyticAt ℂ (riemannChartMap e f g) (e x) := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    intro x
    obtain ⟨e, he, hx⟩ := A.cover x
    obtain ⟨g, hg, hy⟩ := B.cover (f x)
    exact ⟨e, he, hx, g, hg, hy, hf.2 e he g hg (e x) (riemannChartMapDomain_mem e f g x hx hy)⟩
  · rintro ⟨hf, hlocal⟩
    refine ⟨hf, ?_⟩
    intro e he g hg z hz
    let x := e.symm z
    have hx : x ∈ e.source := e.map_target hz.1
    obtain ⟨e₀, he₀, hx₀, g₀, hg₀, hy₀, ha⟩ := hlocal x
    have hh := riemann_chart_analyticAt_change A B f hf e e₀ g g₀ he he₀ hg hg₀
      x hx hx₀ hz.2 hy₀ ha
    simpa only [x, e.right_inv hz.1] using hh



/-- A true complex chart change with analytic inverse has a nonzero complex derivative at every source point. -/
theorem openPartialHomeomorph_analytic_deriv_ne_zero (F : OpenPartialHomeomorph ℂ ℂ)
    (hF : AnalyticOnNhd ℂ F F.source) (hG : AnalyticOnNhd ℂ F.symm F.symm.source)
    (z : ℂ) (hz : z ∈ F.source) : deriv F z ≠ 0 := by
  have hforward := (hF z hz).differentiableAt.hasDerivAt
  have hbackward := (hG (F z) (F.map_source hz)).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun w : ℂ => w) (deriv F.symm (F z) * deriv F z) z := by
    apply (hbackward.comp z hforward).congr_of_eventuallyEq
    filter_upwards [F.open_source.mem_nhds hz] with w hw
    exact (F.left_inv hw).symm
  have hmul : deriv F.symm (F z) * deriv F z = 1 := hcomp.unique (hasDerivAt_id z)
  intro hzero
  rw [hzero, mul_zero] at hmul
  exact zero_ne_one hmul

/-- Every true analytic atlas transition has nonvanishing complex derivative on its actual overlap. -/
theorem RiemannAtlas.transition_deriv_ne_zero {X : Type*} [TopologicalSpace X]
    (A : RiemannAtlas X) (e f : OpenPartialHomeomorph X ℂ) (he : e ∈ A.charts) (hf : f ∈ A.charts)
    (z : ℂ) (hz : z ∈ (e.symm.trans f).source) : deriv (e.symm.trans f) z ≠ 0 := by
  apply openPartialHomeomorph_analytic_deriv_ne_zero (e.symm.trans f) (A.compatible e he f hf) _ z hz
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm] using A.compatible f hf e he

/-- Analytic atlas transitions are actual conformal maps in the fixed complex Euclidean metric. -/
theorem RiemannAtlas.transition_conformalAt {X : Type*} [TopologicalSpace X]
    (A : RiemannAtlas X) (e f : OpenPartialHomeomorph X ℂ) (he : e ∈ A.charts) (hf : f ∈ A.charts)
    (z : ℂ) (hz : z ∈ (e.symm.trans f).source) : ConformalAt (e.symm.trans f) z :=
  _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.complexDifferentiable_conformalAt (A.compatible e he f hf z
    hz).differentiableAt
    (A.transition_deriv_ne_zero e f he hf z hz)

/-- The actual derivative of a continuous surface curve transforms by the complex derivative of the chart transition. -/
theorem RiemannAtlas.curve_change_chart_hasDerivAt {X : Type*} [TopologicalSpace X]
    (A : RiemannAtlas X) (e f : OpenPartialHomeomorph X ℂ) (he : e ∈ A.charts) (hf : f ∈ A.charts)
    (x : X) (hxe : x ∈ e.source) (hxf : x ∈ f.source)
    (γ : ℝ → X) (t : ℝ) (hγ : ContinuousAt γ t) (hγx : γ t = x)
    (v : ℂ) (hv : HasDerivAt (fun s : ℝ => e (γ s)) v t) :
    HasDerivAt (fun s : ℝ => f (γ s)) (deriv (e.symm.trans f) (e x) * v) t := by
  let F := e.symm.trans f
  have hz : e x ∈ F.source := by
    refine ⟨e.map_source hxe, ?_⟩
    change e.symm (e x) ∈ f.source
    rwa [e.left_inv hxe]
  have hd := (A.compatible e he f hf (e x) hz).differentiableAt
  have hreal : HasFDerivAt F ((fderiv ℂ F (e x)).restrictScalars ℝ) (e (γ t)) := by
    rw [hγx]
    exact hd.hasFDerivAt.restrictScalars ℝ
  have hcomp := hreal.comp_hasDerivAt t hv
  have hactual : HasDerivAt (fun s : ℝ => f (γ s))
      (((fderiv ℂ F (e x)).restrictScalars ℝ) v) t := by
    apply hcomp.congr_of_eventuallyEq
    have hnear : ∀ᶠ s in 𝓝 t, γ s ∈ e.source := by
      apply hγ.eventually
      simpa only [hγx] using e.open_source.eventually_mem hxe
    filter_upwards [hnear] with s hs
    change f (γ s) = f (e.symm (e (γ s)))
    rw [e.left_inv hs]
  simpa only [ContinuousLinearMap.coe_restrictScalars', fderiv_eq_deriv_mul] using hactual

/-- The actual angle between two surface curves, measured using the ordinary Euclidean angle of chart-coordinate derivatives. -/
def riemannCurveAngle {X : Type*} [TopologicalSpace X] (e : OpenPartialHomeomorph X ℂ)
    (γ σ : ℝ → X) (t : ℝ) : ℝ :=
  InnerProductGeometry.angle (deriv (fun s : ℝ => e (γ s)) t) (deriv (fun s : ℝ => e (σ s)) t)

/-- changing overlapping analytic charts preserves regular curve tangents and the actual angle between crossing curves. -/
theorem RiemannAtlas.curve_angle_independent {X : Type*} [TopologicalSpace X]
    (A : RiemannAtlas X) (e f : OpenPartialHomeomorph X ℂ) (he : e ∈ A.charts) (hf : f ∈ A.charts)
    (x : X) (hxe : x ∈ e.source) (hxf : x ∈ f.source)
    (γ σ : ℝ → X) (t : ℝ) (hγ : ContinuousAt γ t) (hσ : ContinuousAt σ t)
    (hγx : γ t = x) (hσx : σ t = x)
    (v w : ℂ) (hv : HasDerivAt (fun s : ℝ => e (γ s)) v t)
    (hw : HasDerivAt (fun s : ℝ => e (σ s)) w t) (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    DifferentiableAt ℝ (fun s : ℝ => f (γ s)) t ∧
    DifferentiableAt ℝ (fun s : ℝ => f (σ s)) t ∧
    deriv (fun s : ℝ => f (γ s)) t ≠ 0 ∧ deriv (fun s : ℝ => f (σ s)) t ≠ 0 ∧
    riemannCurveAngle f γ σ t = riemannCurveAngle e γ σ t := by
  have hγf := A.curve_change_chart_hasDerivAt e f he hf x hxe hxf γ t hγ hγx v hv
  have hσf := A.curve_change_chart_hasDerivAt e f he hf x hxe hxf σ t hσ hσx w hw
  have hz : e x ∈ (e.symm.trans f).source := by
    refine ⟨e.map_source hxe, ?_⟩
    change e.symm (e x) ∈ f.source
    rwa [e.left_inv hxe]
  have hD := A.transition_deriv_ne_zero e f he hf (e x) hz
  refine ⟨hγf.differentiableAt, hσf.differentiableAt, ?_, ?_, ?_⟩
  · rw [hγf.deriv]
    exact mul_ne_zero hD hv0
  · rw [hσf.deriv]
    exact mul_ne_zero hD hw0
  · unfold riemannCurveAngle
    rw [hγf.deriv, hσf.deriv, hv.deriv, hw.deriv]
    have hd := (A.compatible e he f hf (e x) hz).differentiableAt
    have hp := InnerProductGeometry.ConformalAt.preserves_angle (hd.hasFDerivAt.restrictScalars ℝ)
      (A.transition_conformalAt e f he hf (e x) hz) v w
    simpa only [ContinuousLinearMap.coe_restrictScalars', fderiv_eq_deriv_mul] using hp

/-- The intrinsic curve angle at a surface point, initially measured in one chart supplied by the covering atlas. -/
def riemannIntrinsicCurveAngle {X : Type*} [TopologicalSpace X] (A : RiemannAtlas X)
    (x : X) (γ σ : ℝ → X) (t : ℝ) : ℝ :=
  riemannCurveAngle (A.cover x).choose γ σ t

/-- The intrinsic angle equals the genuine coordinate-derivative angle in every chart containing the crossing point. -/
theorem RiemannAtlas.intrinsicCurveAngle_eq {X : Type*} [TopologicalSpace X]
    (A : RiemannAtlas X) (e : OpenPartialHomeomorph X ℂ) (he : e ∈ A.charts)
    (x : X) (hxe : x ∈ e.source) (γ σ : ℝ → X) (t : ℝ)
    (hγ : ContinuousAt γ t) (hσ : ContinuousAt σ t) (hγx : γ t = x) (hσx : σ t = x)
    (v w : ℂ) (hv : HasDerivAt (fun s : ℝ => e (γ s)) v t)
    (hw : HasDerivAt (fun s : ℝ => e (σ s)) w t) (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    riemannIntrinsicCurveAngle A x γ σ t = riemannCurveAngle e γ σ t := by
  exact (A.curve_angle_independent e (A.cover x).choose he (A.cover x).choose_spec.1
    x hxe (A.cover x).choose_spec.2 γ σ t hγ hσ hγx hσx v w hv hw hv0 hw0).2.2.2.2




/-- A locally injective holomorphic map takes each neighbourhood to a neighbourhood. -/
theorem complex_analytic_nhds_le_of_injOn (p : ℂ → ℂ) (z : ℂ)
    (hp : AnalyticAt ℂ p z) (S : Set ℂ) (hS : S ∈ 𝓝 z) (hinj : Set.InjOn p S) :
    𝓝 (p z) ≤ Filter.map p (𝓝 z) := by
  rcases hp.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
  · have hzS : z ∈ S := mem_of_mem_nhds hS
    have hsingleton : ({z} : Set ℂ) ∈ 𝓝 z := by
      filter_upwards [hconst, hS] with w hw hwS
      exact hinj hwS hzS hw
    have hopen : IsOpen ({z} : Set ℂ) := by
      rw [isOpen_iff_mem_nhds]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      simpa only [hw] using hsingleton
    exact False.elim ((not_isOpen_singleton z) hopen)
  · exact hopen

/-- An injective analytic surface map is open in the actual underlying topologies. -/
theorem RiemannAnalyticMap.isOpenMap_of_injective {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {A : RiemannAtlas X} {B : RiemannAtlas Y}
    {f : X → Y} (hf : RiemannAnalyticMap A B f) (hinj : Function.Injective f) : IsOpenMap f := by
  rw [isOpenMap_iff_nhds_le]
  intro x
  obtain ⟨e, he, hx⟩ := A.cover x
  obtain ⟨g, hg, hy⟩ := B.cover (f x)
  let D := riemannChartMapDomain e f g
  let p := riemannChartMap e f g
  have hex : e x ∈ D := ⟨e.map_source hx, by
    change f (e.symm (e x)) ∈ g.source
    rwa [e.left_inv hx]⟩
  have hD : D ∈ 𝓝 (e x) := (riemannChartMapDomain_isOpen e f g hf.1).mem_nhds hex
  have hp : AnalyticAt ℂ p (e x) := hf.2 e he g hg (e x) hex
  have hpinj : Set.InjOn p D := by
    intro z hz w hw heq
    apply e.symm.injOn hz.1 hw.1
    apply hinj
    apply g.injOn hz.2 hw.2
    exact heq
  have hopen := complex_analytic_nhds_le_of_injOn p (e x) hp D hD hpinj
  have hpex : p (e x) = g (f x) := by
    change g (f (e.symm (e x))) = g (f x)
    rw [e.left_inv hx]
  rw [hpex] at hopen
  have hmap : Filter.map g.symm (𝓝 (g (f x))) ≤
      Filter.map g.symm (Filter.map p (𝓝 (e x))) := Filter.map_mono hopen
  rw [g.symm_map_nhds_eq hy, Filter.map_map] at hmap
  have hev : (g.symm ∘ p) =ᶠ[𝓝 (e x)] (f ∘ e.symm) := by
    have ht : Tendsto (f ∘ e.symm) (𝓝 (e x)) (𝓝 (f x)) :=
      (show Tendsto f (𝓝 x) (𝓝 (f x)) from hf.1.continuousAt).comp (e.tendsto_symm hx)
    have hsource : ∀ᶠ z in 𝓝 (e x), f (e.symm z) ∈ g.source :=
      ht.eventually (g.open_source.mem_nhds hy)
    filter_upwards [hsource] with z hz
    exact g.left_inv hz
  rw [Filter.map_congr hev, ← Filter.map_map, e.symm_map_nhds_eq hx] at hmap
  exact hmap

/-- An analytic bijection is a genuine homeomorphism before proving inverse analyticity. -/
def RiemannAnalyticMap.toHomeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {A : RiemannAtlas X} {B : RiemannAtlas Y}
    {f : X → Y} (hf : RiemannAnalyticMap A B f) (hbij : Function.Bijective f) : X ≃ₜ Y :=
  (Equiv.ofBijective f hbij).toHomeomorphOfContinuousOpen hf.1 (hf.isOpenMap_of_injective hbij.1)



/-- Critical points of an actual injective analytic chart map are isolated; no nonzero-derivative hypothesis is imposed. -/
theorem openPartialHomeomorph_analytic_deriv_punctured_ne_zero (F : OpenPartialHomeomorph ℂ ℂ)
    (hF : AnalyticOnNhd ℂ F F.source) (x : ℂ) (hx : x ∈ F.source) :
    ∀ᶠ z in 𝓝[≠] x, deriv F z ≠ 0 := by
  rcases (hF x hx).deriv.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (F.open_source.mem_nhds hx) hzero)
    let u : ℂ := x + ((r / 2 : ℝ) : ℂ)
    have hu : u ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm]
      dsimp [u]
      rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
      exact half_lt_self hr
    have hd : DifferentiableOn ℂ F (Metric.ball x r) := by
      intro z hz
      exact (hF z (hsub hz).1).differentiableAt.differentiableWithinAt
    have hdzero : (Metric.ball x r).EqOn (deriv F) 0 := fun z hz => (hsub hz).2
    have heq : F x = F u := IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball (convex_ball x r).isPreconnected
      hd hdzero (Metric.mem_ball_self hr) hu
    have hxu : x = u := F.injOn hx (hsub hu).1 heq
    have hre := congrArg Complex.re hxu
    dsimp [u] at hre
    have hfalse : False := by linarith
    exact hfalse.elim
  · exact hne

/-- The inverse of a true local homeomorphism takes punctured neighbourhoods to punctured neighbourhoods. -/
theorem openPartialHomeomorph_symm_tendsto_punctured (F : OpenPartialHomeomorph ℂ ℂ)
    (x : ℂ) (hx : x ∈ F.source) :
    Tendsto F.symm (𝓝[≠] F x) (𝓝[≠] x) := by
  have hcont := F.symm.continuousAt (F.map_source hx)
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [F.left_inv hx] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [(F.open_target.eventually_mem (F.map_source hx)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with y hy hyne
    change F.symm y ≠ x
    intro he
    apply hyne
    have hh := congrArg F he
    rwa [F.right_inv hy] at hh

/-- A true complex analytic open partial homeomorphism has analytic inverse, without assuming a nonzero derivative. -/
theorem openPartialHomeomorph_analytic_inverse (F : OpenPartialHomeomorph ℂ ℂ)
    (hF : AnalyticOnNhd ℂ F F.source) : AnalyticOnNhd ℂ F.symm F.target := by
  intro y hy
  let x := F.symm y
  have hx : x ∈ F.source := F.map_target hy
  have hDy := (openPartialHomeomorph_symm_tendsto_punctured F x hx).eventually
    (openPartialHomeomorph_analytic_deriv_punctured_ne_zero F hF x hx)
  have hpunct : ∀ᶠ z in 𝓝[≠] F x, DifferentiableAt ℂ F.symm z := by
    filter_upwards [hDy,
      (F.open_target.eventually_mem (F.map_source hx)).filter_mono nhdsWithin_le_nhds] with z hDz hz
    exact (F.hasDerivAt_symm hz hDz (hF (F.symm z) (F.map_target hz)).differentiableAt.hasDerivAt).differentiableAt
  have hinv := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hpunct
    (F.symm.continuousAt (F.map_source hx))
  simpa only [x, F.right_inv hy] using hinv

/-- Every analytic injective open chart map has nonzero complex derivative, as a conclusion rather than an extra hypothesis. -/
theorem openPartialHomeomorph_analytic_forward_deriv_ne_zero (F : OpenPartialHomeomorph ℂ ℂ)
    (hF : AnalyticOnNhd ℂ F F.source) (x : ℂ) (hx : x ∈ F.source) : deriv F x ≠ 0 := by
  have hG := openPartialHomeomorph_analytic_inverse F hF
  have hforward := (hF x hx).differentiableAt.hasDerivAt
  have hbackward := (hG (F x) (F.map_source hx)).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun z : ℂ => z) (deriv F.symm (F x) * deriv F x) x := by
    apply (hbackward.comp x hforward).congr_of_eventuallyEq
    filter_upwards [F.open_source.mem_nhds hx] with z hz
    exact (F.left_inv hz).symm
  have hmul : deriv F.symm (F x) * deriv F x = 1 := hcomp.unique (hasDerivAt_id x)
  intro hzero
  rw [hzero, mul_zero] at hmul
  exact zero_ne_one hmul

/-- The genuine coordinate open partial homeomorphism of a topological homeomorphism between two chart domains. -/
def riemannHomeomorphChart {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X ℂ) (E : X ≃ₜ Y) (g : OpenPartialHomeomorph Y ℂ) :
    OpenPartialHomeomorph ℂ ℂ :=
  e.symm.trans (E.toOpenPartialHomeomorph.trans g)

/-- The coordinate homeomorphism has exactly the local map domain required by. -/
theorem riemannHomeomorphChart_source {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X ℂ) (E : X ≃ₜ Y) (g : OpenPartialHomeomorph Y ℂ) :
    (riemannHomeomorphChart e E g).source = riemannChartMapDomain e E g := by
  simp only [riemannHomeomorphChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, Homeomorph.toOpenPartialHomeomorph_source, univ_inter]
  rfl

/-- The coordinate target is precisely the domain used for the inverse surface map in reversed charts. -/
theorem riemannHomeomorphChart_target {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X ℂ) (E : X ≃ₜ Y) (g : OpenPartialHomeomorph Y ℂ) :
    (riemannHomeomorphChart e E g).target = riemannChartMapDomain g E.symm e := by
  simp only [riemannHomeomorphChart, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.symm_target, Homeomorph.toOpenPartialHomeomorph_target,
    preimage_univ, inter_univ]
  rfl

/-- The actual forward chart homeomorphism agrees with the surface's local analytic expression. -/
theorem riemannHomeomorphChart_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X ℂ) (E : X ≃ₜ Y) (g : OpenPartialHomeomorph Y ℂ) (z : ℂ) :
    riemannHomeomorphChart e E g z = riemannChartMap e E g z := rfl

/-- Its true inverse is exactly the reversed-chart expression of the inverse homeomorphism. -/
theorem riemannHomeomorphChart_symm_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X ℂ) (E : X ≃ₜ Y) (g : OpenPartialHomeomorph Y ℂ) (z : ℂ) :
    (riemannHomeomorphChart e E g).symm z = riemannChartMap g E.symm e z := rfl

/-- An actual homeomorphism of Riemann surfaces that is analytic has analytic inverse, without adding a nonzero-derivative hypothesis. -/
theorem riemannAnalyticMap_homeomorph_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} (E : X ≃ₜ Y)
    (hE : RiemannAnalyticMap A B E) : RiemannAnalyticMap B A E.symm := by
  refine ⟨E.symm.continuous, ?_⟩
  intro g hg e he
  let F := riemannHomeomorphChart e E g
  have hF : AnalyticOnNhd ℂ F F.source := by
    rw [show F.source = riemannChartMapDomain e E g from riemannHomeomorphChart_source e E g]
    exact hE.2 e he g hg
  have hinv := openPartialHomeomorph_analytic_inverse F hF
  rw [show F.target = riemannChartMapDomain g E.symm e from riemannHomeomorphChart_target e E g] at hinv
  exact hinv



/-- The actual inverse of an arbitrary analytic bijection between Riemann surfaces is analytic. -/
theorem RiemannAnalyticMap.inverse_analytic {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {A : RiemannAtlas X} {B : RiemannAtlas Y}
    {f : X → Y} (hf : RiemannAnalyticMap A B f) (hbij : Function.Bijective f) :
    RiemannAnalyticMap B A (hf.toHomeomorph hbij).symm :=
  riemannAnalyticMap_homeomorph_symm (hf.toHomeomorph hbij) hf

/-- conformal equivalence by an analytic bijection is symmetric. -/
theorem RiemannConformallyEquivalent.symm {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {A : RiemannSurface X} {B : RiemannSurface Y}
    (hAB : RiemannConformallyEquivalent A B) : RiemannConformallyEquivalent B A := by
  obtain ⟨f, hf, hbij⟩ := hAB
  exact ⟨(hf.toHomeomorph hbij).symm, hf.inverse_analytic hbij, (hf.toHomeomorph hbij).symm.bijective⟩

end LowDimensionalTopology.Geometry.Surfaces
