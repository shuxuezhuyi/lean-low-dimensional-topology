/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareDevelopmentLocal
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open Set Topology
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P) [MetricSpace X]
local instance compactDevelopmentGeneratedTopology : TopologicalSpace S.Generated := ⊥
local instance compactDevelopmentGeneratedDiscreteTopology : DiscreteTopology S.Generated := ⟨rfl⟩

/--
A geometrically local uniform radius: each original-copy point is in an actual
local tessellation star whose ambient target contains its radius-epsilon ball. Centers may differ.
-/
def UniformLocalTessellationCover (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ x : P.Point, ∃ a : S.Copy, ∃ r : ℝ,
    S.LocalTessellation a r ∧ S.project (1,x) ∈ S.project '' S.copyNeighborhood a r ∧
      Metric.ball x.val ε ⊆ Metric.ball (S.copyEvaluation a) r

/-- The stronger same-class-star formulation is a special case of the genuine recentered uniform cover. -/
theorem UniformLocalTessellationRadius.to_uniform_cover {ε : ℝ}
    (hu : S.UniformLocalTessellationRadius ε) : S.UniformLocalTessellationCover ε := by
  refine ⟨hu.1,fun x => ?_⟩
  have ht := hu.2 x ε hu.1 le_rfl
  refine ⟨(1,x),ε,ht,ht.center_mem S hu.1,?_⟩
  change Metric.ball x.val ε ⊆ Metric.ball ((1 : S.Generated) • x.val) ε
  rw [one_smul]

/-- The actual distinguished polygon copy includes continuously in the literal quotient development. -/
theorem continuous_originalCopy : Continuous (fun x : P.Point => S.project (1,x)) :=
  S.continuous_project.comp (continuous_const.prodMk continuous_id)

/-- Restrict the actual local tessellation chart source by a true target ball around an arbitrary point. -/
def FiniteFiberLocalTessellationCondition.recenteredChart [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) {a : S.Copy} {r : ℝ}
    (ht : S.LocalTessellation a r) (q : S.Development) (ε : ℝ) :
    OpenPartialHomeomorph S.Development X :=
  OpenPartialHomeomorph.ofContinuousOpen
    ((ht.evaluation_injOn S).mono inter_subset_left |>.toPartialEquiv S.evaluation
      ((S.project '' S.copyNeighborhood a r) ∩ S.evaluation ⁻¹' Metric.ball (S.evaluation q) ε))
    S.continuous_evaluation_of_generated_isometric.continuousOn (h.isOpenMap_evaluation S)
    ((ht.isOpen_image S).inter (Metric.isOpen_ball.preimage S.continuous_evaluation_of_generated_isometric))

@[simp] theorem FiniteFiberLocalTessellationCondition.recenteredChart_apply [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) {a : S.Copy} {r : ℝ}
    (ht : S.LocalTessellation a r) (q p : S.Development) (ε : ℝ) :
    h.recenteredChart S ht q ε p = S.evaluation p := rfl

/-- The genuine recentered source contains its specified point at every positive radius. -/
theorem FiniteFiberLocalTessellationCondition.recenteredChart_center [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) {a : S.Copy} {r ε : ℝ}
    (ht : S.LocalTessellation a r) (q : S.Development)
    (hq : q ∈ S.project '' S.copyNeighborhood a r) (hε : 0 < ε) :
    q ∈ (h.recenteredChart S ht q ε).source := ⟨hq,Metric.mem_ball_self hε⟩

/-- A geometric containment of actual target balls proves the exact recentered chart target. -/
theorem FiniteFiberLocalTessellationCondition.recenteredChart_target [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) {a : S.Copy} {r ε : ℝ}
    (ht : S.LocalTessellation a r) (q : S.Development)
    (hb : Metric.ball (S.evaluation q) ε ⊆ Metric.ball (S.copyEvaluation a) r) :
    (h.recenteredChart S ht q ε).target = Metric.ball (S.evaluation q) ε := by
  change S.evaluation '' ((S.project '' S.copyNeighborhood a r) ∩
    S.evaluation ⁻¹' Metric.ball (S.evaluation q) ε) = _
  rw [image_inter_preimage,ht.evaluation_image S]
  exact inter_eq_right.mpr hb

/-- A finite collection of positive real radii has a single positive lower bound. -/
theorem positive_radius_bound {ι : Type*} (t : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ t,0 < r i) : ∃ ε : ℝ,0 < ε ∧ ∀ i ∈ t,ε ≤ r i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i t hit ih =>
    obtain ⟨ε,hε,hbound⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
    refine ⟨min ε (r i),lt_min hε (hr i (Finset.mem_insert_self i t)),?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hbound j hj)

/--
Compactness and actual local tessellation stars construct a uniform recentered radius using
inner-star finite subcovers; no global developing chart or fundamental domain is assumed.
-/
theorem FiniteFiberLocalTessellationCondition.uniform_cover_of_compact
    (h : S.FiniteFiberLocalTessellationCondition) (hc : IsCompact P.carrier) :
    ∃ ε : ℝ,S.UniformLocalTessellationCover ε := by
  classical
  let : CompactSpace P.Point := isCompact_iff_compactSpace.mp hc
  choose r hr ht using h.local_radius
  have hhalf : ∀ x : P.Point,S.LocalTessellation (1,x) (r x/2) := by
    intro x
    exact ht x _ (half_pos (hr x)) (by linarith [hr x])
  let U : P.Point → Set P.Point := fun x =>
    (fun y : P.Point => S.project (1,y)) ⁻¹' (S.project '' S.copyNeighborhood (1,x) (r x/2))
  have hU : ∀ x,IsOpen (U x) := fun x => (hhalf x).isOpen_image S |>.preimage S.continuous_originalCopy
  have hcover : (univ : Set P.Point) ⊆ ⋃ x,U x := by
    intro x _hx
    exact mem_iUnion.mpr ⟨x,(hhalf x).center_mem S (half_pos (hr x))⟩
  obtain ⟨t,hcover⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  obtain ⟨ε,hε,hbound⟩ := positive_radius_bound t (fun x => r x/2) (fun x _ => half_pos (hr x))
  refine ⟨ε,hε,?_⟩
  intro x
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
  have hyx : S.evaluation (S.project (1,x)) ∈ Metric.ball (S.copyEvaluation (1,y)) (r y/2) := by
    rw [←(hhalf y).evaluation_image S]
    exact mem_image_of_mem S.evaluation hxy
  have hdist : dist x.val y.val < r y/2 := by
    change dist ((1 : S.Generated) • x.val) ((1 : S.Generated) • y.val) < r y/2 at hyx
    simpa only [one_smul] using hyx
  refine ⟨(1,y),r y,ht y _ (hr y) le_rfl,?_,?_⟩
  · obtain ⟨b,hb,hbx⟩ := hxy
    exact ⟨b,S.copyNeighborhood_mono (1,y) (by linarith [hr y]) hb,hbx⟩
  · change Metric.ball x.val ε ⊆ Metric.ball ((1 : S.Generated) • y.val) (r y)
    rw [one_smul]
    intro z hz
    have hzdist : dist z x.val < ε := hz
    have he := hbound y hy
    calc dist z y.val ≤ dist z x.val + dist x.val y.val := dist_triangle _ _ _
         _ < ε + r y/2 := add_lt_add hzdist hdist
         _ ≤ r y := by linarith


/-- A genuine geometric uniform cover transfers to every actual generated copy. -/
theorem UniformLocalTessellationCover.at [IsIsometricSMul S.Generated X] {ε : ℝ}
    (hu : S.UniformLocalTessellationCover ε) (q : S.Development) :
    ∃ a : S.Copy,∃ r : ℝ,S.LocalTessellation a r ∧ q ∈ S.project '' S.copyNeighborhood a r ∧
      Metric.ball (S.evaluation q) ε ⊆ Metric.ball (S.copyEvaluation a) r := by
  obtain ⟨⟨g,x⟩,rfl⟩ := Quotient.exists_rep q
  obtain ⟨a,r,ht,hx,hb⟩ := hu.2 x
  refine ⟨S.translateCopy g
    a,r,_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.LocalTessellation.translate S ht g,?_,?_⟩
  · rw [S.quotientNeighborhood_translate]
    refine ⟨S.project (1,x),hx,?_⟩
    change S.project (g*1,x) = S.project (g,x)
    rw [mul_one]
  · have himage := image_mono (f := fun y : X => g • y) hb
    change (IsometryEquiv.constSMul g) '' Metric.ball x.val ε ⊆
      (IsometryEquiv.constSMul g) '' Metric.ball (S.copyEvaluation a) r at himage
    rw [(IsometryEquiv.constSMul g).image_ball,(IsometryEquiv.constSMul g).image_ball] at himage
    change Metric.ball (g • x.val) ε ⊆ Metric.ball (S.copyEvaluation (S.translateCopy g a)) r
    rw [S.copyEvaluation_translate]
    exact himage

/--
local tessellation plus the genuine uniform geometric cover constructs actual recentered charts
onto every native metric ball of one radius.
-/
theorem FiniteFiberLocalTessellationCondition.uniform_recentered_ball_charts [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) {ε : ℝ} (hu : S.UniformLocalTessellationCover ε)
    (q : S.Development) : ∃ e : OpenPartialHomeomorph S.Development X,
      q ∈ e.source ∧ e.target = Metric.ball (S.evaluation q) ε ∧ EqOn e S.evaluation e.source := by
  obtain ⟨a,r,ht,hq,hb⟩ := _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.UniformLocalTessellationCover.at S hu q
  exact ⟨h.recenteredChart S ht q ε,h.recenteredChart_center S ht q hq hu.1,
    h.recenteredChart_target S ht q hb,fun _ _ => rfl⟩

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing

namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open scoped UpperHalfPlane
variable {Γ : Type*} [Group Γ] [MulAction Γ ℍ]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- The actual uniform geometric uniform local cover, combined with local tessellation, gives the global native-plane development. -/
theorem FiniteFiberLocalTessellationCondition.covering_homeomorph_of_uniform_cover
    (h : S.FiniteFiberLocalTessellationCondition) {ε : ℝ} (hu : S.UniformLocalTessellationCover ε)
    (hm : S.MetricPolygonAssumptions) (hcl : P.carrier ⊆ closure P.interior) :
    IsCoveringMap S.evaluation ∧ IsHomeomorph S.evaluation := by
  let : IsIsometricSMul S.Generated ℍ := hm.generatedIsometricSMul S
  let : T2Space S.Development := h.t2Space S
  let : ConnectedSpace S.Development := S.development_connectedSpace_of_interior hm.connected_interior hcl
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.uniform_hyperbolic_charts_covering_homeomorph hu.1
    (h.uniform_recentered_ball_charts S hu)

/--
For a compact genuine polygon, local tessellation itself supplies uniform local by finite subcovers;
no uniform-star or global developing-chart hypothesis is required.
-/
theorem FiniteFiberLocalTessellationCondition.covering_homeomorph_of_compact
    (h : S.FiniteFiberLocalTessellationCondition) (hm : S.MetricPolygonAssumptions)
    (hcl : P.carrier ⊆ closure P.interior) (hc : IsCompact P.carrier) :
    IsCoveringMap S.evaluation ∧ IsHomeomorph S.evaluation := by
  obtain ⟨ε,hu⟩ := h.uniform_cover_of_compact S hc
  exact h.covering_homeomorph_of_uniform_cover S hu hm hcl

/-- Actual compact polygons satisfying local tessellation genuinely cover by closed copies with disjoint interiors. -/
theorem FiniteFiberLocalTessellationCondition.compact_polygon_tessellation
    (h : S.FiniteFiberLocalTessellationCondition) (hm : S.MetricPolygonAssumptions)
    (hcl : P.carrier ⊆ closure P.interior) (hc : IsCompact P.carrier) :
    (⋃ g : S.Generated,(fun x : ℍ => g • x) '' P.carrier) = univ ∧
      ∀ g k : S.Generated,g ≠ k →
        Disjoint ((fun x : ℍ => g • x) '' P.interior) ((fun x : ℍ => k • x) '' P.interior) := by
  have he := (h.covering_homeomorph_of_compact S hm hcl hc).2
  exact ⟨S.evaluation_surjective_iff_closed_cover.mp he.surjective,
    fun _ _ hne => S.original_interior_tiles_disjoint_of_evaluation_injective he.injective hne⟩

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
