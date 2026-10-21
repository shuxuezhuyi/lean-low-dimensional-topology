/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareDevelopmentTopology
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareDevelopmentConnected
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.FiniteFiberHausdorff
public import LowDimensionalTopology.Geometry.Hyperbolic.Covering.UniformCharts
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Tactic
@[expose] public section
noncomputable section
open Set
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Polygon.PoincarePolygon
variable {X : Type*} [MetricSpace X] (P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X)
/-- The polygon-copy metric is its literal ambient subspace metric. -/
instance pointMetric : MetricSpace P.Point :=
  inferInstanceAs (MetricSpace {x : X // x ∈ P.carrier})
end LowDimensionalTopology.Geometry.Polygon.PoincarePolygon

namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
open Topology
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)
variable [MetricSpace X]
local instance generatedTopologyMetric : TopologicalSpace S.Generated := ⊥
local instance generatedDiscreteTopologyMetric : DiscreteTopology S.Generated := ⟨rfl⟩

/-- The metric polygon hypotheses require isometries only for the specified pairing maps, together with an open connected interior. -/
structure MetricPolygonAssumptions : Prop where
  generator_isometry : ∀ s : P.Side, Isometry (fun x : X => S.element s • x)
  open_interior : IsOpen P.interior
  connected_interior : IsConnected P.interior

/-- The generator-isometry hypothesis implies that every actual element of the generated subgroup acts isometrically. -/
theorem MetricPolygonAssumptions.generated_isometry
    (h : S.MetricPolygonAssumptions) (g : S.Generated) : Isometry (fun x : X => g • x) := by
  have hi : ∀ (a : Γ) (_ha : a ∈ S.Generated), Isometry (fun x : X => a • x) := by
    intro a ha
    change a ∈ Subgroup.closure (range S.element) at ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨s,rfl⟩ := ha
      exact h.generator_isometry s
    | one =>
      intro x y
      simp only [one_smul]
    | mul a b _ha _hb iha ihb =>
      simpa only [Function.comp_def,mul_smul] using iha.comp ihb
    | inv a _ha ih =>
      intro x y
      have he := ih (a⁻¹ • x) (a⁻¹ • y)
      simpa only [smul_inv_smul] using he.symm
  exact hi g.val g.property

/-- The generated-group metric action is derived from generator-isometry hypothesis, rather than postulated for all ambient transformations. -/
theorem MetricPolygonAssumptions.generatedIsometricSMul
    (h : S.MetricPolygonAssumptions) : IsIsometricSMul S.Generated X :=
  ⟨fun g => h.generated_isometry S g⟩

/-- Original evaluation is continuous as soon as the actual generated subgroup acts by isometries. -/
theorem continuous_evaluation_of_generated_isometric [IsIsometricSMul S.Generated X] :
    Continuous S.evaluation := by
  have hc : Continuous S.copyEvaluation := by
    change Continuous (fun a : S.Generated × P.Point => a.1 • a.2.val)
    apply continuous_prod_of_discrete_left.mpr
    intro g
    exact (continuous_const_smul g).comp continuous_subtype_val
  exact hc.quotient_lift (fun _ _ h => S.gluing_evaluation h)

/-- The literal union of radius-r polygon balls around all indexed representatives of a glued point. -/
def copyNeighborhood (a : S.Copy) (r : ℝ) : Set S.Copy :=
  {b | ∃ c : S.Copy, S.project c = S.project a ∧ b.1 = c.1 ∧ dist b.2.val c.2.val < r}

/--
local tessellation at a given radius: the original local pieces cover the true ambient ball,
and each local evaluation fiber is a whole original gluing equivalence class.
-/
structure LocalTessellation (a : S.Copy) (r : ℝ) : Prop where
  image_eq : S.copyEvaluation '' S.copyNeighborhood a r = Metric.ball (S.copyEvaluation a) r
  fiber_eq : ∀ b ∈ S.copyNeighborhood a r, ∀ c : S.Copy,
    S.project c = S.project b ↔ c ∈ S.copyNeighborhood a r ∧ S.copyEvaluation c = S.copyEvaluation b

/-- The original local tessellation condition on every point of the distinguished original polygon copy. -/
structure FiniteFiberLocalTessellationCondition : Prop where
  finite_class : ∀ x : P.Point, (S.project ⁻¹' {S.project (1,x)}).Finite
  local_radius : ∀ x : P.Point, ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ r : ℝ, 0 < r → r ≤ r₀ → S.LocalTessellation (1,x) r

/-- A strong uniform same-class-star radius condition, sufficient for uniform developing charts. -/
def UniformLocalTessellationRadius (r₀ : ℝ) : Prop :=
  0 < r₀ ∧ ∀ x : P.Point, ∀ r : ℝ, 0 < r → r ≤ r₀ → S.LocalTessellation (1,x) r

/-- Every representative belongs to its positive-radius literal local neighborhood. -/
theorem mem_copyNeighborhood_self (a : S.Copy) {r : ℝ} (hr : 0 < r) :
    a ∈ S.copyNeighborhood a r := ⟨a,rfl,rfl,by simpa using hr⟩

/-- Increasing the radius genuinely increases the same union of indexed polygon balls. -/
theorem copyNeighborhood_mono (a : S.Copy) {r s : ℝ} (hrs : r ≤ s) :
    S.copyNeighborhood a r ⊆ S.copyNeighborhood a s := by
  rintro b ⟨c,hc,hg,hd⟩
  exact ⟨c,hc,hg,hd.trans_le hrs⟩

/-- These literal indexed-ball neighborhoods are open in the original discrete-index product topology. -/
theorem isOpen_copyNeighborhood (a : S.Copy) (r : ℝ) : IsOpen (S.copyNeighborhood a r) := by
  apply isOpen_iff_forall_mem_open.mpr
  rintro b ⟨c,hc,hg,hd⟩
  let U : Set S.Copy := {d | d.1 = c.1 ∧ dist d.2.val c.2.val < r}
  refine ⟨U,fun d h => ⟨c,hc,h.1,h.2⟩,?_,hg,hd⟩
  have hgOpen : IsOpen {d : S.Copy | d.1 = c.1} :=
    (isOpen_discrete ({c.1} : Set S.Generated)).preimage continuous_fst
  have hdOpen : IsOpen {d : S.Copy | dist d.2.val c.2.val < r} := by
    change IsOpen ((fun d : S.Copy => d.2.val) ⁻¹' Metric.ball c.2.val r)
    exact Metric.isOpen_ball.preimage (continuous_subtype_val.comp continuous_snd)
  exact hgOpen.inter hdOpen

/-- local tessellation proves saturation of the actual local indexed union, rather than postulating a quotient chart. -/
theorem LocalTessellation.saturated {a : S.Copy} {r : ℝ} (h : S.LocalTessellation a r) :
    S.project ⁻¹' (S.project '' S.copyNeighborhood a r) = S.copyNeighborhood a r := by
  ext c
  constructor
  · rintro ⟨b,hb,he⟩
    exact ((h.fiber_eq b hb c).mp he.symm).1
  · intro hc
    exact ⟨c,hc,rfl⟩

/-- The image of a genuine local tessellation union is an open subset of the actual glued quotient. -/
theorem LocalTessellation.isOpen_image {a : S.Copy} {r : ℝ} (h : S.LocalTessellation a r) :
    IsOpen (S.project '' S.copyNeighborhood a r) := by
  rw [S.isOpen_iff_project_preimage,h.saturated]
  exact S.isOpen_copyNeighborhood a r

/-- Genuine evaluation maps the actual quotient neighborhood onto the prescribed ambient metric ball. -/
theorem LocalTessellation.evaluation_image {a : S.Copy} {r : ℝ} (h : S.LocalTessellation a r) :
    S.evaluation '' (S.project '' S.copyNeighborhood a r) = Metric.ball (S.copyEvaluation a) r := by
  rw [image_image]
  exact h.image_eq

/-- vertex-cycles literal fiber equality proves injectivity on the actual open quotient neighborhood. -/
theorem LocalTessellation.evaluation_injOn {a : S.Copy} {r : ℝ} (h : S.LocalTessellation a r) :
    InjOn S.evaluation (S.project '' S.copyNeighborhood a r) := by
  rintro _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩ he
  exact ((h.fiber_eq b hb c).mpr ⟨hc,he.symm⟩).symm

/-- Positive-radius genuine local tessellation quotient neighborhoods contain their original glued center. -/
theorem LocalTessellation.center_mem {a : S.Copy} {r : ℝ} (_h : S.LocalTessellation a r)
    (hr : 0 < r) : S.project a ∈ S.project '' S.copyNeighborhood a r :=
  ⟨a,S.mem_copyNeighborhood_self a hr,rfl⟩


/-- The genuine left-copy translation is an equivalence of original indexed representatives. -/
def copyTranslationEquiv (g : S.Generated) : S.Copy ≃ S.Copy where
  toFun := S.translateCopy g
  invFun := S.translateCopy g⁻¹
  left_inv a := by
    simp only [translateCopy,inv_mul_cancel_left]
    cases a
    rfl
  right_inv a := by
    simp only [translateCopy,mul_inv_cancel_left]
    cases a
    rfl

/-- Translating a glued class translates exactly its union of actual polygon balls. -/
theorem copyNeighborhood_translate (g : S.Generated) (a : S.Copy) (r : ℝ) :
    S.copyNeighborhood (S.translateCopy g a) r =
      S.translateCopy g '' S.copyNeighborhood a r := by
  ext b
  constructor
  · rintro ⟨c,hc,hg,hd⟩
    refine ⟨S.translateCopy g⁻¹ b,?_,(S.copyTranslationEquiv g).right_inv b⟩
    refine ⟨S.translateCopy g⁻¹ c,?_,?_,hd⟩
    · have ht := congrArg (fun q : S.Development => g⁻¹ • q) hc
      change S.project (S.translateCopy g⁻¹ c) = g⁻¹ • (g • S.project a) at ht
      simpa only [inv_smul_smul] using ht
    · exact congrArg (fun k : S.Generated => g⁻¹*k) hg
  · rintro ⟨d,⟨c,hc,hg,hd⟩,rfl⟩
    refine ⟨S.translateCopy g c,?_,?_,hd⟩
    · change g • S.project c = g • S.project a
      exact congrArg (fun q : S.Development => g • q) hc
    · exact congrArg (fun k : S.Generated => g*k) hg

/-- The actual local quotient neighborhoods are precisely translates of those at the original copy. -/
theorem quotientNeighborhood_translate (g : S.Generated) (a : S.Copy) (r : ℝ) :
    S.project '' S.copyNeighborhood (S.translateCopy g a) r =
      g • (S.project '' S.copyNeighborhood a r) := by
  rw [S.copyNeighborhood_translate]
  ext q
  constructor
  · rintro ⟨b,⟨c,hc,rfl⟩,rfl⟩
    exact ⟨S.project c,⟨c,hc,rfl⟩,rfl⟩
  · rintro ⟨p,⟨c,hc,rfl⟩,rfl⟩
    exact ⟨S.translateCopy g c,⟨c,hc,rfl⟩,rfl⟩

omit [MetricSpace X] in
/-- Literal evaluation intertwines the original indexed-copy left translation. -/
theorem copyEvaluation_translate (g : S.Generated) (a : S.Copy) :
    S.copyEvaluation (S.translateCopy g a) = g • S.copyEvaluation a := mul_smul g a.1 a.2.val

/-- The actual local tessellation local covering and whole-fiber condition is invariant under generated isometries. -/
theorem LocalTessellation.translate [IsIsometricSMul S.Generated X]
    {a : S.Copy} {r : ℝ} (h : S.LocalTessellation a r) (g : S.Generated) :
    S.LocalTessellation (S.translateCopy g a) r := by
  constructor
  · rw [S.copyNeighborhood_translate,image_image]
    simp_rw [S.copyEvaluation_translate]
    rw [←image_image,h.image_eq]
    exact (IsometryEquiv.constSMul g).image_ball _ _
  · intro b hb c
    rw [S.copyNeighborhood_translate] at hb
    obtain ⟨b₀,hb₀,rfl⟩ := hb
    constructor
    · intro he
      have he₀ : S.project (S.translateCopy g⁻¹ c) = S.project b₀ := by
        have ht := congrArg (fun q : S.Development => g⁻¹ • q) he
        change S.project (S.translateCopy g⁻¹ c) = g⁻¹ • (g • S.project b₀) at ht
        simpa only [inv_smul_smul] using ht
      have hc₀ := ((h.fiber_eq b₀ hb₀ (S.translateCopy g⁻¹ c)).mp he₀).1
      refine ⟨?_,?_⟩
      · rw [S.copyNeighborhood_translate]
        exact ⟨S.translateCopy g⁻¹ c,hc₀,(S.copyTranslationEquiv g).right_inv c⟩
      · exact (S.gluing_evaluation ((S.project_eq_iff _ _).mp he))
    · rintro ⟨hc,he⟩
      rw [S.copyNeighborhood_translate] at hc
      obtain ⟨c₀,hc₀,rfl⟩ := hc
      have he₀ : S.copyEvaluation c₀ = S.copyEvaluation b₀ := by
        apply (MulAction.injective (g : S.Generated))
        simpa only [S.copyEvaluation_translate] using he
      have hp := (h.fiber_eq b₀ hb₀ c₀).mpr ⟨hc₀,he₀⟩
      change g • S.project c₀ = g • S.project b₀
      exact congrArg (fun q : S.Development => g • q) hp

/-- local tessellation at the original copy supplies genuine sufficiently small local tessellations at every indexed copy. -/
theorem FiniteFiberLocalTessellationCondition.local_radius_at [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) (a : S.Copy) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → S.LocalTessellation a r := by
  rcases a with ⟨g,x⟩
  obtain ⟨r₀,hr₀,ht⟩ := h.local_radius x
  refine ⟨r₀,hr₀,fun r hr hrr => ?_⟩
  have hh := _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.LocalTessellation.translate S (ht r hr
    hrr) g
  simpa only [translateCopy,mul_one] using hh


omit [MetricSpace X] in
/-- Every actual glued fiber is the left translate of its distinguished-copy fiber. -/
theorem project_fiber_translate (g : S.Generated) (q : S.Development) :
    S.project ⁻¹' {g • q} = S.translateCopy g '' (S.project ⁻¹' {q}) := by
  ext b
  constructor
  · intro hb
    refine ⟨S.translateCopy g⁻¹ b,?_,(S.copyTranslationEquiv g).right_inv b⟩
    change S.project b = g • q at hb
    change g⁻¹ • S.project b = q
    rw [hb,inv_smul_smul]
  · rintro ⟨c,hc,rfl⟩
    change S.project c = q at hc
    change g • S.project c = g • q
    exact congrArg (fun p : S.Development => g • p) hc

/-- The finite-class part of local tessellation applies to every actual indexed representative. -/
theorem FiniteFiberLocalTessellationCondition.finite_class_at
    (h : S.FiniteFiberLocalTessellationCondition) (a : S.Copy) : (S.project ⁻¹' {S.project a}).Finite := by
  rcases a with ⟨g,x⟩
  have he : S.project (g,x) = g • S.project (1,x) := by
    change S.project (g,x) = S.project (g*1,x)
    rw [mul_one]
  rw [he,S.project_fiber_translate]
  exact (h.finite_class x).image _

/-- Finitely many original copy points admit one radius inside any given open set containing them. -/
theorem finite_copy_ball_radius {F : Set S.Copy} (hF : F.Finite) {U : Set S.Copy}
    (hU : IsOpen U) (hFU : F ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ c ∈ F, ∀ b : S.Copy,
      b.1 = c.1 → dist b.2.val c.2.val < r → b ∈ U := by
  classical
  induction F,hF using Set.Finite.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert c F hc hF ih =>
    obtain ⟨r₀,hr₀,hball₀⟩ := ih (fun b hb => hFU (mem_insert_of_mem c hb))
    have hcU : c ∈ U := hFU (mem_insert c F)
    have ho : IsOpen ((fun p : P.Point => (c.1,p)) ⁻¹' U) :=
      hU.preimage (continuous_const.prodMk continuous_id)
    obtain ⟨r₁,hr₁,hball₁⟩ := Metric.isOpen_iff.mp ho c.2 hcU
    refine ⟨min r₀ r₁,lt_min hr₀ hr₁,?_⟩
    intro d hd b hindex hdist
    rcases mem_insert_iff.mp hd with he | hd
    · subst d
      have hbc : b.2 ∈ Metric.ball c.2 r₁ := hdist.trans_le (min_le_right _ _)
      have hbU := hball₁ hbc
      have he : (c.1,b.2) = b := Prod.ext hindex.symm rfl
      exact he ▸ hbU
    · exact hball₀ d hd b hindex (hdist.trans_le (min_le_left _ _))

/-- vertex-cycles finite class gives the actual indexed-ball neighborhood basis above every quotient point. -/
theorem FiniteFiberLocalTessellationCondition.copyNeighborhood_basis
    (h : S.FiniteFiberLocalTessellationCondition) (a : S.Copy) {U : Set S.Copy}
    (hU : IsOpen U) (hfU : S.project ⁻¹' {S.project a} ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ S.copyNeighborhood a r ⊆ U := by
  obtain ⟨r,hr,hball⟩ := S.finite_copy_ball_radius (h.finite_class_at S a) hU hfU
  refine ⟨r,hr,?_⟩
  rintro b ⟨c,hc,hg,hd⟩
  exact hball c hc b hg hd


/-- local tessellation constructs a saturated open quotient neighborhood inside any open set containing the full original fiber. -/
theorem FiniteFiberLocalTessellationCondition.saturated_open_basis [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) (q : S.Development) {U : Set S.Copy}
    (hU : IsOpen U) (hfU : S.project ⁻¹' {q} ⊆ U) :
    ∃ V : Set S.Development, IsOpen V ∧ q ∈ V ∧ S.project ⁻¹' V ⊆ U := by
  obtain ⟨a,rfl⟩ := Quotient.exists_rep q
  obtain ⟨δ,hδ,hδU⟩ := h.copyNeighborhood_basis S a hU hfU
  obtain ⟨r₀,hr₀,ht⟩ := h.local_radius_at S a
  let r := min δ r₀
  have hr : 0 < r := lt_min hδ hr₀
  have hlt := ht r hr (min_le_right _ _)
  refine ⟨S.project '' S.copyNeighborhood a r,hlt.isOpen_image S,hlt.center_mem S hr,?_⟩
  rw [hlt.saturated S]
  exact (S.copyNeighborhood_mono a (min_le_left _ _)).trans hδU

/-- actual positive-radius translated quotient neighborhoods form a basis at every original glued point. -/
theorem FiniteFiberLocalTessellationCondition.quotientNeighborhood_basis [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) (a : S.Copy) {U : Set S.Development}
    (hU : IsOpen U) (haU : S.project a ∈ U) :
    ∃ r : ℝ, 0 < r ∧ S.LocalTessellation a r ∧
      S.project '' S.copyNeighborhood a r ⊆ U := by
  have hfU : S.project ⁻¹' {S.project a} ⊆ S.project ⁻¹' U := by
    intro b hb
    change S.project b = S.project a at hb
    change S.project b ∈ U
    rwa [hb]
  obtain ⟨δ,hδ,hδU⟩ := h.copyNeighborhood_basis S a (hU.preimage S.continuous_project) hfU
  obtain ⟨r₀,hr₀,ht⟩ := h.local_radius_at S a
  refine ⟨min δ r₀,lt_min hδ hr₀,ht _ (lt_min hδ hr₀) (min_le_right _ _),?_⟩
  rintro _ ⟨b,hb,rfl⟩
  exact hδU (S.copyNeighborhood_mono a (min_le_left _ _) hb)

/-- The natural glued evaluation is an open map, proved from local tessellation and the actual quotient-neighborhood basis. -/
theorem FiniteFiberLocalTessellationCondition.isOpenMap_evaluation [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) : IsOpenMap S.evaluation := by
  intro U hU
  apply Metric.isOpen_iff.mpr
  rintro x ⟨q,hq,rfl⟩
  obtain ⟨a,rfl⟩ := Quotient.exists_rep q
  obtain ⟨r,hr,ht,hVU⟩ := h.quotientNeighborhood_basis S a hU hq
  refine ⟨r,hr,?_⟩
  change Metric.ball (S.copyEvaluation a) r ⊆ S.evaluation '' U
  rw [←ht.evaluation_image S]
  exact image_mono hVU


/-- The original nonempty polygon supplies an actual point of its glued development. -/
instance developmentNonempty : Nonempty S.Development := by
  obtain ⟨x,hx⟩ := P.interior_nonempty
  exact ⟨S.project (1,⟨x,P.interior_subset_carrier hx⟩)⟩

/-- local tessellation yields a genuine open partial homeomorphism with forward map exactly original evaluation. -/
def FiniteFiberLocalTessellationCondition.localChart [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) {a : S.Copy} {r : ℝ}
    (ht : S.LocalTessellation a r) : OpenPartialHomeomorph S.Development X :=
  OpenPartialHomeomorph.ofContinuousOpen
    ((ht.evaluation_injOn S).toPartialEquiv S.evaluation (S.project '' S.copyNeighborhood a r))
    S.continuous_evaluation_of_generated_isometric.continuousOn (h.isOpenMap_evaluation S) (ht.isOpen_image S)

@[simp] theorem FiniteFiberLocalTessellationCondition.localChart_apply [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) {a : S.Copy} {r : ℝ}
    (ht : S.LocalTessellation a r) (q : S.Development) :
    h.localChart S ht q = S.evaluation q := rfl

/-- The actual chart source is precisely the quotient image of the genuine local pieces. -/
theorem FiniteFiberLocalTessellationCondition.localChart_source [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) {a : S.Copy} {r : ℝ}
    (ht : S.LocalTessellation a r) :
    (h.localChart S ht).source = S.project '' S.copyNeighborhood a r := rfl

/-- The actual chart target is the true original ambient metric ball. -/
theorem FiniteFiberLocalTessellationCondition.localChart_target [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) {a : S.Copy} {r : ℝ}
    (ht : S.LocalTessellation a r) :
    (h.localChart S ht).target = Metric.ball (S.copyEvaluation a) r := ht.evaluation_image S

/-- The literal original local tessellation condition proves the natural glued evaluation is a local homeomorphism. -/
theorem FiniteFiberLocalTessellationCondition.isLocalHomeomorph_evaluation [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) : IsLocalHomeomorph S.evaluation := by
  apply IsLocalHomeomorph.mk
  intro q
  obtain ⟨a,rfl⟩ := Quotient.exists_rep q
  obtain ⟨r₀,hr₀,ht⟩ := h.local_radius_at S a
  have hlt := ht r₀ hr₀ le_rfl
  exact ⟨h.localChart S hlt,hlt.center_mem S hr₀,fun _ _ => rfl⟩


/-- A uniform same-class-star radius also works at every actual generated copy. -/
theorem UniformLocalTessellationRadius.at [IsIsometricSMul S.Generated X] {r₀ : ℝ}
    (hu : S.UniformLocalTessellationRadius r₀) (a : S.Copy) : S.LocalTessellation a r₀ := by
  rcases a with ⟨g,x⟩
  have ht := _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.LocalTessellation.translate S (hu.2 x r₀
    hu.1 le_rfl) g
  simpa only [translateCopy,mul_one] using ht

/-- local tessellation and a uniform same-class-star radius construct actual metric-ball charts at every developed point. -/
theorem FiniteFiberLocalTessellationCondition.uniform_ball_charts [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) {r₀ : ℝ} (hu : S.UniformLocalTessellationRadius r₀)
    (q : S.Development) : ∃ e : OpenPartialHomeomorph S.Development X,
      q ∈ e.source ∧ e.target = Metric.ball (S.evaluation q) r₀ ∧ EqOn e S.evaluation e.source := by
  obtain ⟨a,rfl⟩ := Quotient.exists_rep q
  have ht := _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.UniformLocalTessellationRadius.at S hu a
  refine ⟨h.localChart S ht,ht.center_mem S hu.1,?_,fun _ _ => rfl⟩
  exact h.localChart_target S ht


/-- Actual local tessellation finite fibers and genuine saturated-open neighborhoods make the literal quotient Hausdorff. -/
theorem FiniteFiberLocalTessellationCondition.t2Space [IsIsometricSMul S.Generated X]
    (h : S.FiniteFiberLocalTessellationCondition) : T2Space S.Development := by
  let : T2Space S.Copy := inferInstanceAs (T2Space (S.Generated × P.Point))
  apply _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.finiteFiber_t2Space_of_saturatedNeighborhoods S.project
    S.isQuotientMap_project.surjective
  · intro q
    obtain ⟨a,rfl⟩ := Quotient.exists_rep q
    exact h.finite_class_at S a
  · intro q U hU hfU
    exact h.saturated_open_basis S q hU hfU

/-- With the boundary-closure compatibility implicit for genuine polygons made explicit. -/
theorem FiniteFiberLocalTessellationCondition.development_hausdorff_connected_and_evaluation_localHomeomorph
    (h : S.FiniteFiberLocalTessellationCondition) (hm : S.MetricPolygonAssumptions)
    (hcl : P.carrier ⊆ closure P.interior) :
    T2Space S.Development ∧ ConnectedSpace S.Development ∧ IsLocalHomeomorph S.evaluation := by
  let : IsIsometricSMul S.Generated X := hm.generatedIsometricSMul S
  exact ⟨h.t2Space S,S.development_connectedSpace_of_interior hm.connected_interior hcl,
    h.isLocalHomeomorph_evaluation S⟩

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing

namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open scoped UpperHalfPlane
variable {Γ : Type*} [Group Γ] [MulAction Γ ℍ]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- local tessellation and the strong uniform-star condition give an actual global native-plane development. -/
theorem FiniteFiberLocalTessellationCondition.covering_homeomorph_evaluation [IsIsometricSMul S.Generated ℍ]
    (h : S.FiniteFiberLocalTessellationCondition) {r₀ : ℝ} (hu : S.UniformLocalTessellationRadius r₀)
    (hP : IsConnected P.carrier) : IsCoveringMap S.evaluation ∧ IsHomeomorph S.evaluation := by
  let : T2Space S.Development := h.t2Space S
  let : ConnectedSpace S.Development := S.development_connectedSpace hP
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.uniform_hyperbolic_charts_covering_homeomorph hu.1 (h.uniform_ball_charts S hu)

/-- With its genuine original boundary-closure condition, the open connected polygon satisfies the same conclusion. -/
theorem FiniteFiberLocalTessellationCondition.covering_homeomorph_evaluation_of_interior [IsIsometricSMul S.Generated ℍ]
    (h : S.FiniteFiberLocalTessellationCondition) {r₀ : ℝ} (hu : S.UniformLocalTessellationRadius r₀)
    (hP : IsConnected P.interior) (hcl : P.carrier ⊆ closure P.interior) :
    IsCoveringMap S.evaluation ∧ IsHomeomorph S.evaluation :=
  h.covering_homeomorph_evaluation S hu (P.carrier_isConnected hP hcl)

/-- The original metric/local-tessellation assumptions, a strong uniform-star radius, and genuine polygon compatibility give global evaluation. -/
theorem FiniteFiberLocalTessellationCondition.global_evaluation_from_original_assumptions
    (h : S.FiniteFiberLocalTessellationCondition) {r₀ : ℝ} (hu : S.UniformLocalTessellationRadius r₀)
    (hm : S.MetricPolygonAssumptions) (hcl : P.carrier ⊆ closure P.interior) :
    IsCoveringMap S.evaluation ∧ IsHomeomorph S.evaluation := by
  let : IsIsometricSMul S.Generated ℍ := hm.generatedIsometricSMul S
  exact h.covering_homeomorph_evaluation_of_interior S hu hm.connected_interior hcl

/-- Actual closed polygon copies cover the native plane and their interiors are disjoint,
as consequences of local tessellation and a strong uniform-star radius, never as additional hypotheses. -/
theorem FiniteFiberLocalTessellationCondition.original_polygon_tessellation
    (h : S.FiniteFiberLocalTessellationCondition) {r₀ : ℝ} (hu : S.UniformLocalTessellationRadius r₀)
    (hm : S.MetricPolygonAssumptions) (hcl : P.carrier ⊆ closure P.interior) :
    (⋃ g : S.Generated, (fun x : ℍ => g • x) '' P.carrier) = univ ∧
      ∀ g h : S.Generated, g ≠ h →
        Disjoint ((fun x : ℍ => g • x) '' P.interior) ((fun x : ℍ => h • x) '' P.interior) := by
  have he := (h.global_evaluation_from_original_assumptions S hu hm hcl).2
  exact ⟨(S.evaluation_surjective_iff_closed_cover).mp he.surjective,
    fun _ _ hne => S.original_interior_tiles_disjoint_of_evaluation_injective he.injective hne⟩

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
