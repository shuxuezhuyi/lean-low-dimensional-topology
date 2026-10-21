module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Order.Interval.Set.IsoIoo
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.UnitInterval
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletFiniteBoundaryCycles
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.EquivariantPath
public import LowDimensionalTopology.Geometry.Mobius.Classification.MobiusTypes
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.MobiusDiscTrapping
public import LowDimensionalTopology.Geometry.DiscreteGroups.Discreteness.DiscretenessCriteria
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletInfiniteBoundary
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped Pointwise unitInterval
namespace LowDimensionalTopology.Geometry.Fuchsian

/-- The genuine two-end compactification of a real curve, retaining both
endpoints separately even when their actual values coincide. -/
def twoEndCurveExtension {Y : Type*} (f : ℝ → Y) (a b : Y) : EReal → Y :=
  EReal.rec b f a

theorem twoEndCurveExtension_coe {Y : Type*} (f : ℝ → Y) (a b : Y) (t : ℝ) :
    twoEndCurveExtension f a b (t:EReal) = f t := rfl

theorem twoEndCurveExtension_top {Y : Type*} (f : ℝ → Y) (a b : Y) :
    twoEndCurveExtension f a b ⊤ = a := rfl

theorem twoEndCurveExtension_bot {Y : Type*} (f : ℝ → Y) (a b : Y) :
    twoEndCurveExtension f a b ⊥ = b := rfl

theorem twoEndCurveExtension_eq_toReal {Y : Type*} (f : ℝ → Y) (a b : Y)
    (q : EReal) (hqt : q ≠ ⊤) (hqb : q ≠ ⊥) :
    twoEndCurveExtension f a b q = f q.toReal := by
  lift q to ℝ using ⟨hqt,hqb⟩
  rfl

/-- Actual two-sided limits give a continuous map on the genuine compact
extended real interval. -/
theorem continuous_twoEndCurveExtension {Y : Type*} [TopologicalSpace Y]
    (f : ℝ → Y) (a b : Y) (hf : Continuous f)
    (hTop : Tendsto f atTop (𝓝 a)) (hBot : Tendsto f atBot (𝓝 b)) :
    Continuous (twoEndCurveExtension f a b) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  induction q using EReal.rec with
  | bot =>
      rw [continuousAt_iff_punctured_nhds,twoEndCurveExtension_bot]
      have hnb : ∀ᶠ q : EReal in 𝓝 ⊥, q ≠ ⊤ :=
        isClosed_singleton.isOpen_compl.mem_nhds (by simp)
      apply (hBot.comp EReal.tendsto_toReal_atBot).congr'
      filter_upwards [hnb.filter_mono nhdsWithin_le_nhds,
        (self_mem_nhdsWithin : ∀ᶠ q : EReal in 𝓝[≠] ⊥, q ≠ ⊥)] with q hqt hqb
      exact (twoEndCurveExtension_eq_toReal f a b q hqt hqb).symm

  | top =>
      rw [continuousAt_iff_punctured_nhds,twoEndCurveExtension_top]
      have hnb : ∀ᶠ q : EReal in 𝓝 ⊤, q ≠ ⊥ :=
        isClosed_singleton.isOpen_compl.mem_nhds (by simp)
      apply (hTop.comp EReal.tendsto_toReal_atTop).congr'
      filter_upwards [hnb.filter_mono nhdsWithin_le_nhds,
        (self_mem_nhdsWithin : ∀ᶠ q : EReal in 𝓝[≠] ⊤, q ≠ ⊤)] with q hqb hqt
      exact (twoEndCurveExtension_eq_toReal f a b q hqt hqb).symm
  | coe r =>
      have hnb : ∀ᶠ q : EReal in 𝓝 (r:EReal), q ≠ ⊥ :=
        isClosed_singleton.isOpen_compl.mem_nhds (by simp)
      have hnt : ∀ᶠ q : EReal in 𝓝 (r:EReal), q ≠ ⊤ :=
        isClosed_singleton.isOpen_compl.mem_nhds (by simp)
      apply (hf.continuousAt.comp (EReal.tendsto_toReal (by simp) (by simp))).congr
      filter_upwards [hnb,hnt] with q hqb hqt
      exact (twoEndCurveExtension_eq_toReal f a b q hqt hqb).symm


/-- The actual compactified image consists of the original curve and its two
actual limiting endpoints. -/
theorem twoEndCurveExtension_range {Y : Type*} (f : ℝ → Y) (a b : Y) :
    range (twoEndCurveExtension f a b) = insert a (insert b (range f)) := by
  apply subset_antisymm
  · rintro y ⟨q,rfl⟩
    induction q using EReal.rec with
    | bot => exact mem_insert_of_mem _ (mem_insert _ _)
    | top => exact mem_insert _ _
    | coe t => exact mem_insert_of_mem _ (mem_insert_of_mem _ (mem_range_self t))
  · intro y hy
    rcases mem_insert_iff.mp hy with he | hy
    · exact ⟨⊤,he.symm⟩
    · rcases mem_insert_iff.mp hy with he | hy
      · exact ⟨⊥,he.symm⟩
      · obtain ⟨t,rfl⟩ := hy
        exact ⟨(t:EReal),rfl⟩

/-- Distinct actual endpoints outside the actual curve preserve genuine global
injectivity after adjoining the two ends. -/
theorem twoEndCurveExtension_injective {Y : Type*} (f : ℝ → Y) (a b : Y)
    (hf : Function.Injective f) (hab : a ≠ b) (ha : a ∉ range f) (hb : b ∉ range f) :
    Function.Injective (twoEndCurveExtension f a b) := by
  intro q r he
  induction q using EReal.rec with
  | bot =>
      induction r using EReal.rec with
      | bot => rfl
      | top => exact False.elim (hab he.symm)
      | coe t => exact False.elim (hb ⟨t,he.symm⟩)
  | top =>
      induction r using EReal.rec with
      | bot => exact False.elim (hab he)
      | top => rfl
      | coe t => exact False.elim (ha ⟨t,he.symm⟩)
  | coe s =>
      induction r using EReal.rec with
      | bot => exact False.elim (hb ⟨s,he⟩)
      | top => exact False.elim (ha ⟨s,he⟩)
      | coe t => exact congrArg Real.toEReal (hf he)

/-- Genuine two-sided limits identify the entire closure of the actual real
curve with its genuine compact two-end extension. -/
theorem twoEndCurveExtension_range_eq_closure {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : ℝ → Y) (a b : Y) (hf : Continuous f)
    (hTop : Tendsto f atTop (𝓝 a)) (hBot : Tendsto f atBot (𝓝 b)) :
    range (twoEndCurveExtension f a b) = closure (range f) := by
  have hcont := continuous_twoEndCurveExtension f a b hf hTop hBot
  have hcompact := isCompact_range hcont
  have hsubset : range f ⊆ range (twoEndCurveExtension f a b) := by
    rintro y ⟨t,rfl⟩
    exact ⟨(t:EReal),rfl⟩
  apply subset_antisymm
  · rw [twoEndCurveExtension_range]
    apply insert_subset
    · exact isClosed_closure.mem_of_tendsto hTop
        (Eventually.of_forall fun t => subset_closure (mem_range_self t))
    · apply insert_subset
      · exact isClosed_closure.mem_of_tendsto hBot
          (Eventually.of_forall fun t => subset_closure (mem_range_self t))
      · exact subset_closure
  · exact closure_minimal hsubset hcompact.isClosed

/-- The compactified genuine real line is an actual closed embedded arc when
its genuine limiting endpoints are distinct and are not on the original curve. -/
theorem twoEndCurveExtension_isClosedEmbedding
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : ℝ → Y) (a b : Y) (hf : Continuous f) (hinj : Function.Injective f)
    (hTop : Tendsto f atTop (𝓝 a)) (hBot : Tendsto f atBot (𝓝 b))
    (hab : a ≠ b) (ha : a ∉ range f) (hb : b ∉ range f) :
    IsClosedEmbedding (twoEndCurveExtension f a b) :=
  (continuous_twoEndCurveExtension f a b hf hTop hBot).isClosedEmbedding
    (twoEndCurveExtension_injective f a b hinj hab ha hb)

/-- An actual increasing coordinate on the genuine extended real interval,
using the standard existing order isomorphism from the real line to `(-1,1)`. -/
def extendedRealUnitParameter : EReal → I :=
  EReal.rec 0 (fun t => ⟨((orderIsoIooNegOneOne ℝ t).val+1)/2,by
    have h := (orderIsoIooNegOneOne ℝ t).property
    constructor <;> linarith [h.1,h.2]⟩) 1

theorem extendedRealUnitParameter_coe_bounds (t : ℝ) :
    0 < (extendedRealUnitParameter (t:EReal) : ℝ) ∧
      (extendedRealUnitParameter (t:EReal) : ℝ) < 1 := by
  have h := (orderIsoIooNegOneOne ℝ t).property
  change 0 < ((orderIsoIooNegOneOne ℝ t).val+1)/2 ∧
    ((orderIsoIooNegOneOne ℝ t).val+1)/2 < 1
  constructor <;> linarith [h.1,h.2]

theorem extendedRealUnitParameter_strictMono : StrictMono extendedRealUnitParameter := by
  intro q r hqr
  induction q using EReal.rec with
  | bot =>
      induction r using EReal.rec with
      | bot => exact False.elim ((lt_irrefl _) hqr)
      | top => exact zero_lt_one
      | coe t => exact (extendedRealUnitParameter_coe_bounds t).1
  | top => exact False.elim ((not_lt_of_ge le_top) hqr)
  | coe s =>
      induction r using EReal.rec with
      | bot => exact False.elim ((not_lt_of_ge bot_le) hqr)
      | top => exact (extendedRealUnitParameter_coe_bounds s).2
      | coe t =>
          have hst : s < t := EReal.coe_lt_coe_iff.mp hqr
          have hphi := (orderIsoIooNegOneOne ℝ).strictMono hst
          change ((orderIsoIooNegOneOne ℝ s).val+1)/2 <
            ((orderIsoIooNegOneOne ℝ t).val+1)/2
          have hphi' : (orderIsoIooNegOneOne ℝ s).val <
              (orderIsoIooNegOneOne ℝ t).val := hphi
          linarith

theorem extendedRealUnitParameter_surjective : Function.Surjective extendedRealUnitParameter := by
  intro u
  by_cases h0 : u = 0
  · exact ⟨⊥,h0.symm⟩
  by_cases h1 : u = 1
  · exact ⟨⊤,h1.symm⟩
  have hu0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1
    (fun h => h0 (Subtype.ext h.symm))
  have hu1 : (u:ℝ) < 1 := lt_of_le_of_ne u.property.2
    (fun h => h1 (Subtype.ext h))
  let v : Ioo (-1:ℝ) 1 := ⟨2*(u:ℝ)-1,by constructor <;> linarith⟩
  refine ⟨((orderIsoIooNegOneOne ℝ).symm v : EReal),?_⟩
  apply Subtype.ext
  change ((orderIsoIooNegOneOne ℝ ((orderIsoIooNegOneOne ℝ).symm v)).val+1)/2 = (u:ℝ)
  rw [(orderIsoIooNegOneOne ℝ).apply_symm_apply]
  dsimp [v]
  ring

/-- The genuine extended real interval is the actual standard closed unit
interval, as an order isomorphism and hence as a homeomorphism. -/
def extendedRealUnitIntervalOrderIso : EReal ≃o I :=
  extendedRealUnitParameter_strictMono.orderIsoOfSurjective
    extendedRealUnitParameter extendedRealUnitParameter_surjective

def extendedRealUnitIntervalHomeomorph : EReal ≃ₜ I :=
  extendedRealUnitIntervalOrderIso.toHomeomorph

/-- The genuine closed-unit-interval path obtained by adjoining both actual
limits to the original real curve. -/
def twoEndCurvePath {Y : Type*} [TopologicalSpace Y]
    (f : ℝ → Y) (a b : Y) (hf : Continuous f)
    (hTop : Tendsto f atTop (𝓝 a)) (hBot : Tendsto f atBot (𝓝 b)) : Path b a where
  toFun t := twoEndCurveExtension f a b (extendedRealUnitIntervalHomeomorph.symm t)
  continuous_toFun := (continuous_twoEndCurveExtension f a b hf hTop hBot).comp
    extendedRealUnitIntervalHomeomorph.symm.continuous
  source' := by
    change twoEndCurveExtension f a b (extendedRealUnitIntervalOrderIso.symm ⊥) = b
    rw [OrderIso.map_bot,twoEndCurveExtension_bot]
  target' := by
    change twoEndCurveExtension f a b (extendedRealUnitIntervalOrderIso.symm ⊤) = a
    rw [OrderIso.map_top,twoEndCurveExtension_top]

theorem twoEndCurvePath_range {Y : Type*} [TopologicalSpace Y]
    (f : ℝ → Y) (a b : Y) (hf : Continuous f)
    (hTop : Tendsto f atTop (𝓝 a)) (hBot : Tendsto f atBot (𝓝 b)) :
    range (twoEndCurvePath f a b hf hTop hBot) = insert a (insert b (range f)) := by
  change range (twoEndCurveExtension f a b ∘ extendedRealUnitIntervalHomeomorph.symm) = _
  rw [range_comp,extendedRealUnitIntervalHomeomorph.symm.surjective.range_eq,image_univ,
    twoEndCurveExtension_range]

theorem twoEndCurvePath_injective {Y : Type*} [TopologicalSpace Y]
    (f : ℝ → Y) (a b : Y) (hf : Continuous f) (hinj : Function.Injective f)
    (hTop : Tendsto f atTop (𝓝 a)) (hBot : Tendsto f atBot (𝓝 b))
    (hab : a ≠ b) (ha : a ∉ range f) (hb : b ∉ range f) :
    Function.Injective (twoEndCurvePath f a b hf hTop hBot) :=
  (twoEndCurveExtension_injective f a b hinj hab ha hb).comp
    extendedRealUnitIntervalHomeomorph.symm.injective

/-- With a common actual endpoint outside the curve, the compactified map is
injective before its terminal end; precisely the two interval ends are identified. -/
theorem twoEndCurveExtension_same_endpoint_injOn {Y : Type*} (f : ℝ → Y) (a : Y)
    (hf : Function.Injective f) (ha : a ∉ range f) :
    Set.InjOn (twoEndCurveExtension f a a) (Iio (⊤:EReal)) := by
  intro q hq r hr he
  induction q using EReal.rec with
  | top => exact False.elim ((lt_irrefl _) (mem_Iio.mp hq))
  | bot =>
      induction r using EReal.rec with
      | top => exact False.elim ((lt_irrefl _) (mem_Iio.mp hr))
      | bot => rfl
      | coe t => exact False.elim (ha ⟨t,he.symm⟩)
  | coe s =>
      induction r using EReal.rec with
      | top => exact False.elim ((lt_irrefl _) (mem_Iio.mp hr))
      | bot => exact False.elim (ha ⟨s,he⟩)
      | coe t => exact congrArg Real.toEReal (hf he)

theorem twoEndCurvePath_same_endpoint_injOn {Y : Type*} [TopologicalSpace Y]
    (f : ℝ → Y) (a : Y) (hf : Continuous f) (hinj : Function.Injective f)
    (hTop : Tendsto f atTop (𝓝 a)) (hBot : Tendsto f atBot (𝓝 a)) (ha : a ∉ range f) :
    Set.InjOn (twoEndCurvePath f a a hf hTop hBot) (Iio (1:I)) := by
  intro u hu v hv he
  have hmap : extendedRealUnitIntervalOrderIso.symm (1:I) = (⊤:EReal) := by
    change extendedRealUnitIntervalOrderIso.symm ⊤ = ⊤
    exact OrderIso.map_top _
  apply extendedRealUnitIntervalHomeomorph.symm.injective
  apply twoEndCurveExtension_same_endpoint_injOn f a hinj ha
  · change extendedRealUnitIntervalOrderIso.symm u < ⊤
    rw [←hmap]
    exact extendedRealUnitIntervalOrderIso.symm.strictMono (mem_Iio.mp hu)
  · change extendedRealUnitIntervalOrderIso.symm v < ⊤
    rw [←hmap]
    exact extendedRealUnitIntervalOrderIso.symm.strictMono (mem_Iio.mp hv)
  · exact he

/-- A genuine embedded real curve whose two ends tend to one actual exterior
point becomes a genuine Jordan curve on adjoining that one point. -/
theorem twoEndCurve_same_endpoint_exists_circle {Y : Type*} [TopologicalSpace Y]
    (f : ℝ → Y) (a : Y) (hf : Continuous f) (hinj : Function.Injective f)
    (hTop : Tendsto f atTop (𝓝 a)) (hBot : Tendsto f atBot (𝓝 a)) (ha : a ∉ range f) :
    ∃ J : Circle → Y, Continuous J ∧ Function.Injective J ∧ range J = insert a (range f) := by
  let γ := twoEndCurvePath f a a hf hTop hBot
  refine ⟨closedPathUnitCircleMap γ,?_⟩
  have hs := closedPathUnitCircleMap_spec γ
    (twoEndCurvePath_same_endpoint_injOn f a hf hinj hTop hBot ha)
  refine ⟨hs.1,hs.2.1,?_⟩
  rw [hs.2.2,twoEndCurvePath_range,insert_idem]


open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Genuine compact-uniform boundary dynamics give the actual forward endpoint
of the entire developed real curve, not only of its integer orbit points. -/
theorem equivariantPathExtension_tendsto_atTop_of_uniform
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
      _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (k : H) {x : D.carrier} (γ : Path x (k • x)) (a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hunif : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusIteratesConvergeUniformlyOn k.val a
      (Subtype.val '' range γ)) :
    Tendsto (fun t : ℝ => (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ t).val) atTop (𝓝 a) := by
  rw [tendsto_def]
  intro V hV
  have hu := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusIteratesConvergeUniformlyOn_iff k.val a
    _).mp hunif V hV
  obtain ⟨N,hN⟩ := eventually_atTop.mp hu
  apply eventually_atTop.mpr
  refine ⟨(N:ℝ),?_⟩
  intro t ht
  let n := ⌊t⌋₊
  have ht0 : 0 ≤ t := (Nat.cast_nonneg N).trans ht
  have hn : N ≤ n := Nat.le_floor ht
  have htn : t ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.pathExtensionInterval (n:ℤ) := by
    change (n:ℝ) ≤ t ∧ t ≤ (n:ℝ)+1
    exact ⟨Nat.floor_le ht0,(Nat.lt_floor_add_one t).le⟩
  have hγmem : γ.extend (t-(n:ℝ)) ∈ range γ := by
    rw [←γ.extend_range]
    exact mem_range_self _
  have hpoint := hN n hn (γ.extend (t-(n:ℝ))).val ⟨_,hγmem,rfl⟩
  change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ t).val ∈ V
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_on_interval k γ (n:ℤ) htn]
  change (((k^(n:ℤ)).val : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (γ.extend (t-((n:ℤ):ℝ))).val) ∈ V
  simpa only [Int.cast_natCast,Subgroup.coe_zpow,zpow_natCast,Subgroup.coe_pow] using hpoint

/-- The actual backward endpoint of the entire developed real curve follows
from compact-uniform dynamics of the actual inverse element. -/
theorem equivariantPathExtension_tendsto_atBot_of_inverse_uniform
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
      _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (k : H) {x : D.carrier} (γ : Path x (k • x)) (a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hunif : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusIteratesConvergeUniformlyOn k.val⁻¹ a
      (Subtype.val '' range γ)) :
    Tendsto (fun t : ℝ => (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ t).val) atBot (𝓝 a) := by
  rw [tendsto_def]
  intro V hV
  have hu := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusIteratesConvergeUniformlyOn_iff k.val⁻¹ a
    _).mp hunif V hV
  obtain ⟨N,hN⟩ := eventually_atTop.mp hu
  apply eventually_atBot.mpr
  refine ⟨-(N:ℝ)-1,?_⟩
  intro t ht
  let m := ⌊-t⌋₊
  let n : ℤ := -(m:ℤ)-1
  have ht0 : 0 ≤ -t := by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ))]
  have hml : (m:ℝ) ≤ -t := Nat.floor_le ht0
  have hmu : -t < (m:ℝ)+1 := Nat.lt_floor_add_one (-t)
  have hNm : N ≤ m := Nat.le_floor (by linarith)
  have htn : t ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.pathExtensionInterval n := by
    change ((-(m:ℤ)-1:ℤ):ℝ) ≤ t ∧ t ≤ ((-(m:ℤ)-1:ℤ):ℝ)+1
    push_cast
    constructor <;> linarith
  have hγmem : γ.extend (t-(n:ℝ)) ∈ range γ := by
    rw [←γ.extend_range]
    exact mem_range_self _
  have hpoint := hN (m+1) (by omega) (γ.extend (t-(n:ℝ))).val ⟨_,hγmem,rfl⟩
  have hpow : k^n = (k⁻¹)^(m+1) := by
    have hn : n = -((m+1:ℕ):ℤ) := by dsimp [n]; ring
    rw [hn,zpow_neg,zpow_natCast,inv_pow]
  change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ t).val ∈ V
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_on_interval k γ n htn]
  change (((k^n).val : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (γ.extend
    (t-(n:ℝ))).val) ∈ V
  simpa only [hpow,Subgroup.coe_pow,Subgroup.coe_inv] using hpoint

/-- An actual infinite-order group element has no fixed point in a domain on
which the original whole-group action is properly discontinuous. -/
theorem infiniteOrder_fixed_not_in_discontinuous_domain
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
      _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H D.carrier)
    (k : H) (hk : Function.Injective (fun n : ℤ => k^n))
    (a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (ha : (k.val : Equiv.Perm
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) a = a) :
    a ∉ D.carrier := by
  intro hmem
  have ho := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isOfFinOrder_of_finite_stabilizer k a (hD.finite_stabilizer a hmem) ha
  exact (injective_zpow_iff_not_isOfFinOrder.mp hk) ho

/-- The genuine full-space fixed set is unchanged by inversion of the actual
Möbius transformation. -/
theorem curve_mobiusExtendedFixedPoints_inv (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusExtendedFixedPoints f⁻¹ = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusExtendedFixedPoints f := by
  ext q
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusExtendedSpaceHom
    f⁻¹) q = q ↔ (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusExtendedSpaceHom f) q = q
  rw [map_inv]
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusExtendedSpaceHom
    f).symm q = q ↔ (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusExtendedSpaceHom f) q = q
  rw [Homeomorph.symm_apply_eq]
  exact eq_comm

/-- Inversion preserves the actual geometric loxodromic type. -/
theorem curve_mobiusLoxodromic_inv {f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (hf :
  _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic f) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic f⁻¹ := by
  obtain ⟨hne,a,b,hab,hfixed⟩ := hf
  refine ⟨inv_ne_one.mpr hne,a,b,hab,?_⟩
  rw [curve_mobiusExtendedFixedPoints_inv]
  exact hfixed

/-- A genuine parabolic developed curve has one and the same actual boundary
endpoint as its real parameter tends in either direction to infinity. -/
theorem equivariantPathExtension_parabolic_endpoints
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
      _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H D.carrier)
    (k : H) (hk : Function.Injective (fun n : ℤ => k^n))
    {x : D.carrier} (γ : Path x (k • x)) (hpar : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic k.val) :
    ∃ a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, (k.val : Equiv.Perm
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) a = a ∧ a ∉ D.carrier ∧
      Tendsto (fun t : ℝ => (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ
        t).val) atTop (𝓝 a) ∧
      Tendsto (fun t : ℝ => (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ t).val) atBot (𝓝 a) := by
  obtain ⟨a,ha,_hpa,hua⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.parabolic_iterates_tendsto_unique_fixedPoint_uniformly_off k.val hpar
  obtain ⟨b,hb,_hpb,hub⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.parabolic_iterates_tendsto_unique_fixedPoint_uniformly_off k.val⁻¹
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discTrap_parabolic_inv k.val hpar)
  have hbf : (k.val : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) b = b := by
    simpa only [inv_inv] using _root_.LowDimensionalTopology.Geometry.Mobius.mobius_inv_fixed hb
  obtain ⟨p,hp⟩ := hpar.2
  have hab : a = b := ((hp a).mp ha).trans ((hp b).mp hbf).symm
  subst b
  have hnot := infiniteOrder_fixed_not_in_discontinuous_domain D hD k hk a ha
  have hcompact : IsCompact (Subtype.val '' range γ : Set
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
    (isCompact_range γ.continuous).image continuous_subtype_val
  have hnotK : a ∉ (Subtype.val '' range γ : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rintro ⟨z,_hz,hza⟩
    exact hnot (hza ▸ z.property)
  exact ⟨a,ha,hnot,equivariantPathExtension_tendsto_atTop_of_uniform D k γ a
    (hua _ hcompact hnotK),equivariantPathExtension_tendsto_atBot_of_inverse_uniform D k γ a
    (hub _ hcompact hnotK)⟩

/-- A genuine loxodromic developed curve has two distinct actual endpoints as
its real parameter tends in the two directions to infinity. Both endpoints
are outside the original discontinuity domain. -/
theorem equivariantPathExtension_loxodromic_endpoints
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
      _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H D.carrier)
    (k : H) (hk : Function.Injective (fun n : ℤ => k^n))
    {x : D.carrier} (γ : Path x (k • x)) (hlox : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic k.val) :
    ∃ A B : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, A ≠ B ∧
      (k.val : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) A = A ∧
      (k.val : Equiv.Perm
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) B = B ∧ A ∉ D.carrier ∧ B ∉ D.carrier ∧
      Tendsto (fun t : ℝ => (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ
        t).val) atTop (𝓝 A) ∧
      Tendsto (fun t : ℝ => (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ t).val) atBot (𝓝 B) := by
  obtain ⟨A,B,hAB,hA,hB,hforward,hback⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_loxodromic_attracting_repelling k.val hlox
  obtain ⟨a,b,_hab,_ha,hb,hpoint,hua⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.loxodromic_iterates_tendsto_attractor_uniformly_off_repeller k.val hlox
  obtain ⟨c,d,_hcd,_hc,hd,hpointInv,huc⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.loxodromic_iterates_tendsto_attractor_uniformly_off_repeller k.val⁻¹
    (curve_mobiusLoxodromic_inv hlox)
  have hdf : (k.val : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) d = d := by
    simpa only [inv_inv] using _root_.LowDimensionalTopology.Geometry.Mobius.mobius_inv_fixed hd
  have hpointne (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hz : (k.val : Equiv.Perm
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) z = z) :
      x.val ≠ z := fun h =>
    infiniteOrder_fixed_not_in_discontinuous_domain D hD k hk z hz (h ▸ x.property)
  have haA : a = A := tendsto_nhds_unique
    (hpoint x.val (hpointne b hb)) (hforward x.val (hpointne B hB))
  have hcB : c = B := tendsto_nhds_unique
    (hpointInv x.val (hpointne d hdf)) (hback x.val (hpointne A hA))
  subst a
  subst c
  have hcompact : IsCompact (Subtype.val '' range γ : Set
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
    (isCompact_range γ.continuous).image continuous_subtype_val
  have havoid (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hz : (k.val : Equiv.Perm
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) z = z) :
      z ∉ (Subtype.val '' range γ : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    rintro ⟨u,_hu,huz⟩
    exact infiniteOrder_fixed_not_in_discontinuous_domain D hD k hk z hz (huz ▸ u.property)
  refine ⟨A,B,hAB,hA,hB,infiniteOrder_fixed_not_in_discontinuous_domain D hD k hk A hA,
    infiniteOrder_fixed_not_in_discontinuous_domain D hD k hk B hB,?_,?_⟩
  · exact equivariantPathExtension_tendsto_atTop_of_uniform D k γ A (hua _ hcompact (havoid b hb))
  · exact equivariantPathExtension_tendsto_atBot_of_inverse_uniform D k γ B
      (huc _ hcompact (havoid d hdf))

/-- An actual endpoint of a developed curve, fixed by its genuine infinite-order
element, lies on the actual frontier of the original discontinuity domain. -/
theorem equivariantPathExtension_limit_mem_frontier
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
      _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H D.carrier)
    (k : H) (hk : Function.Injective (fun n : ℤ => k^n))
    {x : D.carrier} (γ : Path x (k • x)) (a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    {l : Filter ℝ} [NeBot l]
    (ha : (k.val : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) a = a)
    (hlim : Tendsto (fun t : ℝ => (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension
      k γ t).val) l (𝓝 a)) :
    a ∈ frontier D.carrier := by
  have hcl : a ∈ closure D.carrier := isClosed_closure.mem_of_tendsto hlim
    (Eventually.of_forall fun t => subset_closure
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ t).property)
  rw [frontier,D.isOpen.interior_eq]
  exact ⟨hcl,infiniteOrder_fixed_not_in_discontinuous_domain D hD k hk a ha⟩

/-- An actual infinite-order element of the original discrete disc action is
genuinely parabolic or hyperbolic; ellipticity is excluded by the already-proved
finite-order theorem, rather than as an additional hypothesis. -/
theorem unitDisc_infiniteOrder_parabolic_or_hyperbolic
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H)
    (k : H) (hk : Function.Injective (fun n : ℤ => k^n)) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic k.val ∨ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic k.val := by
  have hnot := injective_zpow_iff_not_isOfFinOrder.mp hk
  have hne : k.val ≠ 1 := by
    intro h
    have hkone : k = 1 := Subtype.ext h
    exact hnot (hkone ▸ IsOfFinOrder.one)
  rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy k.val hne with hpar | hlox | hell
  · exact Or.inl hpar
  · exact Or.inr ⟨hlox,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc,P.image_eq k⟩
  · have hfin := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elliptic_finiteOrder H P.discrete k.val k.property hell
    exact False.elim (hnot (H.subtype_injective.isOfFinOrder_iff.mp hfin))

/-- Every actual infinite-order disc-developed curve has the true endpoint
alternative: one parabolic frontier endpoint in both directions, or two distinct
hyperbolic frontier endpoints. -/
theorem unitDisc_equivariantPathExtension_endpoint_dichotomy
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H)
    (k : H) (hk : Function.Injective (fun n : ℤ => k^n))
    {x : P.domain.carrier} (γ : Path x (k • x)) :
    (_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic k.val ∧ ∃ a :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,
      (k.val : Equiv.Perm
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) a = a ∧ a ∈ frontier P.domain.carrier ∧
      Tendsto (fun t : ℝ => (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ
        t).val) atTop (𝓝 a) ∧
      Tendsto (fun t : ℝ => (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ
        t).val) atBot (𝓝 a)) ∨
    (_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic k.val ∧ ∃ A B :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, A ≠ B ∧
      (k.val : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) A = A ∧
      (k.val : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) B = B ∧
      A ∈ frontier P.domain.carrier ∧ B ∈ frontier P.domain.carrier ∧
      Tendsto (fun t : ℝ => (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ
        t).val) atTop (𝓝 A) ∧
      Tendsto (fun t : ℝ => (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ t).val) atBot (𝓝 B)) := by
  rcases unitDisc_infiniteOrder_parabolic_or_hyperbolic P k hk with hpar | hhyp
  · obtain ⟨a,ha,_hnot,hTop,hBot⟩ :=
      equivariantPathExtension_parabolic_endpoints P.domain P.discontinuous k hk γ hpar
    exact Or.inl ⟨hpar,a,ha,equivariantPathExtension_limit_mem_frontier
      P.domain P.discontinuous k hk γ a ha hTop,hTop,hBot⟩
  · obtain ⟨A,B,hAB,hA,hB,_hnotA,_hnotB,hTop,hBot⟩ :=
      equivariantPathExtension_loxodromic_endpoints P.domain P.discontinuous k hk γ hhyp.1
    exact Or.inr ⟨hhyp,A,B,hAB,hA,hB,equivariantPathExtension_limit_mem_frontier
      P.domain P.discontinuous k hk γ A hA hTop,equivariantPathExtension_limit_mem_frontier
      P.domain P.discontinuous k hk γ B hB hBot,hTop,hBot⟩


/-- The literal original disc curve becomes a genuine Jordan circle after one
parabolic endpoint is added, or a genuine injective closed interval after its
two hyperbolic endpoints are added. The stated images are the actual ambient
closures and recover precisely the original curve inside the original disc. -/
def DiscFrontierCurveCompactification {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H) (k : H) (F : ℝ →
      P.domain.carrier) : Prop :=
  let S : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := range (fun t => (F t).val)
  (_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic k.val ∧ ∃ a :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,
    (k.val : Equiv.Perm
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) a = a ∧ a ∈ frontier P.domain.carrier ∧
    ∃ J : Circle → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, Continuous J ∧ Function.Injective J ∧
      range J = closure S ∧ range J = insert a S ∧ range J ∩ P.domain.carrier = S) ∨
  (_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic k.val ∧ ∃ A B :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex, A ≠ B ∧
    (k.val : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) A = A ∧
    (k.val : Equiv.Perm _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) B = B ∧
    A ∈ frontier P.domain.carrier ∧ B ∈ frontier P.domain.carrier ∧
    ∃ ψ : Path B A, Function.Injective ψ ∧ range ψ = closure S ∧
      range ψ = insert A (insert B S) ∧ range ψ ∩ P.domain.carrier = S)

/-- The actual whole-real-curve dynamics, rather than just integer orbit
convergence, prove the genuine Jordan/crosscut compactification alternative. -/
theorem unitDisc_equivariantPathExtension_compactified_dichotomy
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H)
    (k : H) (hk : Function.Injective (fun n : ℤ => k^n))
    {x : P.domain.carrier} (γ : Path x (k • x))
    (hinj : Function.Injective (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k
      γ)) :
    DiscFrontierCurveCompactification P k (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ) := by
  let : ContinuousConstSMul H P.domain.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  let f : ℝ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := fun t => (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ t).val
  have hf : Continuous f := continuous_subtype_val.comp (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.continuous_equivariantPathExtension k γ)
  have hfi : Function.Injective f := Subtype.val_injective.comp hinj
  have hS : range f ⊆ P.domain.carrier := by
    rintro z ⟨t,rfl⟩
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k γ t).property
  rcases unitDisc_equivariantPathExtension_endpoint_dichotomy P k hk γ with
    ⟨hpar,a,ha,hfront,hTop,hBot⟩ | ⟨hhyp,A,B,hAB,hA,hB,hfrontA,hfrontB,hTop,hBot⟩
  · have hnot := infiniteOrder_fixed_not_in_discontinuous_domain P.domain P.discontinuous k hk a ha
    have hnotS : a ∉ range f := fun h => hnot (hS h)
    obtain ⟨J,hJ,hJi,hJrange⟩ := twoEndCurve_same_endpoint_exists_circle f a hf hfi hTop hBot hnotS
    have hcl : closure (range f) = insert a (range f) := by
      rw [←twoEndCurveExtension_range_eq_closure f a a hf hTop hBot,
        twoEndCurveExtension_range,insert_idem]
    left
    refine ⟨hpar,a,ha,hfront,J,hJ,hJi,?_,hJrange,?_⟩
    · exact hJrange.trans hcl.symm
    · rw [hJrange,insert_inter_of_notMem hnot,inter_eq_left.mpr hS]
  · have hnotA := infiniteOrder_fixed_not_in_discontinuous_domain P.domain P.discontinuous k hk A hA
    have hnotB := infiniteOrder_fixed_not_in_discontinuous_domain P.domain P.discontinuous k hk B hB
    have hnotSA : A ∉ range f := fun h => hnotA (hS h)
    have hnotSB : B ∉ range f := fun h => hnotB (hS h)
    let ψ := twoEndCurvePath f A B hf hTop hBot
    have hψi := twoEndCurvePath_injective f A B hf hfi hTop hBot hAB hnotSA hnotSB
    have hψrange := twoEndCurvePath_range f A B hf hTop hBot
    have hcl : closure (range f) = insert A (insert B (range f)) := by
      rw [←twoEndCurveExtension_range_eq_closure f A B hf hTop hBot,twoEndCurveExtension_range]
    right
    refine ⟨hhyp,A,B,hAB,hA,hB,hfrontA,hfrontB,ψ,hψi,?_,hψrange,?_⟩
    · exact hψrange.trans hcl.symm
    · rw [hψrange,insert_inter_of_notMem hnotA,insert_inter_of_notMem hnotB,inter_eq_left.mpr hS]

namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

/-- The original aperiodic Dirichlet development is a genuine properly embedded
equivariant line with the actual parabolic Jordan or hyperbolic crosscut closure. -/
theorem aperiodic_exists_compactified_frontier_curve (hw :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (hzero : d.endpointPeriod hw
      x = 0) :
    ∃ k : H, ∃ F : ℝ → P.domain.carrier,
      Function.Injective (fun n : ℤ => k^n) ∧ IsProperMap F ∧ IsClosedEmbedding F ∧
      F 0 = x.val ∧ (∀ t : ℝ, F (t+1) = k • F t) ∧
      range F ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) ∧
      _root_.LowDimensionalTopology.Geometry.Fuchsian.DiscFrontierCurveCompactification P k F := by
  obtain ⟨L,_hL,k,γ,hk,_hγ,_hγrange,hproper,hembed,_hrange,hfront⟩ :=
    d.aperiodic_exists_proper_embedded_frontier_curve hw x hzero
  refine ⟨k,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension k
    γ,hk,hproper,hembed,?_,
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_add_one k γ,hfront,?_⟩
  · simpa only [Int.cast_zero,zpow_zero,one_smul] using _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.equivariantPathExtension_int k γ 0
  · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_equivariantPathExtension_compactified_dichotomy P k hk γ hembed.injective

end RegularDirichletCircleData

/-- The original finite-generation hypotheses give the actual complete
circle/parabolic-Jordan/hyperbolic-crosscut frontier-curve alternative on
cofinally large original regular circles. Global separation and the eventual
finite-sided polygon conclusion are not hypotheses or conclusions of this lemma. -/
theorem finitelyGenerated_compactified_frontier_curve_dichotomy
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (hFG :
      H.FG)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (w : P.domain.carrier)
    (hw : IsDirichletCenter P w) (R₀ : ℝ) :
    ∃ d : RegularDirichletCircleData P w, R₀ < d.radius ∧
      ∀ x : dirichletCircleCuts P w d.radius,
        (∃ J : Circle → P.domain.carrier, Continuous J ∧ Function.Injective J ∧
          x.val ∈ range J ∧ range J ⊆ frontier (fuchsianOrbitBallUnion P w d.radius)) ∨
        (∃ k : H, ∃ F : ℝ → P.domain.carrier,
          Function.Injective (fun n : ℤ => k^n) ∧ IsProperMap F ∧ IsClosedEmbedding F ∧
          F 0 = x.val ∧ (∀ t : ℝ, F (t+1) = k • F t) ∧
          range F ⊆ frontier (fuchsianOrbitBallUnion P w d.radius) ∧
          DiscFrontierCurveCompactification P k F) := by
  obtain ⟨g,hg,hlox⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.nonElementary_exists_loxodromic H hNE
  have hgne : (⟨g,hg⟩:H) ≠ 1 := fun h => hlox.1 (congrArg Subtype.val h)
  obtain ⟨d,hd⟩ := finitelyGenerated_regular_dirichlet_circle_data P hFG w hw ⟨g,hg⟩ hgne R₀
  refine ⟨d,hd,?_⟩
  intro x
  by_cases hzero : d.endpointPeriod hw x = 0
  · exact Or.inr (d.aperiodic_exists_compactified_frontier_curve hw x hzero)
  · left
    have hpos : 0 < d.endpointPeriod hw x := Nat.pos_of_ne_zero hzero
    obtain ⟨J,hJ,hJinj,hJrange,hfront⟩ := d.finite_period_exists_jordan_curve hw x hpos
    refine ⟨J,hJ,hJinj,?_,hfront⟩
    rw [hJrange]
    have hx : x.val ∈ range (d.developedPath hw x 0) :=
      ⟨0,(d.developedPath hw x 0).source⟩
    rw [(d.developedPath_spec hw x 0).2] at hx
    exact mem_iUnion₂.mpr ⟨0,hpos,hx⟩

end LowDimensionalTopology.Geometry.Fuchsian
