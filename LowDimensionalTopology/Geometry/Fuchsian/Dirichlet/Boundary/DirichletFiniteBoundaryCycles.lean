module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletBoundaryDevelopment
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped unitInterval
namespace LowDimensionalTopology.Geometry.Fuchsian
local instance closedPathUnitPeriodPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

/-- Two genuinely injective arcs meeting precisely at their two endpoints give
an actual closed path which is injective before its terminal parameter. -/
theorem path_trans_injOn_Iio_of_two_endpoints {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : Path x y) (δ : Path y x) (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hint : range γ ∩ range δ = {x,y}) : Set.InjOn (γ.trans δ) (Iio (1:I)) := by
  have hcross (u v : I) (he : γ u = δ v) : (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
    have hm : γ u ∈ range γ ∩ range δ := ⟨mem_range_self u,he.symm ▸ mem_range_self v⟩
    have hval : γ u ∈ ({x,y}:Set X) := by rwa [hint] at hm
    rcases mem_insert_iff.mp hval with hx | hy
    · exact Or.inl ⟨hγ (hx.trans γ.source.symm),hδ (he.symm.trans (hx.trans δ.target.symm))⟩
    · have hy' : γ u = y := mem_singleton_iff.mp hy
      exact Or.inr ⟨hγ (hy'.trans γ.target.symm),hδ (he.symm.trans (hy'.trans δ.source.symm))⟩
  intro s hs t ht he
  change (s:ℝ) < 1 at hs
  change (t:ℝ) < 1 at ht
  simp only [Path.trans_apply] at he
  split_ifs at he with hsHalf htHalf htHalf
  · apply Subtype.ext
    have hh := congrArg Subtype.val (hγ he)
    change 2*(s:ℝ) = 2*(t:ℝ) at hh
    linarith
  · rcases hcross _ _ he with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · have hv' := congrArg Subtype.val hv
      change 2*(t:ℝ)-1 = 1 at hv'
      linarith
    · have hu' := congrArg Subtype.val hu
      have hv' := congrArg Subtype.val hv
      change 2*(s:ℝ) = 1 at hu'
      change 2*(t:ℝ)-1 = 0 at hv'
      apply Subtype.ext
      linarith
  · rcases hcross _ _ he.symm with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · have hv' := congrArg Subtype.val hv
      change 2*(s:ℝ)-1 = 1 at hv'
      linarith
    · have hu' := congrArg Subtype.val hu
      have hv' := congrArg Subtype.val hv
      change 2*(t:ℝ) = 1 at hu'
      change 2*(s:ℝ)-1 = 0 at hv'
      apply Subtype.ext
      linarith
  · apply Subtype.ext
    have hh := congrArg Subtype.val (hδ he)
    change 2*(s:ℝ)-1 = 2*(t:ℝ)-1 at hh
    linarith

/-- The genuine map from the actual real unit circle induced by an actual closed path. -/
def closedPathCircleMap {X : Type*} [TopologicalSpace X] {x : X} (γ : Path x x) : AddCircle (1:ℝ) → X :=
  AddCircle.liftIco 1 0 γ.extend

theorem continuous_closedPathCircleMap {X : Type*} [TopologicalSpace X] {x : X} (γ : Path x x) :
    Continuous (closedPathCircleMap γ) := by
  apply AddCircle.liftIco_zero_continuous
  · rw [Path.extend_zero,Path.extend_one]
  · exact γ.continuous_extend.continuousOn

theorem closedPathCircleMap_injective {X : Type*} [TopologicalSpace X] {x : X}
    (γ : Path x x) (hinj : Set.InjOn γ (Iio (1:I))) : Function.Injective (closedPathCircleMap γ) := by
  intro a b he
  let u := AddCircle.equivIco (1:ℝ) 0 a
  let v := AddCircle.equivIco (1:ℝ) 0 b
  have hu : 0 ≤ u.val ∧ u.val < 1 := by simpa only [zero_add,mem_Ico] using u.property
  have hv : 0 ≤ v.val ∧ v.val < 1 := by simpa only [zero_add,mem_Ico] using v.property
  let ui : I := ⟨u.val,hu.1,hu.2.le⟩
  let vi : I := ⟨v.val,hv.1,hv.2.le⟩
  change γ.extend u.val = γ.extend v.val at he
  have he' : γ ui = γ vi := by
    rw [γ.extend_apply ui.property,γ.extend_apply vi.property] at he
    exact he
  have hui : ui ∈ Iio (1:I) := hu.2
  have hvi : vi ∈ Iio (1:I) := hv.2
  have huv : u.val = v.val := congrArg (fun t : I => (t:ℝ)) (hinj hui hvi he')
  have hua : (u.val : AddCircle (1:ℝ)) = a := AddCircle.coe_equivIco
  have hvb : (v.val : AddCircle (1:ℝ)) = b := AddCircle.coe_equivIco
  exact hua.symm.trans ((congrArg (fun t : ℝ => (t:AddCircle (1:ℝ))) huv).trans hvb)

/-- The genuine circle map has exactly the image of the original closed path. -/
theorem closedPathCircleMap_range {X : Type*} [TopologicalSpace X] {x : X} (γ : Path x x) :
    range (closedPathCircleMap γ) = range γ := by
  apply subset_antisymm
  · rintro z ⟨a,rfl⟩
    let u := AddCircle.equivIco (1:ℝ) 0 a
    have hu : 0 ≤ u.val ∧ u.val < 1 := by simpa only [zero_add,mem_Ico] using u.property
    let ui : I := ⟨u.val,hu.1,hu.2.le⟩
    refine ⟨ui,?_⟩
    change γ ui = γ.extend u.val
    exact (γ.extend_extends' ui).symm
  · rintro z ⟨u,rfl⟩
    by_cases hu : (u:ℝ) < 1
    · refine ⟨((u:ℝ):AddCircle (1:ℝ)),?_⟩
      change AddCircle.liftIco (1:ℝ) 0 γ.extend ((u:ℝ):AddCircle (1:ℝ)) = γ u
      rw [AddCircle.liftIco_zero_coe_apply ⟨u.property.1,hu⟩,γ.extend_extends']
    · have huone : u = 1 := Subtype.ext (by have h := u.property.2; change (u:ℝ) = 1; linarith)
      subst u
      refine ⟨((0:ℝ):AddCircle (1:ℝ)),?_⟩
      change AddCircle.liftIco (1:ℝ) 0 γ.extend ((0:ℝ):AddCircle (1:ℝ)) = γ 1
      rw [AddCircle.liftIco_zero_coe_apply ⟨le_rfl,zero_lt_one⟩,γ.extend_zero,γ.target]

/-- A genuinely simple closed path gives a genuine closed embedding of the actual circle. -/
theorem closedPathCircleMap_isClosedEmbedding {X : Type*} [TopologicalSpace X] [T2Space X] {x : X}
    (γ : Path x x) (hinj : Set.InjOn γ (Iio (1:I))) :
    Topology.IsClosedEmbedding (closedPathCircleMap γ) :=
  (continuous_closedPathCircleMap γ).isClosedEmbedding (closedPathCircleMap_injective γ hinj)

/-- The same actual closed curve parametrized by the genuine complex unit circle. -/
def closedPathUnitCircleMap {X : Type*} [TopologicalSpace X] {x : X} (γ : Path x x) : Circle → X :=
  closedPathCircleMap γ ∘ (AddCircle.homeomorphCircle (T := (1:ℝ)) one_ne_zero).symm

/-- The actual unit-circle parametrization is continuous and injective, with its
exact original closed-path image. This is the genuine Jordan-curve parametrization. -/
theorem closedPathUnitCircleMap_spec {X : Type*} [TopologicalSpace X] {x : X}
    (γ : Path x x) (hinj : Set.InjOn γ (Iio (1:I))) :
    Continuous (closedPathUnitCircleMap γ) ∧ Function.Injective (closedPathUnitCircleMap γ) ∧
      range (closedPathUnitCircleMap γ) = range γ := by
  let e := AddCircle.homeomorphCircle (T := (1:ℝ)) one_ne_zero
  refine ⟨(continuous_closedPathCircleMap γ).comp e.symm.continuous,
    (closedPathCircleMap_injective γ hinj).comp e.symm.injective,?_⟩
  change range (closedPathCircleMap γ ∘ e.symm) = _
  rw [range_comp,e.symm.surjective.range_eq,image_univ,closedPathCircleMap_range]

open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

/-- The actual canonical first return brings the full original tile-and-cut state back. -/
theorem endpointPeriod_return (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    d.state hw x (d.endpointPeriod hw x) = d.state hw x 0 := by
  simpa only [state,endpointPeriod,Equiv.Perm.coe_pow,pow_zero,Equiv.Perm.one_apply] using
    Function.iterate_minimalPeriod (f := (d.endpointStep hw : _ → _)) (x := (1,x))

/-- A genuine original arc has distinct actual initial and terminal developed states. -/
theorem state_zero_ne_one (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    d.state hw x 0 ≠ d.state hw x 1 := by
  intro he
  have hv := (d.vertex_eq_iff_state_eq hw x 0 1).mpr he
  rw [d.vertex_next hw x 0] at hv
  change (1:H) • x.val = (1:H) • (d.arcReversal hw x).val at hv
  simp only [one_smul] at hv
  exact d.arcReversal_ne_self hw x (Subtype.ext hv.symm)

/-- A genuine finite developed cycle has at least two actual constituent arcs. -/
theorem endpointPeriod_ne_one (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    d.endpointPeriod hw x ≠ 1 := by
  intro he
  have hh := d.endpointPeriod_return hw x
  rw [he] at hh
  exact d.state_zero_ne_one hw x hh.symm

/-- The genuine developed vertex returns to the literal original starting point. -/
theorem vertex_endpointPeriod (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w) (x :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    d.vertex hw x (d.endpointPeriod hw x) = x.val := by
  have he := (d.vertex_eq_iff_state_eq hw x (d.endpointPeriod hw x) 0).mpr (d.endpointPeriod_return hw x)
  exact he.trans (by simp only [vertex,state,pow_zero,Equiv.Perm.one_apply,one_smul])

end RegularDirichletCircleData
namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

/-- A genuine positive full-state return closes the actual finite original chain
into two actual injective paths meeting exactly in their two common endpoints. -/
theorem finite_period_two_arc_loop (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (hpos : 0 < d.endpointPeriod
      hw x) :
    ∃ y : P.domain.carrier, ∃ γ : Path x.val y, ∃ δ : Path y x.val,
      Function.Injective γ ∧ Function.Injective δ ∧ range γ ∩ range δ = {x.val,y} ∧
      range (γ.trans δ) = ⋃ i ∈ Iio (d.endpointPeriod hw x), d.developedClosedArc hw x i ∧
      range (γ.trans δ) ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) := by
  let T := d.endpointPeriod hw x
  have hTtwo : 2 ≤ T := by
    have hh := d.endpointPeriod_ne_one hw x
    change T ≠ 1 at hh
    change 0 < T at hpos
    omega
  let N := T-2
  have hNT : N+2 = T := by dsimp only [N]; omega
  have hNP : N+1 < d.endpointPeriod hw x := by change N+1 < T; omega
  obtain ⟨γ,hγi,hγrange,hγF⟩ := d.exists_injective_developed_path_lt_period hw x N hNP
  let y := d.vertex hw x (N+1)
  have hEnd : d.vertex hw x (N+2) = x.val := by rw [hNT]; exact d.vertex_endpointPeriod hw x
  let δ : Path y x.val := (d.developedPath hw x (N+1)).cast rfl hEnd.symm
  have hδi : Function.Injective δ := (d.developedPath_spec hw x (N+1)).1
  have hδrange : range δ = d.developedClosedArc hw x (N+1) := (d.developedPath_spec hw x (N+1)).2
  have hδF : range δ ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) :=
    hδrange ▸ d.developedClosedArc_subset_frontier hw x (N+1)
  have hInt : range γ ∩ range δ = {x.val,y} := by
    apply subset_antisymm
    · rintro p ⟨hpγ,hpδ⟩
      rw [hγrange] at hpγ
      obtain ⟨i,hpi⟩ := mem_iUnion.mp hpγ
      obtain ⟨hi,hpi⟩ := mem_iUnion.mp hpi
      have hiN : i ≤ N := mem_Iic.mp hi
      have hne : d.state hw x i ≠ d.state hw x (N+1) := by
        intro he
        have hij := d.state_injOn_before_period hw x (show i < d.endpointPeriod hw x by change i < T; omega) hNP he
        omega
      have hpBoth : p ∈ d.developedClosedArc hw x i ∩ d.developedClosedArc hw x (N+1) :=
        ⟨hpi,hδrange ▸ hpδ⟩
      have hpEnds := (_root_.LowDimensionalTopology.Geometry.Fuchsian.compact_arcs_inter_subset_endpoints
        (d.developedClosedArc_endpoints hw x i)
        (d.developedClosedArc_endpoints hw x (N+1)) (d.developedOpenArc_disjoint_of_state_ne hw x i (N+1) hne)
        ⟨d.vertex_not_mem_developedOpenArc hw x (N+1) i,d.vertex_not_mem_developedOpenArc hw x (N+1) (i+1)⟩
        ⟨d.vertex_not_mem_developedOpenArc hw x i (N+1),d.vertex_not_mem_developedOpenArc hw x i (N+2)⟩ hpBoth).2
      have hh : p ∈ ({y,x.val}:Set P.domain.carrier) := by simpa only [hEnd] using hpEnds
      simpa only [pair_comm] using hh
    · intro p hp
      rcases mem_insert_iff.mp hp with he | he
      · subst p
        exact ⟨⟨0,γ.source⟩,⟨1,δ.target⟩⟩
      · have he' : p = y := mem_singleton_iff.mp he
        subst p
        exact ⟨⟨1,γ.target⟩,⟨0,δ.source⟩⟩
  refine ⟨y,γ,δ,hγi,hδi,hInt,?_,?_⟩
  · rw [Path.trans_range,hγrange,hδrange]
    ext p
    simp only [mem_union,mem_iUnion,mem_Iic,mem_Iio]
    constructor
    · rintro (⟨i,hi,hpi⟩ | hpi)
      · exact ⟨i,by change i < T; omega,hpi⟩
      · exact ⟨N+1,hNP,hpi⟩
    · rintro ⟨i,hi,hpi⟩
      by_cases hin : i ≤ N
      · exact Or.inl ⟨i,hin,hpi⟩
      · have he : i = N+1 := by change i < T at hi; omega
        exact Or.inr (he ▸ hpi)
  · rw [Path.trans_range]
    exact union_subset hγF hδF

/-- Every actual finite full-state boundary cycle is a genuine Jordan curve in
the original carrier, with exactly the true finite developed arc image. -/
theorem finite_period_exists_jordan_curve (hw : _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) (hpos : 0 < d.endpointPeriod
      hw x) :
    ∃ J : Circle → P.domain.carrier, Continuous J ∧ Function.Injective J ∧
      range J = ⋃ i ∈ Iio (d.endpointPeriod hw x), d.developedClosedArc hw x i ∧
      range J ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) := by
  obtain ⟨y,γ,δ,hγi,hδi,hInt,hRange,hF⟩ := d.finite_period_two_arc_loop hw x hpos
  have hIio := _root_.LowDimensionalTopology.Geometry.Fuchsian.path_trans_injOn_Iio_of_two_endpoints γ δ hγi hδi hInt
  obtain ⟨hc,hi,hr⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.closedPathUnitCircleMap_spec (γ.trans δ) hIio
  exact ⟨_root_.LowDimensionalTopology.Geometry.Fuchsian.closedPathUnitCircleMap (γ.trans δ),hc,hi,hr.trans hRange,hr ▸
    hF⟩

end RegularDirichletCircleData
end LowDimensionalTopology.Geometry.Fuchsian
