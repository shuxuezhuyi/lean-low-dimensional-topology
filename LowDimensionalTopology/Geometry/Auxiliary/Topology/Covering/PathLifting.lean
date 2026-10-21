module
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Covering.Deck

/-!
# Path lifting for covering maps

Covering maps have unique continuous path lifts with a prescribed initial point. This module
records the resulting endpoint and deck-transformation properties, including the closed-lift
property of nullhomotopic loops and the group element determined by a quotient-covering loop.

`IsSmoothUnlimitedCovering` packages local homeomorphy and unique continuous path lifting.
Its name is retained for API compatibility; the condition is purely topological and assumes no
smooth or differentiable structure. Every Mathlib `IsCoveringMap` satisfies this condition.

For example, `covering_nullhomotopic_any_lift_closed` applies to an arbitrary continuous lift,
so an endpoint computation does not require replacing that lift by `IsCoveringMap.liftPath`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped unitInterval

namespace LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- Local homeomorphy together with unique continuous unit-interval path lifting from any chosen
initial point. Despite the name, this property assumes no smooth or differentiable structure. -/
def IsSmoothUnlimitedCovering {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    (p : Y → X) : Prop :=
  IsLocalHomeomorph p ∧ ∀ (γ : C(I, X)) (y : Y), γ 0 = p y →
    ∃! Γ : C(I, Y), p ∘ Γ = γ ∧ Γ 0 = y

/-- A covering map lifts each continuous path uniquely after its initial point is prescribed. -/
theorem covering_path_lift_existsUnique {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    {p : Y → X} (hp : IsCoveringMap p) (γ : C(I, X)) (y : Y) (h0 : γ 0 = p y) :
    ∃! Γ : C(I, Y), p ∘ Γ = γ ∧ Γ 0 = y := by
  refine ⟨hp.liftPath γ y h0, ⟨hp.liftPath_lifts γ y h0, hp.liftPath_zero γ y h0⟩, ?_⟩
  intro Γ hΓ
  exact (hp.eq_liftPath_iff' h0).mpr hΓ

/-- A covering map is a local homeomorphism and has unique continuous path lifting. -/
theorem covering_isSmoothUnlimited {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    {p : Y → X} (hp : IsCoveringMap p) : IsSmoothUnlimitedCovering p :=
  ⟨hp.isLocalHomeomorph, covering_path_lift_existsUnique hp⟩

/-- A path from a point to a group translate projects to a closed path in the base. -/
def quotientCoveringProjectedLoop {Y X G : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    [Group G] [MulAction G Y] {p : Y → X} (hp : IsQuotientCoveringMap p G)
    (y : Y) (g : G) (Γ : Path y (g • y)) : Path (p y) (p y) :=
  (Γ.map hp.continuous).cast rfl (hp.map_smul g).symm

/-- The lift of a quotient-covering loop ends at exactly one translate of its initial point. -/
theorem quotientCovering_closed_loop_lift_endpoint {Y X G : Type*}
    [TopologicalSpace Y] [TopologicalSpace X] [Group G] [MulAction G Y] {p : Y → X}
    (hp : IsQuotientCoveringMap p G) (y : Y) (γ : Path (p y) (p y)) :
    ∃! g : G, hp.isCoveringMap.liftPath γ y γ.source 1 = g • y := by
  let Γ := hp.isCoveringMap.liftPath γ y γ.source
  have hproj : p (Γ 1) = p y :=
    (congrFun (hp.isCoveringMap.liftPath_lifts γ y γ.source) 1).trans γ.target
  obtain ⟨g, hg⟩ := hp.apply_eq_iff_mem_orbit.mp hproj
  let := hp.isCancelSMul
  refine ⟨g, hg.symm, ?_⟩
  intro g' hg'
  exact IsCancelSMul.right_cancel g' g y (hg'.symm.trans hg.symm)

/-- The lift of a nullhomotopic loop returns to its prescribed initial point. -/
theorem covering_nullhomotopic_loop_lift_closed {Y X : Type*}
    [TopologicalSpace Y] [TopologicalSpace X] {p : Y → X} (hp : IsCoveringMap p)
    (y : Y) (γ : Path (p y) (p y)) (hγ : γ.Homotopic (Path.refl (p y))) :
    hp.liftPath γ y γ.source 1 = y := by
  have heq := hp.liftPath_apply_one_eq_of_homotopicRel hγ y γ.source (by rfl)
  change hp.liftPath γ y γ.source 1 = hp.liftPath (.const I (p y)) y rfl 1 at heq
  rw [hp.liftPath_const rfl] at heq
  exact heq

/-- Every continuous lift of a nullhomotopic loop is closed. -/
theorem covering_nullhomotopic_any_lift_closed {Y X : Type*}
    [TopologicalSpace Y] [TopologicalSpace X] {p : Y → X} (hp : IsCoveringMap p)
    (y : Y) (γ : Path (p y) (p y)) (hγ : γ.Homotopic (Path.refl (p y)))
    (Γ : C(I, Y)) (hΓ : p ∘ Γ = γ) (hΓ0 : Γ 0 = y) : Γ 1 = y := by
  rw [(hp.eq_liftPath_iff' γ.source).mpr ⟨hΓ, hΓ0⟩]
  exact covering_nullhomotopic_loop_lift_closed hp y γ hγ

/-- The group element represented by a nullhomotopic quotient loop is the identity. -/
theorem quotientCovering_nullhomotopic_endpoint_eq_one {Y X G : Type*}
    [TopologicalSpace Y] [TopologicalSpace X] [Group G] [MulAction G Y] {p : Y → X}
    (hp : IsQuotientCoveringMap p G) (y : Y) (γ : Path (p y) (p y))
    (hγ : γ.Homotopic (Path.refl (p y))) (Γ : C(I, Y)) (hΓ : p ∘ Γ = γ)
    (hΓ0 : Γ 0 = y) (g : G) (hΓ1 : Γ 1 = g • y) : g = 1 := by
  have hc := covering_nullhomotopic_any_lift_closed hp.isCoveringMap y γ hγ Γ hΓ hΓ0
  let := hp.isCancelSMul
  apply IsCancelSMul.right_cancel g 1 y
  simpa only [one_smul] using hΓ1.symm.trans hc

/-- A deck transformation fixing a point of a preconnected covering space is the identity. -/
theorem covering_deck_fixedPoint_eq_one {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X]
    [PreconnectedSpace Y] {p : Y → X} (hp : IsCoveringMap p) (h : deck p) (y : Y)
    (hy : h • y = y) : h = 1 := by
  have he : ((h.val : Y ≃ₜ Y) : Y → Y) = id :=
    hp.eq_of_comp_eq h.val.continuous continuous_id h.property y hy
  apply Subtype.ext
  exact Homeomorph.ext (fun z => congrFun he z)

end LowDimensionalTopology.Geometry.Auxiliary.Topology
end
