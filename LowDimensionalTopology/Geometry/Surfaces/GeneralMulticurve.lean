/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.AdmissibleReduction
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicTraceUniqueness

/-!
# Arbitrary multicurves on the original surface

A family consists of actual embedded essential circles. It can be empty or
infinite. Distinct circles have disjoint geometric images and distinct
unoriented free homotopy classes. A geodesic family additionally has genuine
original-surface closed geodesic images. No existence, finiteness, maximality,
decomposition or collar theorem is part of either predicate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

universe u
variable {X : Type u} [TopologicalSpace X]

/-- An arbitrary disjoint family of essential simple closed curves, with
distinct unoriented free homotopy classes. -/
def IsMulticurve (C : Set (EssentialSimpleCircle X)) : Prop :=
  C.PairwiseDisjoint (fun c => Set.range c.val) ∧
    Set.InjOn (fun c : EssentialSimpleCircle X => c.freeClass) C

/-- Forgetting finiteness and nonemptiness preserves the actual curve family. -/
theorem AdmissibleMulticurve.isMulticurve (C : AdmissibleMulticurve X) :
    IsMulticurve (C.curves : Set (EssentialSimpleCircle X)) :=
  ⟨C.disjoint, C.classes_injective⟩

/-- An arbitrary subfamily is again a multicurve on the same carrier. -/
theorem IsMulticurve.mono {C D : Set (EssentialSimpleCircle X)}
    (hC : IsMulticurve C) (hDC : D ⊆ C) : IsMulticurve D := by
  constructor
  · intro c hc d hd hcd
    exact hC.1 (hDC hc) (hDC hd) hcd
  · intro c hc d hd heq
    exact hC.2 (hDC hc) (hDC hd) heq

/-- Different members are not freely homotopic in either orientation. -/
theorem IsMulticurve.not_homotopic_or_reverse
    {C : Set (EssentialSimpleCircle X)} (hC : IsMulticurve C)
    {c d : EssentialSimpleCircle X} (hc : c ∈ C) (hd : d ∈ C) (hcd : c ≠ d) :
    ¬ (c.val.Homotopic d.val ∨ c.val.Homotopic (d.val.comp circleReversal)) := by
  intro h
  exact hcd (hC.2 hc hd ((EssentialSimpleCircle.freeClass_eq_iff c d).mpr h))

/-- Every geometric circle in the arbitrary family is the actual image of
a closed geodesic for the given original hyperbolic metric. -/
def IsGeodesicMulticurve {R : RiemannSurface X} (M : HyperbolicSurfaceModel R)
    (C : Set (EssentialSimpleCircle X)) : Prop :=
  IsMulticurve C ∧ ∀ c ∈ C, ∃ q : OriginalClosedGeodesic M,
    Set.range q.curve = Set.range c.val

/-- The geodesic condition adds data without changing the multicurve. -/
theorem IsGeodesicMulticurve.toMulticurve
    {R : RiemannSurface X} {M : HyperbolicSurfaceModel R}
    {C : Set (EssentialSimpleCircle X)} (hC : IsGeodesicMulticurve M C) :
    IsMulticurve C :=
  hC.1

end LowDimensionalTopology.Geometry.Surfaces
