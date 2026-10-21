/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Quotient

/-!
# Orbit quotients

For a group action, a subset inherits the ambient orbit relation even when
it is not invariant. The quotient by that restricted relation maps naturally
to the full orbit space. This module proves injectivity, surjectivity under an
orbit-covering hypothesis, and continuity and openness of the relevant maps.
-/

public section

open Topology

universe u v

namespace LowDimensionalTopology.Geometry.DiscreteGroups.Action

variable (G : Type u) [Group G] (X : Type v) [MulAction G X]

/-- The quotient by the ambient group action. -/
abbrev orbitQuotient := Quotient (MulAction.orbitRel G X)

/-- The natural projection onto the ambient orbit space. -/
@[expose] def orbitProjection (x : X) : orbitQuotient G X :=
  Quotient.mk (MulAction.orbitRel G X) x

/-- The ambient orbit relation restricted to a subset, without an invariance assumption. -/
@[expose] def restrictedOrbitRel (D : Set X) : Setoid D :=
  (MulAction.orbitRel G X).comap Subtype.val

/-- The identified subset used for the closed-domain quotient. -/
abbrev restrictedOrbitQuotient (D : Set X) := Quotient (restrictedOrbitRel G X D)

/-- The projection onto the quotient by the restricted ambient orbit relation. -/
@[expose] def restrictedProjection (D : Set X) (x : D) : restrictedOrbitQuotient G X D :=
  Quotient.mk (restrictedOrbitRel G X D) x

/-- The comparison map sends a restricted orbit class to its full ambient orbit class. -/
@[expose] def comparisonMap (D : Set X) : restrictedOrbitQuotient G X D → orbitQuotient G X :=
  Quotient.map Subtype.val (fun _ _ h => h)

/-- The orbit-covering condition needed for surjectivity of the comparison map. -/
@[expose] def MeetsEveryOrbit (D : Set X) : Prop :=
  ∀ x : X, ∃ g : G, g • x ∈ D

/-- A covering by translates supplies the comparison map's orbit-covering hypothesis. -/
theorem meetsEveryOrbit_of_covering (D : Set X)
    (hcover : ∀ x : X, ∃ g : G, ∃ y ∈ D, g • y = x) : MeetsEveryOrbit G X D := by
  intro x
  obtain ⟨g, y, hy, hgy⟩ := hcover x
  refine ⟨g⁻¹, ?_⟩
  rw [← hgy, inv_smul_smul]
  exact hy

@[simp]
theorem orbitProjection_smul (g : G) (x : X) :
    orbitProjection G X (g • x) = orbitProjection G X x :=
  Quotient.sound ⟨g, rfl⟩

/-- The commutative-square identity used in equation. -/
@[simp]
theorem comparisonMap_restrictedProjection (D : Set X) (x : D) :
    comparisonMap G X D (restrictedProjection G X D x) = orbitProjection G X x :=
  rfl

/-- The ambient orbit projection is surjective. -/
theorem orbitProjection_surjective : Function.Surjective (orbitProjection G X) :=
  Quotient.mk_surjective

/-- The restricted projection is surjective. -/
theorem restrictedProjection_surjective (D : Set X) :
    Function.Surjective (restrictedProjection G X D) :=
  Quotient.mk_surjective

/-- The comparison map is injective for every subset. -/
theorem comparisonMap_injective (D : Set X) :
    Function.Injective (comparisonMap G X D) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y h
  change Quotient.mk (MulAction.orbitRel G X) (x : X) =
    Quotient.mk (MulAction.orbitRel G X) (y : X) at h
  exact Quotient.sound (Quotient.exact h : MulAction.orbitRel G X (x : X) (y : X))

/-- Meeting every orbit suffices for the remaining surjectivity. -/
theorem comparisonMap_surjective (D : Set X) (hD : MeetsEveryOrbit G X D) :
    Function.Surjective (comparisonMap G X D) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  obtain ⟨g, hg⟩ := hD x
  exact ⟨restrictedProjection G X D ⟨g • x, hg⟩, orbitProjection_smul G X g x⟩

/-- The comparison is a bijection once the subset meets every orbit. -/
theorem comparisonMap_bijective (D : Set X) (hD : MeetsEveryOrbit G X D) :
    Function.Bijective (comparisonMap G X D) :=
  ⟨comparisonMap_injective G X D, comparisonMap_surjective G X D hD⟩

/-- The subset inclusion is the injective map denoted by an inclusion. -/
theorem subsetInclusion_injective (D : Set X) : Function.Injective (Subtype.val : D → X) :=
  Subtype.val_injective

section Topology

variable [TopologicalSpace X]

/-- Continuity of the ambient orbit projection. -/
theorem orbitProjection_continuous : Continuous (orbitProjection G X) :=
  continuous_quot_mk

/-- Continuity of the restricted projection. -/
theorem restrictedProjection_continuous (D : Set X) :
    Continuous (restrictedProjection G X D) :=
  continuous_quot_mk

/-- Continuity of the subset inclusion. -/
theorem subsetInclusion_continuous (D : Set X) : Continuous (Subtype.val : D → X) :=
  continuous_subtype_val

/-- The comparison-map continuity in follows from quotient topology. -/
theorem comparisonMap_continuous (D : Set X) : Continuous (comparisonMap G X D) := by
  apply (Auxiliary.Topology.continuous_quotientTopology_iff_comp (restrictedProjection G X D)
    (comparisonMap G X D)).2
  exact (orbitProjection_continuous G X).comp continuous_subtype_val

/-- Openness of the ambient projection. -/
theorem orbitProjection_isOpenMap [ContinuousConstSMul G X] :
    IsOpenMap (orbitProjection G X) :=
  (MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := X)).isOpenMap

end Topology

end LowDimensionalTopology.Geometry.DiscreteGroups.Action
