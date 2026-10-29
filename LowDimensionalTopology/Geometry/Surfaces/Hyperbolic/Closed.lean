module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Closed
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.QuotientMetric

/-!
# Closed hyperbolic surfaces

The hyperbolic structure is a genuine analytic presentation by a discontinuous
unit-disc group with no nontrivial elliptic elements. Its existing metric model
supplies intrinsic hyperbolic curve lengths and area on the original surface.
-/

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Surfaces

universe u

/-- A closed Riemann surface equipped with an actual hyperbolic quotient model. -/
structure ClosedHyperbolicSurface (X : Type u) [TopologicalSpace X]
    extends ClosedRiemannSurface X where
  model : HyperbolicSurfaceModel toClosedRiemannSurface.toRiemannSurface

namespace ClosedHyperbolicSurface

variable {X : Type u} [TopologicalSpace X]

/-- Equip a closed Riemann surface with a specified hyperbolic quotient presentation. -/
def ofModel (R : ClosedRiemannSurface X) (M : HyperbolicSurfaceModel R.toRiemannSurface) :
    ClosedHyperbolicSurface X where
  toClosedRiemannSurface := R
  model := M

@[simp]
theorem ofModel_toClosedRiemannSurface
    (R : ClosedRiemannSurface X) (M : HyperbolicSurfaceModel R.toRiemannSurface) :
    (ofModel R M).toClosedRiemannSurface = R := rfl

/-- Every closed hyperbolic surface has hyperbolic conformal type in the original API. -/
theorem isHyperbolicType (R : ClosedHyperbolicSurface X) :
    IsHyperbolicType R.toRiemannSurface :=
  (isHyperbolicType_iff_nonempty_model R.toRiemannSurface).mpr ⟨R.model⟩

/-- Choose an existing quotient model from a proved hyperbolic-type statement. -/
def ofIsHyperbolicType (R : ClosedRiemannSurface X)
    (hR : IsHyperbolicType R.toRiemannSurface) : ClosedHyperbolicSurface X :=
  ofModel R ((isHyperbolicType_iff_nonempty_model R.toRiemannSurface).mp hR).some

@[simp]
theorem ofIsHyperbolicType_toClosedRiemannSurface (R : ClosedRiemannSurface X)
    (hR : IsHyperbolicType R.toRiemannSurface) :
    (ofIsHyperbolicType R hR).toClosedRiemannSurface = R := rfl

end ClosedHyperbolicSurface

/-- On a fixed closed Riemann surface, the original hyperbolic-type predicate is
exactly existence of a closed hyperbolic structure with that complex structure. -/
theorem closedRiemannSurface_isHyperbolicType_iff
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) :
    IsHyperbolicType R.toRiemannSurface ↔
      ∃ S : ClosedHyperbolicSurface X, S.toClosedRiemannSurface = R := by
  constructor
  · intro hR
    exact ⟨ClosedHyperbolicSurface.ofIsHyperbolicType R hR, rfl⟩
  · rintro ⟨S, rfl⟩
    exact S.isHyperbolicType

/-- Existence of a closed hyperbolic surface is existence of a compact complex
structure with the already defined hyperbolic conformal type. -/
theorem nonempty_closedHyperbolicSurface_iff (X : Type u) [TopologicalSpace X] :
    Nonempty (ClosedHyperbolicSurface X) ↔
      ∃ R : ClosedRiemannSurface X, IsHyperbolicType R.toRiemannSurface := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.toClosedRiemannSurface, R.isHyperbolicType⟩
  · rintro ⟨R, hR⟩
    exact ⟨ClosedHyperbolicSurface.ofIsHyperbolicType R hR⟩

end LowDimensionalTopology.Geometry.Surfaces
