module

public import LowDimensionalTopology.Unproved.Surfaces.ShortGeodesicCriticalPair
public import Mathlib.Order.Bounds.Basic

/-!
# The full sharp short-geodesic cutoff, conditional on a geometric witness

The strict disjointness bound is already proved. A fixed actual intersecting
simple pair at the critical length rules out every larger universal cutoff.
-/

@[expose] public section
noncomputable section
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

/-- A universal strict cutoff for distinct simple original geodesic images,
using the actual single-traversal period maps on whole-disc-quotient surfaces. -/
def IsUniversalSimpleGeodesicCutoff (δ : ℝ) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (R : RiemannSurface X) (M : HyperbolicSurfaceModel R)
    (q r : OriginalClosedGeodesic M),
    Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X) →
    Function.Injective (r.periodic.lift : AddCircle (1 : ℝ) → X) →
    range q.curve ≠ range r.curve →
    q.length.toReal < δ → r.length.toReal < δ → Disjoint (range q.curve) (range r.curve)

/-- The strict cutoff is the largest universal one, conditional on
the independently geometric fixed critical pair. -/
theorem isGreatest_shortClosedGeodesicCutoff_of_criticalPair
    (hpair : LowDimensionalTopology.Unproved.Surfaces.ShortGeodesicCriticalPair) :
    IsGreatest {δ : ℝ | 0 < δ ∧ IsUniversalSimpleGeodesicCutoff δ} shortClosedGeodesicCutoff := by
  refine ⟨⟨shortClosedGeodesicCutoff_pos, ?_⟩, ?_⟩
  · intro X t R M q r _hq _hr hneq hq hr
    exact (q.trace_eq_or_disjoint_of_length_lt_shortCutoff r hq hr).resolve_left hneq
  · intro δ hδ
    by_contra hle
    have hgt : shortClosedGeodesicCutoff < δ := lt_of_not_ge hle
    obtain ⟨X, t, h⟩ := hpair
    let : TopologicalSpace X := t
    obtain ⟨R, M, q, r, hq, hr, hneq, hcross, hql, hrl⟩ := h
    have hqδ : q.length.toReal < δ := by
      rw [hql]
      exact hgt
    have hrδ : r.length.toReal < δ := by
      rw [hrl]
      exact hgt
    exact hcross (hδ.2 X R M q r hq hr hneq hqδ hrδ)

end LowDimensionalTopology.Geometry.Surfaces
