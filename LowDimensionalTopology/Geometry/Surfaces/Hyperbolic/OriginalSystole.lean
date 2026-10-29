module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedLengthSpectrum
public import Mathlib.Topology.Order.Monotone

/-!
# The systole from the actual original closed-geodesic spectrum

The systole is the shortest essential closed-geodesic length; the
infimum is not restricted to simple representatives.
The existing original geodesics are non-null-homotopic, and their actual
full-period Poincaré BV lengths retain all traversals and proper powers.
Nonemptiness is explicit below; no geodesic existence theorem is reconstructed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

universe u
variable {X : Type u} [TopologicalSpace X]

/-- The infimum of the actual essential closed-geodesic lengths on the original closed surface. -/
def originalHyperbolicSystole (R : ClosedRiemannSurface X)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) : ℝ :=
  sInf (originalClosedGeodesicLengthSpectrum M)

/-- The literal infimum is positive and is the length of an actual essential closed geodesic,
provided the actual original geodesic space is nonempty. -/
theorem ClosedRiemannSurface.originalHyperbolicSystole_pos_attained
    (R : ClosedRiemannSurface X) (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (hnonempty : Nonempty (OriginalClosedGeodesic M)) :
    0 < originalHyperbolicSystole R M ∧
      ∃ q : OriginalClosedGeodesic M, ¬ IsNullHomotopicLoop q.toLoop ∧
        q.length.toReal = originalHyperbolicSystole R M ∧
        ∀ r : OriginalClosedGeodesic M, originalHyperbolicSystole R M ≤ r.length.toReal := by
  let := R.compactSpace
  let spectrum : Set ℝ := originalClosedGeodesicLengthSpectrum M
  change 0 < sInf spectrum ∧
    ∃ q : OriginalClosedGeodesic M, ¬ IsNullHomotopicLoop q.toLoop ∧
      q.length.toReal = sInf spectrum ∧
      ∀ r : OriginalClosedGeodesic M, sInf spectrum ≤ r.length.toReal
  obtain ⟨q₀⟩ := hnonempty
  have hs : spectrum.Nonempty := ⟨q₀.length.toReal, ⟨q₀, rfl⟩⟩
  have hb : BddBelow spectrum := by
    refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact le_of_lt q.length_toReal_pos
  have hc : IsClosed spectrum := (R.originalClosedGeodesicLengthSpectrum_closed_discrete M).1
  have hleast : IsLeast spectrum (sInf spectrum) := hc.isLeast_csInf hs hb
  obtain ⟨q, hq⟩ := hleast.1
  constructor
  · rw [← hq]
    exact q.length_toReal_pos
  · refine ⟨q, q.not_isNullHomotopicLoop, hq, ?_⟩
    intro r
    exact hleast.2 ⟨r, rfl⟩

end LowDimensionalTopology.Geometry.Surfaces
