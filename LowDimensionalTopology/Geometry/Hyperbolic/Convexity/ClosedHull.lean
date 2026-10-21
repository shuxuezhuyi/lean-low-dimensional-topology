module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Klein.Closed

/-!
# Closed-disc hyperbolic convex hulls.

The hyperbolic convex hull in the closed disc is characterized by containment in convex
sets. Klein coordinates identify it with the ordinary real convex hull.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Module
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The intrinsic convex hull uses the actual compactified geodesic segments. -/
def closedDiscHConvexHull (S : Set 𝕔𝔻) : Set 𝕔𝔻 :=
  {p | ∀ U : Set 𝕔𝔻, ClosedDiscHConvex U → S ⊆ U → p ∈ U}

theorem subset_closedDiscHConvexHull (S : Set 𝕔𝔻) : S ⊆ closedDiscHConvexHull S :=
  fun _ hp _ _ hU => hU hp

theorem closedDiscHConvexHull_min {S U : Set 𝕔𝔻} (hU : ClosedDiscHConvex U) (hSU : S ⊆ U) :
    closedDiscHConvexHull S ⊆ U := fun _ hp => hp U hU hSU

theorem closedDiscHConvexHull_convex (S : Set 𝕔𝔻) : ClosedDiscHConvex (closedDiscHConvexHull S) := by
  intro p hp q hq x hx U hU hSU
  exact hU p (hp U hU hSU) q (hq U hU hSU) hx

theorem closedDiscHConvexHull_klein_image (S : Set 𝕔𝔻) :
    closedKleinCoordinate '' closedDiscHConvexHull S = convexHull ℝ (closedKleinCoordinate '' S) := by
  have hball : convexHull ℝ (closedKleinCoordinate '' S) ⊆ Metric.closedBall (0 : ℂ) 1 := by
    apply convexHull_min _ (convex_closedBall _ _)
    intro x hx
    obtain ⟨p,_,rfl⟩ := hx
    simpa only [Metric.mem_closedBall, dist_zero_right, closedKleinCoordinate] using
      (closedPoincareToKlein p).norm_le_one
  have him : closedKleinCoordinate ''
      (closedKleinCoordinate ⁻¹' convexHull ℝ (closedKleinCoordinate '' S)) =
        convexHull ℝ (closedKleinCoordinate '' S) := by
    apply image_preimage_eq_of_subset
    rw [range_closedKleinCoordinate]
    exact hball
  apply subset_antisymm
  · apply image_subset_iff.mpr
    apply closedDiscHConvexHull_min
    · apply (closedDiscHConvex_iff_klein_convex _).mpr
      rw [him]
      exact convex_convexHull ℝ _
    · intro p hp
      exact subset_convexHull ℝ _ (mem_image_of_mem closedKleinCoordinate hp)
  · apply convexHull_min (image_mono (subset_closedDiscHConvexHull S))
    exact (closedDiscHConvex_iff_klein_convex _).mp (closedDiscHConvexHull_convex S)

end LowDimensionalTopology.Geometry.Hyperbolic
