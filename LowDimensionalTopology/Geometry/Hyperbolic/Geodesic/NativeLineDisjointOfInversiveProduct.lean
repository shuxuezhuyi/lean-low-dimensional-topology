module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicInversiveProducts
public import LowDimensionalTopology.Geometry.Inversive.InversePairs

/-!
# Strict inversive separation gives actual native hyperbolic disjointness

The existing classification excludes equality, parallelism and intersection.
The inversive product is the absolute normalized side pairing.
-/

@[expose] public section
noncomputable section
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A strict inversive product bound excludes both shared ideal ends and
shared actual half-plane points. -/
theorem HalfPlaneLine.hDisjoint_of_one_lt_inversiveProduct (L M : HalfPlaneLine)
    (hprod : 1 < Inversive.inversiveProduct
      L.extendedCircle.realModel M.extendedCircle.realModel) : L.HDisjoint M := by
  have hne : L ≠ M := by
    intro hLM
    subst M
    rw [Inversive.inversiveProduct_self] at hprod
    exact (lt_irrefl (1 : ℝ)) hprod
  rcases L.classification M hne with hp | hi | hd
  · rw [halfPlane_inversiveProduct_eq_one_of_parallel L M hp] at hprod
    exact False.elim ((lt_irrefl (1 : ℝ)) hprod)
  · obtain ⟨p, hpL, hpM⟩ := hi.2.2
    rw [halfPlane_inversiveProduct_eq_cos_acuteAngle L M p hpL hpM] at hprod
    exact False.elim ((not_lt_of_ge (Real.cos_le_one _)) hprod)
  · exact hd

/-- The same separation criterion expressed in the actual signed side
pairing; both positive and negative separated pairs are admitted. -/
theorem HalfPlaneLine.hDisjoint_of_one_lt_abs_normalPairing (L M : HalfPlaneLine)
    (hpair : 1 < |L.normalPairing M|) : L.HDisjoint M := by
  apply L.hDisjoint_of_one_lt_inversiveProduct M
  simpa only [halfPlane_inversiveProduct_eq_normal_product,
    HalfPlaneLine.normalPairing] using hpair

end LowDimensionalTopology.Geometry.Hyperbolic
