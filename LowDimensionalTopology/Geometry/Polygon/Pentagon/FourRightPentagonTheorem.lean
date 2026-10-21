/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Area.PolygonArea
public import LowDimensionalTopology.Geometry.Polygon.Pentagon.FourRightPentagonAdapters
@[expose] public section
noncomputable section
namespace LowDimensionalTopology.Geometry.Polygon

/-- The remaining angle bound follows from the actual Jordan polygon's
unconditional angle sum, including an ideal remaining vertex. -/
theorem DiscPolygon.fourRightPentagon_angle_lt_pi (P : DiscPolygon 5)
    (hR : P.IsFourRightPentagon) : P.angle 0<Real.pi := by
  have h:=P.angle_sum_lt
  have hsum : ∑i:Fin 5,P.angle i=P.angle 0+2*Real.pi:=by
    simp only [Fin.sum_univ_succ]
    change P.angle 0+(P.angle 1+(P.angle 2+(P.angle 3+(P.angle 4+0))))=P.angle 0+2*Real.pi
    rw [hR 1 (by decide),hR 2 (by decide),hR 3 (by decide),hR 4 (by decide)]
    ring
  rw [hsum] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h]

/-- Every actual four-right Jordan pentagon is convex; no convexity or
remaining-angle assumption is added. -/
theorem DiscPolygon.fourRightPentagon_isConvex (P : DiscPolygon 5)
    (hR : P.IsFourRightPentagon) : P.IsConvex := by
  apply P.isConvex_of_angles_le_pi
  intro i
  by_cases hi : i=0
  · subst i;exact (P.fourRightPentagon_angle_lt_pi hR).le
  · rw [hR i hi];linarith only [Real.pi_pos]

/--
For every actual finite-or-ideal Jordan
pentagon with the four original right angles and genuine path side lengths.
-/
theorem DiscPolygon.fourRightPentagon_cosh_identity (P : DiscPolygon 5) (hR : P.IsFourRightPentagon) :
    Real.cosh (P.sideLength 1).toReal*Real.cosh (P.sideLength 3).toReal+Real.cos (P.angle 0)=
      Real.sinh (P.sideLength 1).toReal*Real.cosh (P.sideLength 2).toReal*Real.sinh (P.sideLength 3).toReal :=
  P.fourRightPentagon_cosh_identity_of_angle_lt_pi hR (P.fourRightPentagon_angle_lt_pi hR)

end LowDimensionalTopology.Geometry.Polygon
