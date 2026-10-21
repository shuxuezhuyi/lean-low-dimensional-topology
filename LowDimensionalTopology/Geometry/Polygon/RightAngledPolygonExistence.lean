module
public import LowDimensionalTopology.Geometry.Polygon.Area.PolygonArea
/-! Genuine right-angled polygon existence, including all impossible small side counts. -/

@[expose] public section
open Set
open scoped Complex.UnitDisc Classical
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- The original all-right angle budget is equivalent to at least five sides. -/
theorem rightAngledPolygon_angle_budget_iff (n : ℕ) :
    (∑ _i : Fin n,Real.pi/2) < ((n : ℝ)-2)*Real.pi ↔ 5 ≤ n := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  constructor
  · intro h
    have hn : (4 : ℝ) < n := by nlinarith only [h,Real.pi_pos]
    exact_mod_cast (show 4 < n by exact_mod_cast hn)
  · intro h
    have hn : (5 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith only [hn,Real.pi_pos]

/-- A genuine right-angled native Jordan polygon exists exactly from five sides onward. -/
theorem exists_rightAngledDiscPolygon_iff (n : ℕ) :
    (∃ P : DiscPolygon n,∀ i,P.angle i=Real.pi/2) ↔ 5 ≤ n := by
  rw [exists_discPolygon_angles_iff (fun _ : Fin n => Real.pi/2)
    (by intro i; exact ⟨by positivity,by linarith [Real.pi_pos]⟩)]
  exact rightAngledPolygon_angle_budget_iff n

/-- The right-angled realization may be chosen genuinely convex. -/
theorem exists_convexRightAngledDiscPolygon_iff (n : ℕ) :
    (∃ P : DiscPolygon n,P.IsConvex ∧ ∀ i,P.angle i=Real.pi/2) ↔ 5 ≤ n := by
  rw [exists_convexDiscPolygon_angles_iff (fun _ : Fin n => Real.pi/2)
    (by intro i; exact ⟨by positivity,by linarith [Real.pi_pos]⟩)]
  exact rightAngledPolygon_angle_budget_iff n

/-- Every possible side count also has a genuine all-right polygon with an inscribed hyperbolic circle. -/
theorem exists_tangentialRightAngledDiscPolygon_iff (n : ℕ) :
    (∃ P : DiscPolygon n,P.IsConvex ∧ (∀ i,P.angle i=Real.pi/2) ∧ ∃ d,P.HasIncircleAt 0 d) ↔
      5 ≤ n := by
  rw [exists_tangentialDiscPolygon_angles_iff (fun _ : Fin n => Real.pi/2)
    (by intro i; exact ⟨by positivity,by linarith [Real.pi_pos]⟩)]
  exact rightAngledPolygon_angle_budget_iff n

end
end LowDimensionalTopology.Geometry.Polygon
