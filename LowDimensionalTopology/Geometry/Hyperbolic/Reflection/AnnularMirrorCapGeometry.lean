module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.GeodesicReflections

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Hyperbolic

private theorem halfPlane_radius_pos (c : ℝ) (z : ℍ) :
    0 < ‖(z : ℂ) - (c : ℂ)‖ := by
  apply norm_pos_iff.mpr
  intro he
  have hi := congrArg Complex.im (sub_eq_zero.mp he)
  exact z.im_ne_zero (by simpa only [UpperHalfPlane.coe_im, Complex.ofReal_im] using hi)

/-- The literal native circle reflection has the exact inverted radius. -/
theorem circle_reflection_radius (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    ‖((HalfPlaneLine.circle c r hr).reflection z : ℂ) - (c : ℂ)‖ =
      r ^ 2 / ‖(z : ℂ) - (c : ℂ)‖ := by
  have hden : ‖conj (z : ℂ) - (c : ℂ)‖ = ‖(z : ℂ) - (c : ℂ)‖ := by
    calc
      _ = ‖conj ((z : ℂ) - (c : ℂ))‖ := by rw [map_sub, Complex.conj_ofReal]
      _ = _ := Complex.norm_conj _
  change ‖(circleReflection c r hr z : ℂ) - (c : ℂ)‖ = _
  rw [circleReflection_coe, add_sub_cancel_left, norm_div, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hden]

/-- Closed inside and closed outside are swapped, retaining the circle. -/
theorem circle_reflection_radius_le_iff (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    ‖((HalfPlaneLine.circle c r hr).reflection z : ℂ) - (c : ℂ)‖ ≤ r ↔
      r ≤ ‖(z : ℂ) - (c : ℂ)‖ := by
  rw [circle_reflection_radius, div_le_iff₀ (halfPlane_radius_pos c z), pow_two]
  exact mul_le_mul_iff_right₀ hr

/-- Strict outside is carried into strict inside by the actual reflection. -/
theorem circle_reflection_radius_lt_iff (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    ‖((HalfPlaneLine.circle c r hr).reflection z : ℂ) - (c : ℂ)‖ < r ↔
      r < ‖(z : ℂ) - (c : ℂ)‖ := by
  rw [circle_reflection_radius, div_lt_iff₀ (halfPlane_radius_pos c z), pow_two]
  exact mul_lt_mul_iff_right₀ hr

/-- Unit-mirror reflection inverts the actual half-plane point norm. -/
theorem unitCircle_reflection_norm (z : ℍ) :
    ‖((HalfPlaneLine.circle 0 1 zero_lt_one).reflection z : ℂ)‖ = ‖(z : ℂ)‖⁻¹ := by
  simpa only [Complex.ofReal_zero, sub_zero, one_pow, one_div] using
    circle_reflection_radius 0 1 zero_lt_one z

/-- The first reflected closed Schottky cap is exactly its radius-inverse cap. -/
theorem unitCircle_reflection_image_closed_outer (E : ℝ) (hE : 0 < E) :
    (HalfPlaneLine.circle 0 1 zero_lt_one).reflection ''
        {z : ℍ | E ≤ ‖(z : ℂ)‖} = {z : ℍ | ‖(z : ℂ)‖ ≤ E⁻¹} := by
  let s := (HalfPlaneLine.circle 0 1 zero_lt_one).reflection
  have hnorm (z : ℍ) : ‖(s z : ℂ)‖ = ‖(z : ℂ)‖⁻¹ := unitCircle_reflection_norm z
  have hpos (z : ℍ) : 0 < ‖(z : ℂ)‖ := by
    simpa only [Complex.ofReal_zero, sub_zero] using halfPlane_radius_pos 0 z
  have hmem (z : ℍ) : ‖(s z : ℂ)‖ ≤ E⁻¹ ↔ E ≤ ‖(z : ℂ)‖ := by
    rw [hnorm]
    exact inv_le_inv₀ (hpos z) hE
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hmem z).mpr hz
  · intro hy
    refine ⟨s y, ?_, (HalfPlaneLine.circle 0 1 zero_lt_one).reflection_involutive y⟩
    apply (hmem (s y)).mp
    rw [show s (s y) = y from
      (HalfPlaneLine.circle 0 1 zero_lt_one).reflection_involutive y]
    exact hy

/-- Strict annular separation makes the two original full closed caps disjoint. -/
theorem annular_closed_outer_disjoint_small (E r x : ℝ) (hx : 0 ≤ x)
    (hsep : x + r < E) :
    Disjoint {z : ℍ | E ≤ ‖(z : ℂ)‖}
      {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ ≤ r} := by
  apply disjoint_left.mpr
  intro z hzE hzr
  have hzlt : ‖(z : ℂ)‖ < E := by
    calc
      _ ≤ ‖(z : ℂ) - (x : ℂ)‖ + ‖(x : ℂ)‖ := by
        simpa only [sub_add_cancel] using norm_add_le ((z : ℂ) - (x : ℂ)) (x : ℂ)
      _ ≤ r + x := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
        exact add_le_add hzr (le_refl x)
      _ < E := by simpa only [add_comm] using hsep
  exact (not_lt_of_ge hzE) hzlt

end LowDimensionalTopology.Geometry.Hyperbolic
