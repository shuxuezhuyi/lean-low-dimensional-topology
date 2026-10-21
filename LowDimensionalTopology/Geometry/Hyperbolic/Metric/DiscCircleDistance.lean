/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PointLineDistance
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HyperbolicBalls

@[expose] public section
open Set
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The radial hyperbolic cosine for the actual density path distance in the disc. -/
theorem disc_cosh_distance_zero (z : 𝔻) :
    Real.cosh (discPathDist 0 z) = (1 + ‖(z : ℂ)‖ ^ 2) / (1 - ‖(z : ℂ)‖ ^ 2) := by
  have h := disc_cosh_distance 0 z
  simp only [Complex.UnitDisc.coe_zero, norm_zero,
    zero_pow (by omega : 2 ≠ 0), sub_zero, zero_sub, norm_neg, one_mul] at h
  rw [h]
  have hp : 0 < 1 - ‖(z : ℂ)‖ ^ 2 := sub_pos.mpr z.sq_norm_lt_one
  field_simp [hp.ne']
  ring

/-- The radial hyperbolic sine for the same actual distance. -/
theorem disc_sinh_distance_zero (z : 𝔻) :
    Real.sinh (discPathDist 0 z) = 2 * ‖(z : ℂ)‖ / (1 - ‖(z : ℂ)‖ ^ 2) := by
  have hd : 0 ≤ discPathDist 0 z := by rw [discPathDist_eq_halfPlane]; exact dist_nonneg
  have hn : 0 ≤ ‖(z : ℂ)‖ := norm_nonneg _
  have hp : 0 < 1 - ‖(z : ℂ)‖ ^ 2 := sub_pos.mpr z.sq_norm_lt_one
  apply (sq_eq_sq₀ (Real.sinh_nonneg_iff.mpr hd) (div_nonneg (by positivity) hp.le)).mp
  have h := Real.cosh_sq_sub_sinh_sq (discPathDist 0 z)
  rw [disc_cosh_distance_zero] at h
  have he : ((1 + ‖(z : ℂ)‖ ^ 2) / (1 - ‖(z : ℂ)‖ ^ 2)) ^ 2 -
      (2 * ‖(z : ℂ)‖ / (1 - ‖(z : ℂ)‖ ^ 2)) ^ 2 = 1 := by
    field_simp
    ring
  nlinarith

/-- Radial order in the disc agrees with order of the actual path distances from zero. -/
theorem disc_distance_zero_le_of_norm_le {z w : 𝔻} (hzw : ‖(z : ℂ)‖ ≤ ‖(w : ℂ)‖) :
    discPathDist 0 z ≤ discPathDist 0 w := by
  have hz : 0 < 1 - ‖(z : ℂ)‖ ^ 2 := sub_pos.mpr z.sq_norm_lt_one
  have hw : 0 < 1 - ‖(w : ℂ)‖ ^ 2 := sub_pos.mpr w.sq_norm_lt_one
  have hsq : ‖(z : ℂ)‖ ^ 2 ≤ ‖(w : ℂ)‖ ^ 2 := by
    nlinarith [norm_nonneg (z : ℂ), norm_nonneg (w : ℂ)]
  have hc : Real.cosh (discPathDist 0 z) ≤ Real.cosh (discPathDist 0 w) := by
    rw [disc_cosh_distance_zero, disc_cosh_distance_zero, div_le_div_iff₀ hz hw]
    nlinarith
  have hdz : 0 ≤ discPathDist 0 z := by rw [discPathDist_eq_halfPlane]; exact dist_nonneg
  have hdw : 0 ≤ discPathDist 0 w := by rw [discPathDist_eq_halfPlane]; exact dist_nonneg
  simpa only [abs_of_nonneg hdz, abs_of_nonneg hdw] using Real.cosh_le_cosh.mp hc

/-- The near radial intersection of a circle orthogonal to the unit circle. -/
def discCircleClosestPoint (c : ℂ) (r : ℝ) (hr : 0 < r) (hc : ‖c‖ ^ 2 = r ^ 2 + 1) : 𝔻 := by
  have hn : 0 < ‖c‖ := by nlinarith [norm_nonneg c]
  have hnr : r < ‖c‖ := by nlinarith
  have hnr1 : ‖c‖ - r < 1 := by nlinarith
  refine ⟨((‖c‖ - r) / ‖c‖ : ℝ) • c, ?_⟩
  apply mem_ball_zero_iff.mpr
  change ‖((‖c‖ - r) / ‖c‖ : ℝ) • c‖ < 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (sub_pos.mpr hnr) hn),
    div_mul_cancel₀ _ hn.ne']
  exact hnr1

theorem discCircleClosestPoint_norm (c : ℂ) (r : ℝ) (hr : 0 < r) (hc : ‖c‖ ^ 2 = r ^ 2 + 1) :
    ‖(discCircleClosestPoint c r hr hc : ℂ)‖ = ‖c‖ - r := by
  have hn : 0 < ‖c‖ := by nlinarith [norm_nonneg c]
  have hnr : r < ‖c‖ := by nlinarith
  change ‖((‖c‖ - r) / ‖c‖ : ℝ) • c‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (sub_pos.mpr hnr) hn),
    div_mul_cancel₀ _ hn.ne']

theorem discCircleClosestPoint_mem (c : ℂ) (r : ℝ) (hr : 0 < r) (hc : ‖c‖ ^ 2 = r ^ 2 + 1) :
    ‖(discCircleClosestPoint c r hr hc : ℂ) - c‖ = r := by
  have hn : 0 < ‖c‖ := by nlinarith [norm_nonneg c]
  have he : (discCircleClosestPoint c r hr hc : ℂ) - c = (-r / ‖c‖ : ℝ) • c := by
    change ((‖c‖ - r) / ‖c‖ : ℝ) • c - c = _
    calc
      ((‖c‖ - r) / ‖c‖ : ℝ) • c - c = ((‖c‖ - r) / ‖c‖ : ℝ) • c - (1 : ℝ) • c := by rw [one_smul]
      _ = (-r / ‖c‖ : ℝ) • c := by
        rw [← sub_smul]
        congr 1
        field_simp
        ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_neg (div_neg_of_neg_of_pos (neg_neg_of_pos hr) hn)]
  rw [neg_div, neg_neg, div_mul_cancel₀ _ hn.ne']

theorem discCircleClosestPoint_minimizes (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : ‖c‖ ^ 2 = r ^ 2 + 1) {z : 𝔻} (hz : ‖(z : ℂ) - c‖ = r) :
    discPathDist 0 (discCircleClosestPoint c r hr hc) ≤ discPathDist 0 z := by
  apply disc_distance_zero_le_of_norm_le
  rw [discCircleClosestPoint_norm]
  have h := norm_sub_le (z : ℂ) ((z : ℂ) - c)
  rw [sub_sub_cancel, hz] at h
  linarith

/-- The near intersection has the sine and cosine specified by. -/
theorem discCircleClosestPoint_formulas (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : ‖c‖ ^ 2 = r ^ 2 + 1) :
    Real.sinh (discPathDist 0 (discCircleClosestPoint c r hr hc)) = 1 / r ∧
      Real.cosh (discPathDist 0 (discCircleClosestPoint c r hr hc)) = ‖c‖ / r := by
  have hnr : r < ‖c‖ := by nlinarith [norm_nonneg c]
  have hk : 0 < ‖c‖ - r := sub_pos.mpr hnr
  have hden : 1 - (‖c‖ - r) ^ 2 = 2 * r * (‖c‖ - r) := by nlinarith
  have hnum : 1 + (‖c‖ - r) ^ 2 = 2 * ‖c‖ * (‖c‖ - r) := by nlinarith
  constructor
  · rw [disc_sinh_distance_zero, discCircleClosestPoint_norm, hden]
    field_simp
  · rw [disc_cosh_distance_zero, discCircleClosestPoint_norm, hnum, hden]
    field_simp

/-- For every actual nearest point on the circle arc. -/
theorem discCircle_nearestPoint_formulas (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hc : ‖c‖ ^ 2 = r ^ 2 + 1) (w : 𝔻)
    (hw : ∀ z : 𝔻, ‖(z : ℂ) - c‖ = r → discPathDist 0 w ≤ discPathDist 0 z)
    (hwc : ‖(w : ℂ) - c‖ = r) :
    Real.sinh (discPathDist 0 w) = 1 / r ∧ Real.cosh (discPathDist 0 w) = ‖c‖ / r := by
  have he : discPathDist 0 w = discPathDist 0 (discCircleClosestPoint c r hr hc) :=
    le_antisymm (hw _ (discCircleClosestPoint_mem c r hr hc))
      (discCircleClosestPoint_minimizes c r hr hc hwc)
  rw [he]
  exact discCircleClosestPoint_formulas c r hr hc

/-- The source formulas stated directly for any native circular disc geodesic. -/
theorem DiscLine.nearest_zero_circle_formulas (L : DiscLine) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hcircle : L.val.val = Mobius.complexCircle c r) (w : 𝔻) (hw : w ∈ L.carrier)
    (hmin : ∀ z ∈ L.carrier, discPathDist 0 w ≤ discPathDist 0 z) :
    Real.sinh (discPathDist 0 w) = 1 / r ∧ Real.cosh (discPathDist 0 w) = ‖c‖ / r := by
  have hs : L.val = ⟨Mobius.complexCircle c r, Mobius.complexCircle_isGeneralized c r hr⟩ :=
    Subtype.ext hcircle
  have hc := (complexCircle_orthogonal_discBoundary_iff c r hr).mp (by rw [← hs]; exact L.property)
  have hmem (z : 𝔻) : z ∈ L.carrier ↔ ‖(z : ℂ) - c‖ = r := by
    change ((z : ℂ) : Mobius.ExtendedComplex) ∈ L.val.val ↔ _
    rw [hcircle]
    exact Mobius.complexCircle_coe c z r
  exact discCircle_nearestPoint_formulas c r hr hc w
    (fun z hz => hmin z ((hmem z).mpr hz)) ((hmem w).mp hw)

/-- The same source identities for the actual infimum distance from zero to the geodesic. -/
theorem DiscLine.pointDist_zero_circle_formulas (L : DiscLine) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hcircle : L.val.val = Mobius.complexCircle c r) :
    Real.sinh (L.pointDist 0) = 1 / r ∧ Real.cosh (L.pointDist 0) = ‖c‖ / r := by
  obtain ⟨w, ⟨hw, hwd⟩, _⟩ := L.exists_unique_nearest_point 0
  rw [hwd]
  apply L.nearest_zero_circle_formulas c r hr hcircle w hw
  intro z hz
  rw [← hwd]
  let := discHyperbolicMetric
  change Metric.infDist (0 : 𝔻) L.carrier ≤ discPathDist 0 z
  rw [← discHyperbolicMetric_distance]
  exact Metric.infDist_le_dist_of_mem hz

end
end LowDimensionalTopology.Geometry.Hyperbolic
