module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicOrthogonality
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HalfPlaneLorentzReflections
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
open scoped UpperHalfPlane
noncomputable section

/-- A common-perpendicular foot on the centered circle lies strictly to the right. -/
theorem circle_common_perpendicular_foot_re_pos
    (s r x : ℝ) (hs : 0 < s) (hr : 0 < r) (hxr : r < x)
    (N : HalfPlaneLine) (p : ℍ)
    (hp : (HalfPlaneLine.circle 0 s hs).OrthogonalAt N p)
    (hM : (HalfPlaneLine.circle x r hr).Orthogonal N) : 0 < p.re := by
  have hx : 0 < x := lt_trans hr hxr
  have h0 := ((HalfPlaneLine.circle 0 s hs).orthogonal_iff_coefficients N).mp ⟨p, hp⟩
  have hxN := ((HalfPlaneLine.circle x r hr).orthogonal_iff_coefficients N).mp hM
  cases N with
  | vertical d =>
    change (0 : ℝ) = d at h0
    change x = d at hxN
    exact False.elim (hx.ne' (hxN.trans h0.symm))
  | circle d ρ hρ =>
    change (0 - d) ^ 2 = s ^ 2 + ρ ^ 2 at h0
    change (x - d) ^ 2 = r ^ 2 + ρ ^ 2 at hxN
    have hgap : 0 < (x - r) * (x + r) :=
      mul_pos (sub_pos.mpr hxr) (by linarith)
    have hnum : 0 < x ^ 2 + s ^ 2 - r ^ 2 := by
      nlinarith only [hgap, sq_nonneg s]
    have hdprod : 0 < (2 * x) * d := by
      nlinarith only [h0, hxN, hnum]
    have hd : 0 < d :=
      (mul_pos_iff_of_pos_left (mul_pos (by norm_num : (0 : ℝ) < 2) hx)).mp hdprod
    have hp0 := norm_sub_real_eq_radius_sq hp.1
    have hpd := norm_sub_real_eq_radius_sq hp.2.1
    have hprod : d * p.re = s ^ 2 := by
      nlinarith only [h0, hp0, hpd]
    exact (mul_pos_iff_of_pos_left hd).mp (by
      rw [hprod]
      exact sq_pos_of_pos hs)

/-- The same actual foot has the negative native vertical-side normal sign. -/
theorem circle_common_perpendicular_foot_vertical_time_neg
    (s r x : ℝ) (hs : 0 < s) (hr : 0 < r) (hxr : r < x)
    (N : HalfPlaneLine) (p : ℍ)
    (hp : (HalfPlaneLine.circle 0 s hs).OrthogonalAt N p)
    (hM : (HalfPlaneLine.circle x r hr).Orthogonal N) :
    (HalfPlaneLine.vertical 0).normalTimeAt p < 0 := by
  have hpRe := circle_common_perpendicular_foot_re_pos s r x hs hr hxr N p hp hM
  rw [HalfPlaneLine.normalTimeAt_vertical, zero_sub]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hpRe) p.im_pos

end
end LowDimensionalTopology.Geometry.Hyperbolic
