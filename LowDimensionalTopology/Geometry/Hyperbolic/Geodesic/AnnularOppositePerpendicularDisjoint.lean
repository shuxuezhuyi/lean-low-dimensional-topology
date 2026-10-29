module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.NativeLineDisjointOfInversiveProduct
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The outer/small-circle common perpendicular is genuinely disjoint from the unit circle. -/
theorem annular_inner_circle_hDisjoint_outer_common_perpendicular
    (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) (hE1 : 1 < E)
    (hinner : 1 + r < x) (houter : x + r < E) (N : HalfPlaneLine)
    (hEN : (HalfPlaneLine.circle 0 E hE).Orthogonal N)
    (hMN : (HalfPlaneLine.circle x r hr).Orthogonal N) :
    (HalfPlaneLine.circle 0 1 (by norm_num)).HDisjoint N := by
  have hx1 : 1 < x := by linarith
  have hx : 0 < x := lt_trans zero_lt_one hx1
  have hxr : r < x := by linarith
  have hxE : x < E := by linarith
  have hEEsq : E < E ^ 2 := by
    nlinarith only [mul_pos hE (sub_pos.mpr hE1)]
  have hEsq : 1 < E ^ 2 := lt_trans hE1 hEEsq
  have hxEsq : x < E ^ 2 := lt_trans hxE hEEsq
  have h0 := ((HalfPlaneLine.circle 0 E hE).orthogonal_iff_coefficients N).mp hEN
  have hxN := ((HalfPlaneLine.circle x r hr).orthogonal_iff_coefficients N).mp hMN
  cases N with
  | vertical d =>
    change (0 : ℝ) = d at h0
    change x = d at hxN
    exact False.elim (hx.ne' (hxN.trans h0.symm))
  | circle d ρ hρ =>
    change (0 - d) ^ 2 = E ^ 2 + ρ ^ 2 at h0
    change (x - d) ^ 2 = r ^ 2 + ρ ^ 2 at hxN
    have hdeq : 2 * d * x = x ^ 2 + E ^ 2 - r ^ 2 := by
      nlinarith only [h0, hxN]
    have hgap : 0 < (x - 1) * (E ^ 2 - x) + r ^ 2 :=
      add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hxEsq)) (sq_nonneg r)
    have hlim : 2 * d < E ^ 2 + 1 := by
      have hp : 0 < x * (E ^ 2 + 1 - 2 * d) := by nlinarith only [hdeq, hgap]
      have hpos := (mul_pos_iff_of_pos_left hx).mp hp
      linarith
    have hsq : r ^ 2 < x ^ 2 := (sq_lt_sq₀ hr.le hx.le).mpr hxr
    have hdprod : 0 < (2 * x) * d := by nlinarith only [hdeq, hsq, hEsq]
    have hd : 0 < d :=
      (mul_pos_iff_of_pos_left (mul_pos (by norm_num : (0 : ℝ) < 2) hx)).mp hdprod
    have hd1 : 1 < d := by
      apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hd.le).mp
      nlinarith only [h0, hEsq, sq_nonneg ρ]
    have hρd : ρ < d - 1 := by
      apply (sq_lt_sq₀ hρ.le (by linarith : 0 ≤ d - 1)).mp
      nlinarith only [h0, hlim]
    have hρbound : 2 * ρ < E ^ 2 - 1 := by linarith
    have hpair : (HalfPlaneLine.circle 0 1 (by norm_num)).normalPairing
        (HalfPlaneLine.circle d ρ hρ) = (1 - E ^ 2) / (2 * ρ) := by
      simp only [HalfPlaneLine.normalPairing, HalfPlaneLine.incenterNormal,
        HalfPlaneLine.incenterOffset,
        LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
      field_simp [hρ.ne']
      nlinarith only [h0]
    apply (HalfPlaneLine.circle 0 1 (by norm_num)).hDisjoint_of_one_lt_abs_normalPairing
      (HalfPlaneLine.circle d ρ hρ)
    rw [hpair, abs_div, abs_of_neg (sub_neg.mpr hEsq),
      abs_of_pos (by positivity : 0 < 2 * ρ)]
    apply (lt_div_iff₀ (by positivity : 0 < 2 * ρ)).mpr
    linarith

end
end LowDimensionalTopology.Geometry.Hyperbolic
