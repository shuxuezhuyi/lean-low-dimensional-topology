module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.NativeLineDisjointOfInversiveProduct
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The inner/small-circle common perpendicular is genuinely disjoint from the outer circle. -/
theorem annular_outer_circle_hDisjoint_inner_common_perpendicular
    (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) (hE1 : 1 < E)
    (hinner : 1 + r < x) (houter : x + r < E) (N : HalfPlaneLine)
    (h1N : (HalfPlaneLine.circle 0 1 (by norm_num)).Orthogonal N)
    (hMN : (HalfPlaneLine.circle x r hr).Orthogonal N) :
    (HalfPlaneLine.circle 0 E hE).HDisjoint N := by
  have hx1 : 1 < x := by linarith
  have hx : 0 < x := lt_trans zero_lt_one hx1
  have hxr : r < x := by linarith
  have hxE : x < E := by linarith
  have hEsq : 1 < E ^ 2 := by nlinarith only [hE1, sq_nonneg (E - 1)]
  have hEx1 : 1 < E * x := by
    nlinarith only [hx1, mul_pos (sub_pos.mpr hE1) hx]
  have h0 := ((HalfPlaneLine.circle 0 1 (by norm_num)).orthogonal_iff_coefficients N).mp h1N
  have hxN := ((HalfPlaneLine.circle x r hr).orthogonal_iff_coefficients N).mp hMN
  cases N with
  | vertical d =>
    change (0 : ℝ) = d at h0
    change x = d at hxN
    exact False.elim (hx.ne' (hxN.trans h0.symm))
  | circle d ρ hρ =>
    change (0 - d) ^ 2 = (1 : ℝ) ^ 2 + ρ ^ 2 at h0
    simp only [zero_sub, neg_sq, one_pow] at h0
    change (x - d) ^ 2 = r ^ 2 + ρ ^ 2 at hxN
    have hdeq : 2 * d * x = x ^ 2 + 1 - r ^ 2 := by
      nlinarith only [h0, hxN]
    have hgap : 0 < (E - x) * (E * x - 1) + E * r ^ 2 :=
      add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr hxE) (sub_pos.mpr hEx1))
        (mul_nonneg hE.le (sq_nonneg r))
    have hdeqE := congrArg (fun u : ℝ => E * u) hdeq
    have hlim : 2 * E * d < E ^ 2 + 1 := by
      have hp : 0 < x * (E ^ 2 + 1 - 2 * E * d) := by
        nlinarith only [hdeqE, hgap]
      have hpos := (mul_pos_iff_of_pos_left hx).mp hp
      linarith
    have hsq : r ^ 2 < x ^ 2 := (sq_lt_sq₀ hr.le hx.le).mpr hxr
    have hdprod : 0 < (2 * x) * d := by nlinarith only [hdeq, hsq]
    have hd : 0 < d :=
      (mul_pos_iff_of_pos_left (mul_pos (by norm_num : (0 : ℝ) < 2) hx)).mp hdprod
    have hd1 : 1 < d := by
      apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hd.le).mp
      nlinarith only [h0, sq_pos_of_pos hρ]
    have hEd1 : 1 < E * d := by
      nlinarith only [hd1, mul_pos (sub_pos.mpr hE1) hd]
    have hscaled : (E * d) ^ 2 = E ^ 2 + (E * ρ) ^ 2 := by
      nlinarith only [congrArg (fun u : ℝ => E ^ 2 * u) h0]
    have hRlt : E * ρ < E * d - 1 := by
      apply (sq_lt_sq₀ (mul_pos hE hρ).le (by linarith : 0 ≤ E * d - 1)).mp
      nlinarith only [hscaled, hlim]
    have hρbound : 2 * E * ρ < E ^ 2 - 1 := by nlinarith only [hRlt, hlim]
    have hpair : (HalfPlaneLine.circle 0 E hE).normalPairing
        (HalfPlaneLine.circle d ρ hρ) = (E ^ 2 - 1) / (2 * E * ρ) := by
      simp only [HalfPlaneLine.normalPairing, HalfPlaneLine.incenterNormal,
        HalfPlaneLine.incenterOffset,
        LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
      field_simp [hE.ne', hρ.ne']
      nlinarith only [h0]
    have hden : 0 < 2 * E * ρ := by positivity
    apply (HalfPlaneLine.circle 0 E hE).hDisjoint_of_one_lt_abs_normalPairing
      (HalfPlaneLine.circle d ρ hρ)
    rw [hpair, abs_of_pos (div_pos (sub_pos.mpr hEsq) hden)]
    apply (lt_div_iff₀ hden).mpr
    nlinarith only [hρbound]

end
end LowDimensionalTopology.Geometry.Hyperbolic
