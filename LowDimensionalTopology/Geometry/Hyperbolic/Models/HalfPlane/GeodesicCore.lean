/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.MinimizingCurves

@[expose] public section

open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

theorem halfPlane_dist_triangle_eq_iff_vertical_between {z w u : ℍ}
    (hr : z.re = w.re) (hi : z.im ≤ w.im) :
    dist z u + dist u w = dist z w ↔
      u.re = z.re ∧ z.im ≤ u.im ∧ u.im ≤ w.im := by
  constructor
  · intro heq
    obtain ⟨p, hp0, hp1, hp⟩ := exists_length_minimizing_piece z u
    obtain ⟨q, hq0, hq1, hq⟩ := exists_length_minimizing_piece u w
    have hpl := p.logHeightChange_le_length
    have hql := q.logHeightChange_le_length
    dsimp [C1CurvePiece.logHeightChange] at hpl hql
    rw [hp0, hp1] at hpl
    rw [hq0, hq1] at hql
    have hzw := metric_vertical_distance_of_im_le hr hi
    have hpe : p.length = p.logHeightChange := by
      dsimp [C1CurvePiece.logHeightChange]
      rw [hp0, hp1]
      linarith
    have hqe : q.length = q.logHeightChange := by
      dsimp [C1CurvePiece.logHeightChange]
      rw [hq0, hq1]
      linarith
    have hpg := (p.length_eq_logHeightChange_iff.mp hpe).geometry
    have hqg := (q.length_eq_logHeightChange_iff.mp hqe).geometry
    have hpre := hpg.1 p.b (right_mem_Icc.mpr p.ordered)
    have hpim := hpg.2 (left_mem_Icc.mpr p.ordered)
      (right_mem_Icc.mpr p.ordered) p.ordered
    have hqim := hqg.2 (left_mem_Icc.mpr q.ordered)
      (right_mem_Icc.mpr q.ordered) q.ordered
    simpa only [hp0, hp1, hq0, hq1] using And.intro hpre (And.intro hpim hqim)
  · rintro ⟨hu, hzu, huw⟩
    rw [metric_vertical_distance_of_im_le hu.symm hzu,
      metric_vertical_distance_of_im_le (hu.trans hr) huw,
      metric_vertical_distance_of_im_le hr hi]
    ring

/-- A complete vertical geodesic parametrized by logarithmic height. -/
def halfPlaneVerticalLogParam (a t : ℝ) : ℍ :=
  ⟨(a : ℂ) + (Real.exp t : ℂ) * Complex.I, by
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add] using Real.exp_pos t⟩

theorem halfPlaneVerticalLogParam_re (a t : ℝ) : (halfPlaneVerticalLogParam a t).re = a := by
  simp [halfPlaneVerticalLogParam]

theorem halfPlaneVerticalLogParam_im (a t : ℝ) : (halfPlaneVerticalLogParam a t).im = Real.exp t := by
  simp only [halfPlaneVerticalLogParam, UpperHalfPlane.mk_im, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re,
    mul_one, zero_mul, add_zero, zero_add]

theorem halfPlaneVerticalLogParam_log_im (a : ℝ) (z : ℍ) (hz : z.re = a) :
    halfPlaneVerticalLogParam a (Real.log z.im) = z := by
  apply UpperHalfPlane.ext_re_im
  · simpa only [halfPlaneVerticalLogParam_re] using hz.symm
  · rw [halfPlaneVerticalLogParam_im, Real.exp_log z.im_pos]

theorem halfPlaneVerticalLogParam_dist (a s t : ℝ) :
    dist (halfPlaneVerticalLogParam a s) (halfPlaneVerticalLogParam a t) = dist s t := by
  rw [UpperHalfPlane.dist_of_re_eq (by simp only [halfPlaneVerticalLogParam_re]),
    halfPlaneVerticalLogParam_im, halfPlaneVerticalLogParam_im, Real.log_exp, Real.log_exp]

/-- Möbius transport sends logarithmic vertical geodesics to complete half-plane geodesics. -/
def halfPlaneSL2Geodesic (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a t : ℝ) : ℍ :=
  g⁻¹ • halfPlaneVerticalLogParam a t

theorem halfPlaneSL2Geodesic_parameter (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (a : ℝ) (z : ℍ) (hz : (g • z).re = a) :
    halfPlaneSL2Geodesic g a (Real.log (g • z).im) = z := by
  rw [halfPlaneSL2Geodesic, halfPlaneVerticalLogParam_log_im a (g • z) hz, inv_smul_smul]

theorem halfPlaneSL2Geodesic_isometry (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a : ℝ) :
    Isometry (halfPlaneSL2Geodesic g a) := by
  apply Isometry.of_dist_eq
  intro s t
  simpa only [halfPlaneSL2Geodesic, dist_smul] using halfPlaneVerticalLogParam_dist a s t

theorem halfPlane_real_triangle_eq_iff_uIcc (s t r : ℝ) :
    dist s r + dist r t = dist s t ↔ r ∈ uIcc s t := by
  rw [Real.dist_eq, Real.dist_eq, Real.dist_eq]
  rcases le_total s t with hst | hts
  · rw [uIcc_of_le hst, abs_of_nonpos (sub_nonpos.mpr hst)]
    constructor
    · intro h
      constructor <;> by_contra hh
      · rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hh)),
          abs_of_nonpos (sub_nonpos.mpr ((lt_of_not_ge hh).le.trans hst))] at h
        linarith
      · rw [abs_of_nonpos (sub_nonpos.mpr (hst.trans (lt_of_not_ge hh).le)),
          abs_of_pos (sub_pos.mpr (lt_of_not_ge hh))] at h
        linarith
    · rintro ⟨hsr, hrt⟩
      rw [abs_of_nonpos (sub_nonpos.mpr hsr), abs_of_nonpos (sub_nonpos.mpr hrt)]
      ring
  · rw [uIcc_of_ge hts, abs_of_nonneg (sub_nonneg.mpr hts)]
    constructor
    · intro h
      constructor <;> by_contra hh
      · rw [abs_of_nonneg (sub_nonneg.mpr ((lt_of_not_ge hh).le.trans hts)),
          abs_of_neg (sub_neg.mpr (lt_of_not_ge hh))] at h
        linarith
      · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hh)),
          abs_of_nonneg (sub_nonneg.mpr (hts.trans (lt_of_not_ge hh).le))] at h
        linarith
    · rintro ⟨htr, hrs⟩
      rw [abs_of_nonneg (sub_nonneg.mpr hrs), abs_of_nonneg (sub_nonneg.mpr htr)]
      ring

/-- Triangle equality gives exactly the actual interval of a normalized complete geodesic. -/
theorem halfPlane_triangle_eq_iff_geodesic_interval
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z w p : ℍ)
    (hre : (g • z).re = (g • w).re) :
    dist z p + dist p w = dist z w ↔
      p ∈ halfPlaneSL2Geodesic g (g • z).re ''
        uIcc (Real.log (g • z).im) (Real.log (g • w).im) := by
  constructor
  · intro heq
    have heq' : dist (g • z) (g • p) + dist (g • p) (g • w) = dist (g • z) (g • w) := by
      simpa only [dist_smul] using heq
    refine ⟨Real.log (g • p).im, ?_,
      halfPlaneSL2Geodesic_parameter g (g • z).re p ?_⟩
    · rcases le_total (g • z).im (g • w).im with hi | hi
      · have hu := (halfPlane_dist_triangle_eq_iff_vertical_between hre hi).mp heq'
        rw [uIcc_of_le (Real.log_le_log (g • z).im_pos hi)]
        exact ⟨Real.log_le_log (g • z).im_pos hu.2.1,
          Real.log_le_log (g • p).im_pos hu.2.2⟩
      · have heq'' : dist (g • w) (g • p) + dist (g • p) (g • z) = dist (g • w) (g • z) := by
          simpa only [dist_comm, add_comm] using heq'
        have hu := (halfPlane_dist_triangle_eq_iff_vertical_between hre.symm hi).mp heq''
        rw [uIcc_of_ge (Real.log_le_log (g • w).im_pos hi)]
        exact ⟨Real.log_le_log (g • w).im_pos hu.2.1,
          Real.log_le_log (g • p).im_pos hu.2.2⟩
    · rcases le_total (g • z).im (g • w).im with hi | hi
      · exact ((halfPlane_dist_triangle_eq_iff_vertical_between hre hi).mp heq').1
      · have heq'' : dist (g • w) (g • p) + dist (g • p) (g • z) = dist (g • w) (g • z) := by
          simpa only [dist_comm, add_comm] using heq'
        exact (((halfPlane_dist_triangle_eq_iff_vertical_between hre.symm hi).mp heq'').1).trans hre.symm
  · rintro ⟨r, hr, rfl⟩
    have hz := halfPlaneSL2Geodesic_parameter g (g • z).re z rfl
    have hw := halfPlaneSL2Geodesic_parameter g (g • z).re w hre.symm
    let Γ := halfPlaneSL2Geodesic g (g • z).re
    have hΓ : Isometry Γ := halfPlaneSL2Geodesic_isometry g (g • z).re
    have h : dist (Γ (Real.log (g • z).im)) (Γ r) +
        dist (Γ r) (Γ (Real.log (g • w).im)) =
        dist (Γ (Real.log (g • z).im)) (Γ (Real.log (g • w).im)) := by
      rw [hΓ.dist_eq, hΓ.dist_eq, hΓ.dist_eq]
      exact (halfPlane_real_triangle_eq_iff_uIcc _ _ _).mpr hr
    simpa only [Γ, hz, hw] using h

/-! ## Euclidean shapes of complete geodesics -/

def IsHalfPlaneGeodesicLine (L : Set ℍ) : Prop :=
  (∃ x : ℝ, L = {z : ℍ | z.re = x}) ∨
    ∃ (c r : ℝ), 0 < r ∧ L = {z : ℍ | ‖(z : ℂ) - (c : ℂ)‖ = r}

/-- The quadratic zero-set generated by an invertible real fractional-linear map is an actual h-line. -/
theorem halfPlane_real_mobius_axis_quadratic_isLine (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) :
    IsHalfPlaneGeodesicLine {z : ℍ | (a * z.re + b) * (c * z.re + d) + a * c * z.im ^ 2 = 0} := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by intro h; apply hdet; simp [ha, h]
    have hc : c ≠ 0 := by intro h; apply hdet; simp [ha, h]
    left
    refine ⟨-d / c, ?_⟩
    ext z
    change (a * z.re + b) * (c * z.re + d) + a * c * z.im ^ 2 = 0 ↔ z.re = -d / c
    rw [ha]
    simp only [zero_mul, zero_add, add_zero, mul_eq_zero, hb, false_or]
    rw [eq_div_iff hc]
    constructor <;> intro h <;> nlinarith
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by intro h; apply hdet; simp [hc, h]
    left
    refine ⟨-b / a, ?_⟩
    ext z
    change (a * z.re + b) * (c * z.re + d) + a * c * z.im ^ 2 = 0 ↔ z.re = -b / a
    rw [hc]
    simp only [zero_mul, add_zero, zero_add, mul_zero, mul_eq_zero, hd, or_false]
    rw [eq_div_iff ha]
    constructor <;> intro h <;> nlinarith
  let α := -b / a
  let β := -d / c
  have hab : α ≠ β := by
    intro h
    apply hdet
    dsimp [α, β] at h
    field_simp [ha, hc] at h
    nlinarith
  let m := (α + β) / 2
  let r := |β - α| / 2
  have hr : 0 < r := div_pos (abs_pos.mpr (sub_ne_zero.mpr hab.symm)) (by norm_num)
  have halg (x y : ℝ) :
      (a * x + b) * (c * x + d) + a * c * y ^ 2 =
        a * c * ((x - m) ^ 2 + y ^ 2 - r ^ 2) := by
    dsimp [m, r, α, β]
    rw [div_pow, sq_abs]
    field_simp [ha, hc]
    ring
  right
  refine ⟨m, r, hr, ?_⟩
  ext z
  change (a * z.re + b) * (c * z.re + d) + a * c * z.im ^ 2 = 0 ↔
    ‖(z : ℂ) - (m : ℂ)‖ = r
  rw [halg, mul_eq_zero]
  simp only [mul_ne_zero ha hc, false_or, sub_eq_zero]
  rw [← sq_eq_sq₀ (norm_nonneg _) hr.le, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  constructor <;> intro h <;> nlinarith

/-- The real part of an actual finite fractional-linear map has the stated quadratic numerator. -/
theorem halfPlane_real_fractional_re_zero_iff (a b c d : ℝ) (z : ℍ)
    (hd : (c : ℂ) * z + d ≠ 0) :
    (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).re = 0 ↔
      (a * z.re + b) * (c * z.re + d) + a * c * z.im ^ 2 = 0 := by
  rw [Complex.div_re, ← add_div, div_eq_zero_iff]
  simp only [(Complex.normSq_pos.mpr hd).ne', or_false, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring_nf

/-- An actual real Möbius preimage of the imaginary axis is a Euclidean h-line, not an abstract normalizer condition. -/
theorem halfPlane_realMobius_axis_preimage_isLine (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) :
    IsHalfPlaneGeodesicLine {z : ℍ | (g • z).re = 0} := by
  have he : {z : ℍ | (g • z).re = 0} =
      {z : ℍ | (g 0 0 * z.re + g 0 1) * (g 1 0 * z.re + g 1 1) +
        g 0 0 * g 1 0 * z.im ^ 2 = 0} := by
    ext z
    have hd := UpperHalfPlane.denom_ne_zero g z
    change (g 1 0 : ℂ) * z + g 1 1 ≠ 0 at hd
    change (g • z : ℍ).re = 0 ↔ _
    rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_smul_of_det_pos (by simpa using hg)]
    exact halfPlane_real_fractional_re_zero_iff (g 0 0) (g 0 1) (g 1 0) (g 1 1) z hd
  rw [he]
  exact halfPlane_real_mobius_axis_quadratic_isLine (g 0 0) (g 0 1) (g 1 0) (g 1 1)
    (by simpa only [Matrix.det_fin_two] using g.det_ne_zero)

def halfPlaneHorizontalShift (a : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![1, -a; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem halfPlaneHorizontalShift_re (a : ℝ) (z : ℍ) :
    (halfPlaneHorizontalShift a • z).re = z.re - a := by
  change ((halfPlaneHorizontalShift a • z : ℍ) : ℂ).re = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [halfPlaneHorizontalShift, sub_eq_add_neg]

theorem halfPlaneSL2Geodesic_range (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a : ℝ) :
    range (halfPlaneSL2Geodesic g a) = {z : ℍ | (g • z).re = a} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    change (g • (g⁻¹ • halfPlaneVerticalLogParam a t)).re = a
    rw [smul_inv_smul, halfPlaneVerticalLogParam_re]
  · intro hz
    exact ⟨Real.log (g • z).im, halfPlaneSL2Geodesic_parameter g a z hz⟩

/-- Every transported complete metric geodesic is an actual perpendicular circle or vertical line. -/
theorem halfPlaneSL2Geodesic_isLine (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a : ℝ) :
    IsHalfPlaneGeodesicLine (range (halfPlaneSL2Geodesic g a)) := by
  let h := halfPlaneHorizontalShift a * g
  have he : {z : ℍ | (g • z).re = a} =
      {z : ℍ | (Matrix.SpecialLinearGroup.mapGL ℝ h • z).re = 0} := by
    ext z
    change (g • z).re = a ↔ (h • z).re = 0
    dsimp only [h]
    rw [mul_smul, halfPlaneHorizontalShift_re, sub_eq_zero]
  rw [halfPlaneSL2Geodesic_range, he]
  exact halfPlane_realMobius_axis_preimage_isLine (Matrix.SpecialLinearGroup.mapGL ℝ h) (by simp)


end
end LowDimensionalTopology.Geometry.Hyperbolic
