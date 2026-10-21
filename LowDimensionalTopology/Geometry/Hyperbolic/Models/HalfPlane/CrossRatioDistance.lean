/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Mobius.CrossRatio.CrossRatio
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyIdealBoundary
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.MinimizingCurves
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Tactic

/-!
# Distance and ordered ideal endpoints
-/

@[expose] public section

open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius

/-- The actual complex matrix underlying a real fractional linear transformation. -/
def complexifiedRealMobiusMatrix (g : GL (Fin 2) ℝ) : Mobius.FractionalLinearMatrix :=
  Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g

/-- Positive determinant identifies the complex action with the actual upper-half-plane action. -/
theorem realMobiusMatrix_coe (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (z : ℍ) :
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ((z : ℂ) : OnePoint ℂ) =
      (((g • z : ℍ) : ℂ) : OnePoint ℂ) := by
  rw [Mobius.fractionalLinear_coe]
  have hd := UpperHalfPlane.denom_ne_zero g z
  change (g 1 0 : ℂ) * z + g 1 1 ≠ 0 at hd
  change (if (g 1 0 : ℂ) * z + g 1 1 = 0 then ∞ else
    ((((g 0 0 : ℂ) * z + g 0 1) / ((g 1 0 : ℂ) * z + g 1 1) : ℂ) : OnePoint ℂ)) = _
  rw [ite_eq_right hd, UpperHalfPlane.coe_smul_of_det_pos (by simpa using hg)]
  rfl

/-- Infinity remains on the genuine half-plane ideal boundary under every real invertible matrix. -/
theorem realMobiusMatrix_infty_mem_boundary (g : GL (Fin 2) ℝ) :
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞ ∈ halfPlaneIdealBoundary := by
  rw [Mobius.fractionalLinear_infty]
  change (if (g 1 0 : ℂ) = 0 then ∞ else
    (((g 0 0 : ℂ) / (g 1 0 : ℂ) : ℂ) : OnePoint ℂ)) ∈ _
  split_ifs
  · simp [halfPlaneIdealBoundary]
  · rw [coe_mem_halfPlaneIdealBoundary]
    simp

/-- Every finite real boundary point also remains on the genuine ideal boundary. -/
theorem realMobiusMatrix_real_mem_boundary (g : GL (Fin 2) ℝ) (r : ℝ) :
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ((r : ℂ) : OnePoint ℂ) ∈ halfPlaneIdealBoundary := by
  rw [Mobius.fractionalLinear_coe]
  change (if (g 1 0 : ℂ) * (r : ℂ) + g 1 1 = 0 then ∞ else
    ((((g 0 0 : ℂ) * (r : ℂ) + g 0 1) / ((g 1 0 : ℂ) * (r : ℂ) + g 1 1) : ℂ) :
      OnePoint ℂ)) ∈ _
  split_ifs
  · simp [halfPlaneIdealBoundary]
  · rw [coe_mem_halfPlaneIdealBoundary]
    have him (a b c d : ℝ) :
        (((a : ℂ) * (r : ℂ) + b) / ((c : ℂ) * (r : ℂ) + d)).im = 0 := by
      simp [Complex.div_im, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re]
    exact him (g 0 0) (g 0 1) (g 1 0) (g 1 1)

theorem realMobiusMatrix_maps_boundary (g : GL (Fin 2) ℝ) :
    MapsTo (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)) halfPlaneIdealBoundary halfPlaneIdealBoundary :=
      by
  intro p hp
  rw [halfPlaneIdealBoundary_eq_real_infty] at hp
  rcases hp with rfl | ⟨r, rfl⟩
  · exact realMobiusMatrix_infty_mem_boundary g
  · exact realMobiusMatrix_real_mem_boundary g r

/-- A determinant-one horizontal translation, used without an existential assumption. -/
def horizontalNormalizer (a : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![1, -a; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem horizontalNormalizer_re (a : ℝ) (z : ℍ) :
    (horizontalNormalizer a • z).re = z.re - a := by
  change ((horizontalNormalizer a • z : ℍ) : ℂ).re = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [horizontalNormalizer, sub_eq_add_neg]

theorem verticalNormalizer_zero_re {z : ℍ} (hz : z.re = 0) :
    (verticalNormalizer 0 • z).re = 0 := by
  rw [verticalNormalizer_re, hz]
  simp

theorem verticalNormalizer_zero_im {z : ℍ} (hz : z.re = 0) :
    (verticalNormalizer 0 • z).im = 1 / z.im := by
  rw [sl2_im_smul]
  change z.im / Complex.normSq (((1 : ℝ) : ℂ) * z + ((-0 : ℝ) : ℂ)) = 1 / z.im
  simp only [neg_zero, Complex.ofReal_zero, Complex.ofReal_one, one_mul, add_zero,
    Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hz, zero_mul, zero_add]
  field_simp

/-- Every distinct pair admits an actual real determinant-one normalizer with increasing imaginary heights. -/
theorem exists_sl2_ordered_imaginary (z w : ℍ) (hzw : z ≠ w) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, (g • z).re = 0 ∧ (g • w).re = 0 ∧
      (g • z).im < (g • w).im := by
  obtain ⟨g₀, h₀⟩ := exists_sl2_same_real_part z w
  let g := horizontalNormalizer (g₀ • z).re * g₀
  have hz : (g • z).re = 0 := by
    dsimp [g]
    rw [mul_smul, horizontalNormalizer_re, sub_self]
  have hw : (g • w).re = 0 := by
    dsimp [g]
    rw [mul_smul, horizontalNormalizer_re, ← h₀, sub_self]
  have hne : (g • z).im ≠ (g • w).im := by
    intro he
    apply hzw
    apply MulAction.injective g
    exact UpperHalfPlane.ext_re_im (hz.trans hw.symm) he
  by_cases hi : (g • z).im < (g • w).im
  · exact ⟨g, hz, hw, hi⟩
  · refine ⟨verticalNormalizer 0 * g, ?_, ?_, ?_⟩
    · rw [mul_smul]
      exact verticalNormalizer_zero_re hz
    · rw [mul_smul]
      exact verticalNormalizer_zero_re hw
    · have hrev : (verticalNormalizer 0 • (g • z)).im < (verticalNormalizer 0 • (g • w)).im := by
        rw [verticalNormalizer_zero_im hz, verticalNormalizer_zero_im hw]
        exact one_div_lt_one_div_of_lt (g • w).im_pos (lt_of_le_of_ne (not_lt.mp hi) hne.symm)
      simpa only [mul_smul] using hrev

/-- The cross-ratio of an actual normalized configuration is its positive height ratio. -/
theorem extendedCrossRatio_normalized_imaginary (z w : ℍ) (hz : z.re = 0) (hw : w.re = 0) :
    Mobius.extendedCrossRatio (0 : ℂ) ((z : ℂ) : OnePoint ℂ) ((w : ℂ) : OnePoint ℂ) ∞ =
      ((w.im / z.im : ℝ) : ℂ) := by
  rw [Mobius.extendedCrossRatio_infty_fourth]
  simp only [zero_sub, neg_div_neg_eq]
  have ez : (z : ℂ) = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hz]
  have ew : (w : ℂ) = (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hw]
  rw [ez, ew, mul_div_mul_right _ _ Complex.I_ne_zero]
  exact (Complex.ofReal_div _ _).symm

/-- The actual cross-ratio distance identity once all four points have been normalized by one real matrix. -/
theorem distance_eq_log_crossRatio_of_normalizer (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (z w : ℍ) (a b : OnePoint ℂ)
    (ha : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) a = (0 : ℂ))
    (hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) b = ∞)
    (hz : (g • z).re = 0) (hw : (g • w).re = 0) (hi : (g • z).im ≤ (g • w).im) :
    dist z w = Real.log (Mobius.extendedCrossRatio a ((z : ℂ) : OnePoint ℂ)
      ((w : ℂ) : OnePoint ℂ) b).re := by
  have hc := Mobius.extendedCrossRatio_fractionalLinear (complexifiedRealMobiusMatrix g)
    a ((z : ℂ) : OnePoint ℂ) ((w : ℂ) : OnePoint ℂ) b
  rw [ha, hb, realMobiusMatrix_coe g hg z, realMobiusMatrix_coe g hg w,
    extendedCrossRatio_normalized_imaginary _ _ hz hw] at hc
  rw [← hc, Complex.ofReal_re, Real.log_div (g • w).im_ne_zero (g • z).im_ne_zero,
    ← metric_distance_gl_pos g hg z w]
  exact metric_vertical_distance_of_im_le (hz.trans hw.symm) hi

/-- Complexification commutes with the actual group inverse. -/
theorem realMobiusMatrix_inv (g : GL (Fin 2) ℝ) :
    complexifiedRealMobiusMatrix g⁻¹ = (complexifiedRealMobiusMatrix g)⁻¹ :=
  map_inv (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)) g

/-- Ordered ideal endpoints and their genuine normalizing matrix exist for every distinct pair. -/
theorem exists_ordered_ideal_normalizer (z w : ℍ) (hzw : z ≠ w) :
    ∃ (a b : OnePoint ℂ) (g : GL (Fin 2) ℝ), a ∈ halfPlaneIdealBoundary ∧
      b ∈ halfPlaneIdealBoundary ∧ a ≠ b ∧ 0 < g.val.det ∧
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) a = (0 : ℂ) ∧
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) b = ∞ ∧
      (g • z).re = 0 ∧ (g • w).re = 0 ∧ (g • z).im < (g • w).im := by
  obtain ⟨s, hz, hw, hi⟩ := exists_sl2_ordered_imaginary z w hzw
  let g := Matrix.SpecialLinearGroup.mapGL ℝ s
  let a := Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)⁻¹ (0 : ℂ)
  let b := Mobius.fractionalLinear (complexifiedRealMobiusMatrix g)⁻¹ ∞
  have ha : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) a = (0 : ℂ) := by
    exact smul_inv_smul (complexifiedRealMobiusMatrix g) ((0 : ℂ) : OnePoint ℂ)
  have hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) b = ∞ := by
    exact smul_inv_smul (complexifiedRealMobiusMatrix g) (∞ : OnePoint ℂ)
  have ha' : a ∈ halfPlaneIdealBoundary := by
    dsimp [a]
    rw [← realMobiusMatrix_inv]
    exact realMobiusMatrix_real_mem_boundary g⁻¹ 0
  have hb' : b ∈ halfPlaneIdealBoundary := by
    dsimp [b]
    rw [← realMobiusMatrix_inv]
    exact realMobiusMatrix_infty_mem_boundary g⁻¹
  refine ⟨a, b, g, ha', hb', ?_, ?_, ha, hb, hz, hw, hi⟩
  · intro he
    have hh : ((0 : ℂ) : OnePoint ℂ) = ∞ := by
      rw [← ha, he, hb]
    exact (OnePoint.coe_ne_infty (0 : ℂ)) hh
  · dsimp [g]
    simp

/-- The ordered normalized configuration always has the source's positive real cross-ratio. -/
theorem exists_ideal_endpoints_distance_crossRatio (z w : ℍ) (hzw : z ≠ w) :
    ∃ a b : OnePoint ℂ, a ∈ halfPlaneIdealBoundary ∧ b ∈ halfPlaneIdealBoundary ∧ a ≠ b ∧
      1 < (Mobius.extendedCrossRatio a ((z : ℂ) : OnePoint ℂ) ((w : ℂ) : OnePoint ℂ) b).re ∧
      (Mobius.extendedCrossRatio a ((z : ℂ) : OnePoint ℂ) ((w : ℂ) : OnePoint ℂ) b).im = 0 ∧
      dist z w = Real.log (Mobius.extendedCrossRatio a ((z : ℂ) : OnePoint ℂ)
        ((w : ℂ) : OnePoint ℂ) b).re := by
  obtain ⟨a, b, g, ha, hb, hab, hg, hga, hgb, hz, hw, hi⟩ :=
    exists_ordered_ideal_normalizer z w hzw
  have hc := Mobius.extendedCrossRatio_fractionalLinear (complexifiedRealMobiusMatrix g)
    a ((z : ℂ) : OnePoint ℂ) ((w : ℂ) : OnePoint ℂ) b
  rw [hga, hgb, realMobiusMatrix_coe g hg z, realMobiusMatrix_coe g hg w,
    extendedCrossRatio_normalized_imaginary _ _ hz hw] at hc
  refine ⟨a, b, ha, hb, hab, ?_, ?_,
    distance_eq_log_crossRatio_of_normalizer g hg z w a b hga hgb hz hw hi.le⟩
  · rw [← hc, Complex.ofReal_re]
    exact (one_lt_div (g • z).im_pos).mpr hi
  · rw [← hc]
    exact Complex.ofReal_im _

/-- A genuine upper-half-plane h-line is a vertical line or a real-centred circle of positive radius. -/
def IsHalfPlaneHLine (L : Set ℍ) : Prop :=
  (∃ x : ℝ, L = {z : ℍ | z.re = x}) ∨
    ∃ (c r : ℝ), 0 < r ∧ L = {z : ℍ | ‖(z : ℂ) - (c : ℂ)‖ = r}

/-- The quadratic zero-set generated by an invertible real fractional-linear map is an actual h-line. -/
theorem real_mobius_axis_quadratic_isHLine (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) :
    IsHalfPlaneHLine {z : ℍ | (a * z.re + b) * (c * z.re + d) + a * c * z.im ^ 2 = 0} := by
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
theorem real_fractional_re_zero_iff (a b c d : ℝ) (z : ℍ)
    (hd : (c : ℂ) * z + d ≠ 0) :
    (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).re = 0 ↔
      (a * z.re + b) * (c * z.re + d) + a * c * z.im ^ 2 = 0 := by
  rw [Complex.div_re, ← add_div, div_eq_zero_iff]
  simp only [(Complex.normSq_pos.mpr hd).ne', or_false, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring_nf

/-- An actual real Möbius preimage of the imaginary axis is a Euclidean h-line, not an abstract normalizer condition. -/
theorem realMobius_axis_preimage_isHLine (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) :
    IsHalfPlaneHLine {z : ℍ | (g • z).re = 0} := by
  have he : {z : ℍ | (g • z).re = 0} =
      {z : ℍ | (g 0 0 * z.re + g 0 1) * (g 1 0 * z.re + g 1 1) +
        g 0 0 * g 1 0 * z.im ^ 2 = 0} := by
    ext z
    have hd := UpperHalfPlane.denom_ne_zero g z
    change (g 1 0 : ℂ) * z + g 1 1 ≠ 0 at hd
    change (g • z : ℍ).re = 0 ↔ _
    rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_smul_of_det_pos (by simpa using hg)]
    exact real_fractional_re_zero_iff (g 0 0) (g 0 1) (g 1 0) (g 1 1) z hd
  rw [he]
  exact real_mobius_axis_quadratic_isHLine (g 0 0) (g 0 1) (g 1 0) (g 1 1)
    (by simpa only [Matrix.det_fin_two] using g.det_ne_zero)

/-- The actual unit-speed imaginary-axis parametrization. -/
def imaginaryAxisParam (t : ℝ) : ℍ := UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t)

theorem imaginaryAxisParam_coe (t : ℝ) :
    (imaginaryAxisParam t : ℂ) = (Real.exp t : ℂ) * Complex.I := by
  change (⟨0, Real.exp t⟩ : ℂ) = (Real.exp t : ℂ) * Complex.I
  apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, neg_zero, add_zero]

theorem imaginaryAxisParam_norm (t : ℝ) : ‖(imaginaryAxisParam t : ℂ)‖ = Real.exp t := by
  rw [imaginaryAxisParam_coe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]

theorem imaginaryAxisParam_isometry : Isometry imaginaryAxisParam :=
  UpperHalfPlane.isometry_vertical_line 0

theorem imaginaryAxisParam_tendsto_zero :
    Tendsto (fun t : ℝ => ((imaginaryAxisParam t : ℂ) : OnePoint ℂ)) atBot
      (𝓝 ((0 : ℂ) : OnePoint ℂ)) := by
  have hc : Tendsto (fun t : ℝ => (imaginaryAxisParam t : ℂ)) atBot (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, imaginaryAxisParam_coe, Complex.ofReal_zero, zero_mul] using
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp Real.tendsto_exp_atBot).mul_const Complex.I)
  exact OnePoint.continuous_coe.continuousAt.tendsto.comp hc

theorem imaginaryAxisParam_tendsto_infty :
    Tendsto (fun t : ℝ => ((imaginaryAxisParam t : ℂ) : OnePoint ℂ)) atTop
      (𝓝 (∞ : OnePoint ℂ)) := by
  have hn : Tendsto (fun t : ℝ => ‖(imaginaryAxisParam t : ℂ)‖) atTop atTop := by
    simpa only [imaginaryAxisParam_norm] using Real.tendsto_exp_atTop
  have hc : Tendsto (fun t : ℝ => (imaginaryAxisParam t : ℂ)) atTop (coclosedCompact ℂ) := by
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact tendsto_norm_atTop_iff_cobounded.mp hn
  exact OnePoint.tendsto_coe_infty.comp hc

/-- The actual geodesic obtained from a real normalizer, with logarithmic height parameter. -/
def normalizerGeodesic (g : GL (Fin 2) ℝ) (t : ℝ) : ℍ := g⁻¹ • imaginaryAxisParam t

theorem normalizerGeodesic_isometry (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) :
    Isometry (normalizerGeodesic g) := by
  apply Isometry.of_dist_eq
  intro s t
  change dist (g⁻¹ • imaginaryAxisParam s) (g⁻¹ • imaginaryAxisParam t) = dist s t
  rw [metric_distance_gl_pos g⁻¹ (gl_pos_inverse g hg)]
  exact imaginaryAxisParam_isometry.dist_eq s t

theorem normalizerGeodesic_parameter (g : GL (Fin 2) ℝ) (z : ℍ) (hz : (g • z).re = 0) :
    normalizerGeodesic g (Real.log (g • z).im) = z := by
  have he : imaginaryAxisParam (Real.log (g • z).im) = g • z := by
    apply UpperHalfPlane.ext_re_im
    · simpa only [imaginaryAxisParam, UpperHalfPlane.mk_re, Complex.zero_re] using hz.symm
    · exact Real.exp_log (g • z).im_pos
  rw [normalizerGeodesic, he, inv_smul_smul]

theorem range_normalizerGeodesic (g : GL (Fin 2) ℝ) :
    Set.range (normalizerGeodesic g) = {z : ℍ | (g • z).re = 0} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    simp [normalizerGeodesic, imaginaryAxisParam]
  · intro hz
    exact ⟨Real.log (g • z).im, normalizerGeodesic_parameter g z hz⟩

theorem normalizerGeodesic_isHLine (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) :
    IsHalfPlaneHLine (Set.range (normalizerGeodesic g)) := by
  rw [range_normalizerGeodesic]
  exact realMobius_axis_preimage_isHLine g hg

theorem normalizerGeodesic_extended (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (t : ℝ) :
    ((normalizerGeodesic g t : ℂ) : OnePoint ℂ) =
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ((imaginaryAxisParam t : ℂ) : OnePoint ℂ) :=
  (realMobiusMatrix_coe g⁻¹ (gl_pos_inverse g hg) (imaginaryAxisParam t)).symm

/-- The negative infinite parameter tends to the actual first ideal endpoint. -/
theorem normalizerGeodesic_tendsto_first (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) :
    Tendsto (fun t : ℝ => ((normalizerGeodesic g t : ℂ) : OnePoint ℂ)) atBot
      (𝓝 (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) (0 : ℂ))) := by
  have h := (Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g⁻¹)).continuous.continuousAt.tendsto.comp
    imaginaryAxisParam_tendsto_zero
  change Tendsto (fun t : ℝ => Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹)
    ((imaginaryAxisParam t : ℂ) : OnePoint ℂ)) atBot
      (𝓝 (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) (0 : ℂ))) at h
  simpa only [← normalizerGeodesic_extended g hg] using h

/-- The positive infinite parameter tends to the actual second ideal endpoint. -/
theorem normalizerGeodesic_tendsto_last (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) :
    Tendsto (fun t : ℝ => ((normalizerGeodesic g t : ℂ) : OnePoint ℂ)) atTop
      (𝓝 (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ∞)) := by
  have h := (Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g⁻¹)).continuous.continuousAt.tendsto.comp
    imaginaryAxisParam_tendsto_infty
  change Tendsto (fun t : ℝ => Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹)
    ((imaginaryAxisParam t : ℂ) : OnePoint ℂ)) atTop
      (𝓝 (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ∞)) at h
  simpa only [← normalizerGeodesic_extended g hg] using h

/-- For every distinct pair, the cross-ratio identity uses the ordered ends of an actual Euclidean h-line. -/
theorem exists_ordered_geodesic_distance_crossRatio (z w : ℍ) (hzw : z ≠ w) :
    ∃ (a b : OnePoint ℂ) (γ : ℝ → ℍ) (s t : ℝ),
      a ∈ halfPlaneIdealBoundary ∧ b ∈ halfPlaneIdealBoundary ∧ a ≠ b ∧
      Isometry γ ∧ IsHalfPlaneHLine (Set.range γ) ∧ s < t ∧ γ s = z ∧ γ t = w ∧
      Tendsto (fun u => ((γ u : ℂ) : OnePoint ℂ)) atBot (𝓝 a) ∧
      Tendsto (fun u => ((γ u : ℂ) : OnePoint ℂ)) atTop (𝓝 b) ∧
      1 < (Mobius.extendedCrossRatio a ((z : ℂ) : OnePoint ℂ) ((w : ℂ) : OnePoint ℂ) b).re ∧
      (Mobius.extendedCrossRatio a ((z : ℂ) : OnePoint ℂ) ((w : ℂ) : OnePoint ℂ) b).im = 0 ∧
      dist z w = Real.log (Mobius.extendedCrossRatio a ((z : ℂ) : OnePoint ℂ)
        ((w : ℂ) : OnePoint ℂ) b).re := by
  obtain ⟨a, b, g, ha, hb, hab, hg, hga, hgb, hz, hw, hi⟩ :=
    exists_ordered_ideal_normalizer z w hzw
  have hfirst : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) (0 : ℂ) = a := by
    rw [realMobiusMatrix_inv, ← hga, Mobius.fractionalLinear_inv_apply]
  have hlast : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ∞ = b := by
    rw [realMobiusMatrix_inv, ← hgb, Mobius.fractionalLinear_inv_apply]
  have hc := Mobius.extendedCrossRatio_fractionalLinear (complexifiedRealMobiusMatrix g)
    a ((z : ℂ) : OnePoint ℂ) ((w : ℂ) : OnePoint ℂ) b
  rw [hga, hgb, realMobiusMatrix_coe g hg z, realMobiusMatrix_coe g hg w,
    extendedCrossRatio_normalized_imaginary _ _ hz hw] at hc
  refine ⟨a, b, normalizerGeodesic g, Real.log (g • z).im, Real.log (g • w).im,
    ha, hb, hab, normalizerGeodesic_isometry g hg, normalizerGeodesic_isHLine g hg,
    Real.log_lt_log (g • z).im_pos hi, normalizerGeodesic_parameter g z hz,
    normalizerGeodesic_parameter g w hw, ?_, ?_, ?_, ?_,
    distance_eq_log_crossRatio_of_normalizer g hg z w a b hga hgb hz hw hi.le⟩
  · simpa only [hfirst] using normalizerGeodesic_tendsto_first g hg
  · simpa only [hlast] using normalizerGeodesic_tendsto_last g hg
  · rw [← hc, Complex.ofReal_re]
    exact (one_lt_div (g • z).im_pos).mpr hi
  · rw [← hc]
    exact Complex.ofReal_im _

/-- Cayley invariance is for the actual extended fractional-linear map. -/
theorem extendedCrossRatio_extendedCayley (a z w b : OnePoint ℂ) :
    Mobius.extendedCrossRatio (extendedCayley a) (extendedCayley z) (extendedCayley w)
      (extendedCayley b) = Mobius.extendedCrossRatio a z w b :=
  Mobius.extendedCrossRatio_fractionalLinear extendedCayleyMatrix a z w b

theorem extendedCayley_halfPlane (z : ℍ) :
    extendedCayley ((z : ℂ) : OnePoint ℂ) = ((halfPlaneToDisc z : ℂ) : OnePoint ℂ) :=
  extendedCayley_coe z (cayley_denom_ne_zero z)

/-- The same source identity in the actual unit-disc model, at its genuine ideal boundary. -/
theorem exists_disc_ideal_endpoints_distance_crossRatio (z w : 𝔻) (hzw : z ≠ w) :
    ∃ a b : OnePoint ℂ, a ∈ extendedDiscIdealBoundary ∧ b ∈ extendedDiscIdealBoundary ∧ a ≠ b ∧
      1 < (Mobius.extendedCrossRatio a ((z : ℂ) : OnePoint ℂ) ((w : ℂ) : OnePoint ℂ) b).re ∧
      (Mobius.extendedCrossRatio a ((z : ℂ) : OnePoint ℂ) ((w : ℂ) : OnePoint ℂ) b).im = 0 ∧
      discPathDist z w = Real.log (Mobius.extendedCrossRatio a ((z : ℂ) : OnePoint ℂ)
        ((w : ℂ) : OnePoint ℂ) b).re := by
  have hZW : discToHalfPlane z ≠ discToHalfPlane w := by
    intro he
    exact hzw (cayleyHomeomorph.symm.injective he)
  obtain ⟨a, b, ha, hb, hab, hr, hi, hd⟩ :=
    exists_ideal_endpoints_distance_crossRatio (discToHalfPlane z) (discToHalfPlane w) hZW
  have hc := extendedCrossRatio_extendedCayley a
    (((discToHalfPlane z : ℍ) : ℂ) : OnePoint ℂ)
    (((discToHalfPlane w : ℍ) : ℂ) : OnePoint ℂ) b
  rw [extendedCayley_halfPlane, extendedCayley_halfPlane,
    halfPlaneToDisc_discToHalfPlane, halfPlaneToDisc_discToHalfPlane] at hc
  refine ⟨extendedCayley a, extendedCayley b, (idealBoundary_cayley_iff a).mp ha,
    (idealBoundary_cayley_iff b).mp hb, fun he => hab (extendedCayley.injective he), ?_, ?_, ?_⟩
  · rw [hc]
    exact hr
  · rw [hc]
    exact hi
  · rw [hc, discPathDist_eq_halfPlane]
    exact hd

/-- Cayley transports the actual ordered geodesic, its two ideal limits, and the distance formula to the disc. -/
theorem exists_disc_ordered_geodesic_distance_crossRatio (z w : 𝔻) (hzw : z ≠ w) :
    letI := discHyperbolicMetric
    ∃ (a b : OnePoint ℂ) (γ : ℝ → 𝔻) (s t : ℝ),
      a ∈ extendedDiscIdealBoundary ∧ b ∈ extendedDiscIdealBoundary ∧ a ≠ b ∧
      Isometry γ ∧ s < t ∧ γ s = z ∧ γ t = w ∧
      Tendsto (fun u => ((γ u : ℂ) : OnePoint ℂ)) atBot (𝓝 a) ∧
      Tendsto (fun u => ((γ u : ℂ) : OnePoint ℂ)) atTop (𝓝 b) ∧
      1 < (Mobius.extendedCrossRatio a ((z : ℂ) : OnePoint ℂ) ((w : ℂ) : OnePoint ℂ) b).re ∧
      (Mobius.extendedCrossRatio a ((z : ℂ) : OnePoint ℂ) ((w : ℂ) : OnePoint ℂ) b).im = 0 ∧
      discPathDist z w = Real.log (Mobius.extendedCrossRatio a ((z : ℂ) : OnePoint ℂ)
        ((w : ℂ) : OnePoint ℂ) b).re := by
  let := discHyperbolicMetric
  have hZW : discToHalfPlane z ≠ discToHalfPlane w := by
    intro he
    exact hzw (cayleyHomeomorph.symm.injective he)
  obtain ⟨a, b, γ, s, t, ha, hb, hab, hγ, _, hst, hs, ht, hfirst, hlast, hr, hi, hd⟩ :=
    exists_ordered_geodesic_distance_crossRatio (discToHalfPlane z) (discToHalfPlane w) hZW
  have hc := extendedCrossRatio_extendedCayley a
    (((discToHalfPlane z : ℍ) : ℂ) : OnePoint ℂ)
    (((discToHalfPlane w : ℍ) : ℂ) : OnePoint ℂ) b
  rw [extendedCayley_halfPlane, extendedCayley_halfPlane,
    halfPlaneToDisc_discToHalfPlane, halfPlaneToDisc_discToHalfPlane] at hc
  refine ⟨extendedCayley a, extendedCayley b, halfPlaneToDisc ∘ γ, s, t,
    (idealBoundary_cayley_iff a).mp ha, (idealBoundary_cayley_iff b).mp hb,
    fun he => hab (extendedCayley.injective he), cayley_isometry.comp hγ, hst, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simp only [Function.comp_def, hs, halfPlaneToDisc_discToHalfPlane]
  · simp only [Function.comp_def, ht, halfPlaneToDisc_discToHalfPlane]
  · have he := extendedCayley.continuous.continuousAt.tendsto.comp hfirst
    change Tendsto (fun u => extendedCayley ((γ u : ℂ) : OnePoint ℂ)) atBot (𝓝 (extendedCayley a)) at he
    simpa only [Function.comp_def, extendedCayley_halfPlane] using he
  · have he := extendedCayley.continuous.continuousAt.tendsto.comp hlast
    change Tendsto (fun u => extendedCayley ((γ u : ℂ) : OnePoint ℂ)) atTop (𝓝 (extendedCayley b)) at he
    simpa only [Function.comp_def, extendedCayley_halfPlane] using he
  · rw [hc]
    exact hr
  · rw [hc]
    exact hi
  · rw [hc, discPathDist_eq_halfPlane]
    exact hd

end

end LowDimensionalTopology.Geometry.Hyperbolic
