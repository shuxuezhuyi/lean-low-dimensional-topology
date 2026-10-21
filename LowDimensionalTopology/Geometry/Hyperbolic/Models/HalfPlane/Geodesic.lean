/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.CrossRatioDistance
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Tactic

/-!
# Actual half-plane h-lines and incidence
-/

@[expose] public section

open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

/-- The two genuine Euclidean presentations of an h-line in the upper half-plane. -/
inductive HalfPlaneLine where
  | vertical (x : ℝ)
  | circle (center radius : ℝ) (radius_pos : 0 < radius)

/-- Its actual point set in the upper half-plane. -/
def HalfPlaneLine.carrier : HalfPlaneLine → Set ℍ
  | .vertical x => {z : ℍ | z.re = x}
  | .circle c r _ => {z : ℍ | ‖(z : ℂ) - (c : ℂ)‖ = r}

theorem HalfPlaneLine.isHLine (L : HalfPlaneLine) : IsHalfPlaneHLine L.carrier := by
  cases L with
  | vertical x => exact Or.inl ⟨x, rfl⟩
  | circle c r hr => exact Or.inr ⟨c, r, hr, rfl⟩

theorem exists_halfPlaneLine_of_isHLine {S : Set ℍ} (h : IsHalfPlaneHLine S) :
    ∃ L : HalfPlaneLine, L.carrier = S := by
  rcases h with ⟨x, hx⟩ | ⟨c, r, hr, hc⟩
  · exact ⟨.vertical x, hx.symm⟩
  · exact ⟨.circle c r hr, hc.symm⟩

/-- The exact Euclidean circle equation, expressed in the half-plane coordinates. -/
theorem norm_sub_real_eq_radius_sq {c r : ℝ} {z : ℍ}
    (h : ‖(z : ℂ) - (c : ℂ)‖ = r) : (z.re - c) ^ 2 + z.im ^ 2 = r ^ 2 := by
  have hs := congrArg (fun x : ℝ => x ^ 2) h
  rw [← Complex.normSq_eq_norm_sq] at hs
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hs
  nlinarith

/-- A real-centred circle contains at most one upper-half-plane point on each vertical line. -/
theorem eq_of_circle_mem_of_re_eq {c r : ℝ} {z w : ℍ}
    (hz : ‖(z : ℂ) - (c : ℂ)‖ = r) (hw : ‖(w : ℂ) - (c : ℂ)‖ = r)
    (hre : z.re = w.re) : z = w := by
  have hzs := norm_sub_real_eq_radius_sq hz
  have hws := norm_sub_real_eq_radius_sq hw
  apply UpperHalfPlane.ext_re_im hre
  rw [hre] at hzs
  nlinarith [z.im_pos, w.im_pos]

/-- Any two actual h-lines through the same two distinct interior points coincide. -/
theorem HalfPlaneLine.eq_of_two_points (L M : HalfPlaneLine) {z w : ℍ} (hzw : z ≠ w)
    (hzL : z ∈ L.carrier) (hwL : w ∈ L.carrier)
    (hzM : z ∈ M.carrier) (hwM : w ∈ M.carrier) : L = M := by
  cases L with
  | vertical x =>
    cases M with
    | vertical y =>
      change z.re = x at hzL
      change z.re = y at hzM
      exact congrArg HalfPlaneLine.vertical (hzL.symm.trans hzM)
    | circle c r hr =>
      change z.re = x at hzL
      change w.re = x at hwL
      exact (hzw (eq_of_circle_mem_of_re_eq hzM hwM (hzL.trans hwL.symm))).elim
  | circle c r hr =>
    cases M with
    | vertical x =>
      change z.re = x at hzM
      change w.re = x at hwM
      exact (hzw (eq_of_circle_mem_of_re_eq hzL hwL (hzM.trans hwM.symm))).elim
    | circle d s hs =>
      have hzr := norm_sub_real_eq_radius_sq hzL
      have hwr := norm_sub_real_eq_radius_sq hwL
      have hzs := norm_sub_real_eq_radius_sq hzM
      have hws := norm_sub_real_eq_radius_sq hwM
      have hre : z.re ≠ w.re := fun h => hzw (eq_of_circle_mem_of_re_eq hzL hwL h)
      have hmul : (c - d) * (z.re - w.re) = 0 := by nlinarith
      have hcd : c = d := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hre))
      have hrs : r = s := by rw [hcd] at hzr; nlinarith
      subst d
      subst s
      rfl

/-- Every pair of distinct interior points belongs to an actual Euclidean h-line. -/
theorem exists_halfPlaneLine_through (z w : ℍ) (hzw : z ≠ w) :
    ∃ L : HalfPlaneLine, z ∈ L.carrier ∧ w ∈ L.carrier := by
  obtain ⟨a, b, g, _, _, _, hg, _, _, hz, hw, _⟩ := exists_ordered_ideal_normalizer z w hzw
  obtain ⟨L, hL⟩ := exists_halfPlaneLine_of_isHLine (realMobius_axis_preimage_isHLine g hg)
  exact ⟨L, by rw [hL]; exact hz, by rw [hL]; exact hw⟩

/-- The h-line through two distinct points is unique. -/
theorem existsUnique_halfPlaneLine_through (z w : ℍ) (hzw : z ≠ w) :
    ∃! L : HalfPlaneLine, z ∈ L.carrier ∧ w ∈ L.carrier := by
  obtain ⟨L, hz, hw⟩ := exists_halfPlaneLine_through z w hzw
  exact ⟨L, ⟨hz, hw⟩, fun M hM => M.eq_of_two_points L hzw hM.1 hM.2 hz hw⟩

/-- distinct h-lines have at most one interior intersection point. -/
theorem HalfPlaneLine.inter_subsingleton {L M : HalfPlaneLine} (hLM : L ≠ M) :
    (L.carrier ∩ M.carrier).Subsingleton := by
  intro z hz w hw
  by_contra hzw
  exact hLM (L.eq_of_two_points M hzw hz.1 hw.1 hz.2 hw.2)

/-- The positive-determinant real map sending the endpoints `a < b` to zero and infinity. -/
def intervalNormalizer (a b : ℝ) (hab : a < b) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, -a; -1, b]
    (by simp [Matrix.det_fin_two]; linarith)

theorem intervalNormalizer_pos (a b : ℝ) (hab : a < b) :
    0 < (intervalNormalizer a b hab).val.det := by
  simp [intervalNormalizer, Matrix.det_fin_two]
  linarith

/-- The exact real polynomial test for the image lying on the imaginary axis. -/
theorem realMobius_re_zero_iff (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (z : ℍ) :
    (g • z).re = 0 ↔ (g 0 0 * z.re + g 0 1) * (g 1 0 * z.re + g 1 1) +
      g 0 0 * g 1 0 * z.im ^ 2 = 0 := by
  have hd := UpperHalfPlane.denom_ne_zero g z
  change (g 1 0 : ℂ) * z + g 1 1 ≠ 0 at hd
  rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_smul_of_det_pos (by simpa using hg)]
  exact real_fractional_re_zero_iff (g 0 0) (g 0 1) (g 1 0) (g 1 1) z hd

/-- The actual interval normalizer sends a real-centred semicircle precisely onto the imaginary axis. -/
theorem intervalNormalizer_circle_re_zero_iff (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    (intervalNormalizer (c - r) (c + r) (by linarith) • z).re = 0 ↔
      ‖(z : ℂ) - (c : ℂ)‖ = r := by
  rw [realMobius_re_zero_iff _ (intervalNormalizer_pos _ _ _)]
  change (1 * z.re + -(c - r)) * (-1 * z.re + (c + r)) + 1 * (-1) * z.im ^ 2 = 0 ↔ _
  rw [← sq_eq_sq₀ (norm_nonneg _) hr.le, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  constructor <;> intro h <;> nlinarith

/-- Every actual h-line has a genuine positive-determinant real Möbius normalizer. -/
theorem HalfPlaneLine.exists_normalizer (L : HalfPlaneLine) :
    ∃ g : GL (Fin 2) ℝ, 0 < g.val.det ∧ L.carrier = {z : ℍ | (g • z).re = 0} := by
  cases L with
  | vertical x =>
    refine ⟨Matrix.SpecialLinearGroup.mapGL ℝ (horizontalNormalizer x), by simp, ?_⟩
    ext z
    change z.re = x ↔ (horizontalNormalizer x • z).re = 0
    rw [horizontalNormalizer_re]
    exact sub_eq_zero.symm
  | circle c r hr =>
    refine ⟨intervalNormalizer (c - r) (c + r) (by linarith), intervalNormalizer_pos _ _ _, ?_⟩
    ext z
    exact (intervalNormalizer_circle_re_zero_iff c r hr z).symm

/-- Every actual h-line is the complete range of a unit-speed real isometric parametrization. -/
theorem HalfPlaneLine.exists_isometric_param (L : HalfPlaneLine) :
    ∃ γ : ℝ → ℍ, Isometry γ ∧ Set.range γ = L.carrier := by
  obtain ⟨g, hg, hL⟩ := L.exists_normalizer
  refine ⟨normalizerGeodesic g, normalizerGeodesic_isometry g hg, ?_⟩
  rw [range_normalizerGeodesic, ← hL]

/-- Every h-line contains two different interior points. -/
theorem HalfPlaneLine.exists_two_points (L : HalfPlaneLine) :
    ∃ z w : ℍ, z ∈ L.carrier ∧ w ∈ L.carrier ∧ z ≠ w := by
  obtain ⟨γ, hγ, hrange⟩ := L.exists_isometric_param
  refine ⟨γ 0, γ 1, ?_, ?_, ?_⟩
  · rw [← hrange]
    exact Set.mem_range_self 0
  · rw [← hrange]
    exact Set.mem_range_self 1
  · intro he
    exact zero_ne_one (hγ.injective he)

/-- Euclidean h-line parameters are uniquely determined by their actual point set. -/
theorem HalfPlaneLine.carrier_injective : Function.Injective HalfPlaneLine.carrier := by
  intro L M h
  obtain ⟨z, w, hz, hw, hzw⟩ := L.exists_two_points
  exact L.eq_of_two_points M hzw hz hw (h ▸ hz) (h ▸ hw)

/-- Positive determinant is preserved by multiplication. -/
theorem gl_pos_mul (g h : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (hh : 0 < h.val.det) :
    0 < (g * h).val.det := by
  change 0 < (g.val * h.val).det
  rw [Matrix.det_mul]
  exact mul_pos hg hh

/-- A real Möbius isometry carries any h-line onto any other one. -/
theorem HalfPlaneLine.exists_mobius_map (L M : HalfPlaneLine) :
    ∃ g : GL (Fin 2) ℝ, 0 < g.val.det ∧ (fun z : ℍ => g • z) '' L.carrier = M.carrier := by
  obtain ⟨l, hl, hL⟩ := L.exists_normalizer
  obtain ⟨m, hm, hM⟩ := M.exists_normalizer
  refine ⟨m⁻¹ * l, gl_pos_mul _ _ (gl_pos_inverse m hm) hl, ?_⟩
  rw [hL, hM]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change (l • w).re = 0 at hw
    change (m • ((m⁻¹ * l) • w)).re = 0
    simpa only [mul_smul, smul_inv_smul] using hw
  · intro hz
    change (m • z).re = 0 at hz
    refine ⟨l⁻¹ • (m • z), ?_, ?_⟩
    · change (l • (l⁻¹ • (m • z))).re = 0
      simpa only [smul_inv_smul] using hz
    · simp only [mul_smul, smul_inv_smul, inv_smul_smul]

theorem imaginaryAxisReflection_re (z : ℍ) : (UpperHalfPlane.J • z).re = -z.re := by
  change ((UpperHalfPlane.J • z : ℍ) : ℂ).re = _
  rw [UpperHalfPlane.coe_J_smul]
  simp

theorem imaginaryAxisReflection_im (z : ℍ) : (UpperHalfPlane.J • z).im = z.im := by
  change ((UpperHalfPlane.J • z : ℍ) : ℂ).im = _
  rw [UpperHalfPlane.coe_J_smul]
  simp

/-- The actual reflection in the imaginary axis is an isometry of the genuine hyperbolic metric. -/
theorem imaginaryAxisReflection_isometry : Isometry (fun z : ℍ => UpperHalfPlane.J • z) := by
  apply Isometry.of_dist_eq
  intro z w
  apply Real.cosh_injOn dist_nonneg dist_nonneg
  rw [halfPlane_cosh_dist_eq_norm_sq_formula, halfPlane_cosh_dist_eq_norm_sq_formula,
    imaginaryAxisReflection_im, imaginaryAxisReflection_im]
  have hn : ‖((UpperHalfPlane.J • z : ℍ) : ℂ) - (UpperHalfPlane.J • w : ℍ)‖ =
      ‖(z : ℂ) - w‖ := by
    rw [UpperHalfPlane.coe_J_smul, UpperHalfPlane.coe_J_smul]
    calc
      _ = ‖-(conj ((z : ℂ) - w))‖ := by congr 1; simp only [map_sub]; ring
      _ = _ := by rw [norm_neg, Complex.norm_conj]
  rw [hn]

/-- The actual `GL₂(ℝ)` action, including its antiholomorphic branch, consists of isometries. -/
theorem realGL_isometry (g : GL (Fin 2) ℝ) : Isometry (fun z : ℍ => g • z) := by
  by_cases hg : 0 < g.val.det
  · exact Isometry.of_dist_eq (metric_distance_gl_pos g hg)
  have hneg : g.val.det < 0 := lt_of_le_of_ne (not_lt.mp hg) g.det_ne_zero
  have hJ : UpperHalfPlane.J.val.det = -1 := by simp [UpperHalfPlane.J, Matrix.det_fin_two]
  have hpos : 0 < (UpperHalfPlane.J * g).val.det := by
    change 0 < (UpperHalfPlane.J.val * g.val).det
    rw [Matrix.det_mul, hJ]
    linarith
  apply Isometry.of_dist_eq
  intro z w
  have h := metric_distance_gl_pos (UpperHalfPlane.J * g) hpos z w
  simpa only [mul_smul, imaginaryAxisReflection_isometry.dist_eq] using h

/-- Distance invariance for the actual holomorphic and antiholomorphic real matrix actions. -/
theorem realGL_distance (g : GL (Fin 2) ℝ) (z w : ℍ) : dist (g • z) (g • w) = dist z w :=
  (realGL_isometry g).dist_eq z w

/-- The actual negative-determinant branch is the conjugate fractional-linear formula. -/
theorem realGL_coe_of_det_neg (g : GL (Fin 2) ℝ) (hg : g.val.det < 0) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = conj (((g 0 0 : ℂ) * z + g 0 1) / ((g 1 0 : ℂ) * z + g 1 1)) := by
  have hnot : ¬0 < g.det.val := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply] using not_lt_of_ge hg.le
  rw [UpperHalfPlane.coe_smul, UpperHalfPlane.σ, ite_eq_right hnot]
  rfl

/-- Matrix of the genuine reflection in the vertical line of real coordinate `x`. -/
def verticalReflectionMatrix (x : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 2 * x; 0, 1] (by simp [Matrix.det_fin_two])

theorem verticalReflectionMatrix_det (x : ℝ) : (verticalReflectionMatrix x).val.det = -1 := by
  simp [verticalReflectionMatrix, Matrix.det_fin_two]

/-- Matrix of reflection in the real-centred circle with radius `r`. -/
def circleReflectionMatrix (c r : ℝ) (hr : 0 < r) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, r ^ 2 - c ^ 2; 1, -c]
    (by
      rw [Matrix.det_fin_two]
      change c * (-c) - (r ^ 2 - c ^ 2) * 1 ≠ 0
      nlinarith [sq_pos_of_pos hr])

theorem circleReflectionMatrix_det (c r : ℝ) (hr : 0 < r) :
    (circleReflectionMatrix c r hr).val.det = -(r ^ 2) := by
  change (!![c, r ^ 2 - c ^ 2; 1, -c] : Matrix (Fin 2) (Fin 2) ℝ).det = -(r ^ 2)
  rw [Matrix.det_fin_two]
  change c * (-c) - (r ^ 2 - c ^ 2) * 1 = -(r ^ 2)
  ring

/-- Vertical reflection, acting on the actual half-plane. -/
def verticalReflection (x : ℝ) (z : ℍ) : ℍ := verticalReflectionMatrix x • z

/-- Circle inversion, acting on the actual half-plane. -/
def circleReflection (c r : ℝ) (hr : 0 < r) (z : ℍ) : ℍ := circleReflectionMatrix c r hr • z

theorem verticalReflection_coe (x : ℝ) (z : ℍ) :
    (verticalReflection x z : ℂ) = (2 * x : ℝ) - conj (z : ℂ) := by
  rw [verticalReflection, realGL_coe_of_det_neg _ (by rw [verticalReflectionMatrix_det]; norm_num)]
  change conj ((((-1 : ℝ) : ℂ) * z + ((2 * x : ℝ) : ℂ)) /
    (((0 : ℝ) : ℂ) * z + ((1 : ℝ) : ℂ))) = _
  simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, zero_add, div_one,
    map_add, map_neg, Complex.conj_ofReal, Complex.ofReal_neg, neg_one_mul]
  ring

/-- A conjugated upper-half-plane point never lies on the real axis. -/
theorem conj_sub_real_ne_zero (c : ℝ) (z : ℍ) : conj (z : ℂ) - (c : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, Complex.ofReal_im, sub_zero,
    UpperHalfPlane.coe_im, Complex.zero_im] at hi
  linarith [z.im_pos]

/-- The finite formula is the actual Euclidean inversion in the real-centred circle. -/
theorem circleReflection_coe (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    (circleReflection c r hr z : ℂ) = (c : ℂ) + (r : ℂ) ^ 2 / (conj (z : ℂ) - (c : ℂ)) := by
  rw [circleReflection, realGL_coe_of_det_neg _
    (by rw [circleReflectionMatrix_det]; nlinarith)]
  change conj (((c : ℂ) * z + ((r ^ 2 - c ^ 2 : ℝ) : ℂ)) /
    (((1 : ℝ) : ℂ) * z + ((-c : ℝ) : ℂ))) = _
  have hz : (z : ℂ) - (c : ℂ) ≠ 0 := by
    intro h
    apply conj_sub_real_ne_zero c z
    simpa only [map_sub, Complex.conj_ofReal, map_zero] using congrArg conj h
  have he : ((c : ℂ) * z + ((r : ℂ) ^ 2 - (c : ℂ) ^ 2)) / ((z : ℂ) - (c : ℂ)) =
      (c : ℂ) + (r : ℂ) ^ 2 / ((z : ℂ) - (c : ℂ)) := by
    apply (div_eq_iff hz).mpr
    rw [add_mul, div_mul_cancel₀ _ hz]
    ring
  simp only [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, one_mul, ← sub_eq_add_neg]
  rw [he]
  simp only [map_add, map_div₀, map_pow, map_sub, Complex.conj_ofReal]

/-- For a vertical h-line. -/
theorem verticalReflection_isometry (x : ℝ) : Isometry (verticalReflection x) :=
  realGL_isometry (verticalReflectionMatrix x)

/-- For a real-centred semicircle. -/
theorem circleReflection_isometry (c r : ℝ) (hr : 0 < r) : Isometry (circleReflection c r hr) :=
  realGL_isometry (circleReflectionMatrix c r hr)

/-- Reflection in either of the two genuine Euclidean h-line presentations. -/
def HalfPlaneLine.reflection : HalfPlaneLine → ℍ → ℍ
  | .vertical x => verticalReflection x
  | .circle c r hr => circleReflection c r hr

/-- Every actual h-line reflection is an isometry, including circle inversion. -/
theorem HalfPlaneLine.reflection_isometry (L : HalfPlaneLine) : Isometry L.reflection := by
  cases L with
  | vertical x => exact verticalReflection_isometry x
  | circle c r hr => exact circleReflection_isometry c r hr

end

end LowDimensionalTopology.Geometry.Hyperbolic
