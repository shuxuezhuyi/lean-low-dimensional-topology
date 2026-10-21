/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.Geodesic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Tactic

/-!
# The unique perpendicular through an arbitrary point

Orthogonality uses the actual real Euclidean inner product of the canonical
nonzero tangent vectors at an actual intersection point. Coefficient tests are
proved equivalent to this geometric condition before being used to construct
the perpendicular.
-/

@[expose] public section

open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section


theorem complex_real_inner_mul_I (z w : ℂ) :
    inner ℝ (Complex.I * z) (Complex.I * w) = inner ℝ z w := by
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,
    _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, zero_add]
  ring

/-- The actual canonical Euclidean tangent to a vertical line or a real-centred circle. -/
def HalfPlaneLine.tangentAt : HalfPlaneLine → ℍ → ℂ
  | .vertical _ => fun _ => Complex.I
  | .circle c _ _ => fun z => Complex.I * ((z : ℂ) - (c : ℂ))

/-- Euclidean orthogonality of the actual tangents at an actual common interior point. -/
def HalfPlaneLine.OrthogonalAt (L M : HalfPlaneLine) (z : ℍ) : Prop :=
  z ∈ L.carrier ∧ z ∈ M.carrier ∧ inner ℝ (L.tangentAt z) (M.tangentAt z) = 0

/-- Two h-lines are orthogonal when their actual tangent vectors are perpendicular where they meet. -/
def HalfPlaneLine.Orthogonal (L M : HalfPlaneLine) : Prop := ∃ z, L.OrthogonalAt M z

/-- An algebraic criterion, subsequently proved equivalent to geometric orthogonality. -/
def HalfPlaneLine.OrthogonalCoefficients : HalfPlaneLine → HalfPlaneLine → Prop
  | .vertical _, .vertical _ => False
  | .vertical x, .circle c _ _ => x = c
  | .circle c _ _, .vertical x => c = x
  | .circle c r _, .circle d s _ => (c - d) ^ 2 = r ^ 2 + s ^ 2

theorem HalfPlaneLine.orthogonalAt_iff_coefficients (L M : HalfPlaneLine) (z : ℍ)
    (hzL : z ∈ L.carrier) (hzM : z ∈ M.carrier) :
    L.OrthogonalAt M z ↔ L.OrthogonalCoefficients M := by
  change (z ∈ L.carrier ∧ z ∈ M.carrier ∧ _) ↔ _
  simp only [hzL, hzM, true_and]
  cases L with
  | vertical x =>
    cases M with
    | vertical y =>
      change inner ℝ Complex.I Complex.I = 0 ↔ False
      simp
    | circle c r hr =>
      change inner ℝ Complex.I (Complex.I * ((z : ℂ) - (c : ℂ))) = 0 ↔ x = c
      change z.re = x at hzL
      have he : inner ℝ Complex.I (Complex.I * ((z : ℂ) - (c : ℂ))) =
          inner ℝ (1 : ℂ) ((z : ℂ) - (c : ℂ)) := by
        simpa only [mul_one] using complex_real_inner_mul_I (1 : ℂ) ((z : ℂ) - (c : ℂ))
      rw [he, _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
      simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, add_zero, Complex.sub_re,
        Complex.ofReal_re, UpperHalfPlane.coe_re, hzL]
      exact sub_eq_zero
  | circle c r hr =>
    cases M with
    | vertical x =>
      change inner ℝ (Complex.I * ((z : ℂ) - (c : ℂ))) Complex.I = 0 ↔ c = x
      change z.re = x at hzM
      have he : inner ℝ (Complex.I * ((z : ℂ) - (c : ℂ))) Complex.I =
          inner ℝ ((z : ℂ) - (c : ℂ)) (1 : ℂ) := by
        simpa only [mul_one] using complex_real_inner_mul_I ((z : ℂ) - (c : ℂ)) (1 : ℂ)
      rw [he, _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
      simp only [Complex.one_re, Complex.one_im, mul_one, mul_zero, add_zero, Complex.sub_re,
        Complex.ofReal_re, UpperHalfPlane.coe_re, hzM]
      exact sub_eq_zero.trans eq_comm
    | circle d s hs =>
      change inner ℝ (Complex.I * ((z : ℂ) - (c : ℂ)))
        (Complex.I * ((z : ℂ) - (d : ℂ))) = 0 ↔ (c - d) ^ 2 = r ^ 2 + s ^ 2
      rw [complex_real_inner_mul_I, _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      have hL := norm_sub_real_eq_radius_sq hzL
      have hM := norm_sub_real_eq_radius_sq hzM
      constructor <;> intro h <;> nlinarith

/-- A positive radius is recovered from its exact squared Euclidean circle equation. -/
theorem norm_sub_real_eq_of_sq {c r : ℝ} (hr : 0 < r) {z : ℍ}
    (h : (z.re - c) ^ 2 + z.im ^ 2 = r ^ 2) : ‖(z : ℂ) - (c : ℂ)‖ = r := by
  rw [← sq_eq_sq₀ (norm_nonneg _) hr.le, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  nlinarith

/-- Two positive-radius circles satisfying the orthogonality equation actually meet in the upper half-plane. -/
theorem exists_orthogonal_circle_intersection (c r d s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (horth : (c - d) ^ 2 = r ^ 2 + s ^ 2) :
    ∃ z : ℍ, ‖(z : ℂ) - (c : ℂ)‖ = r ∧ ‖(z : ℂ) - (d : ℂ)‖ = s := by
  let D := d - c
  have hDsq : D ^ 2 = r ^ 2 + s ^ 2 := by dsimp [D]; nlinarith
  have hD : D ≠ 0 := by intro h; rw [h] at hDsq; nlinarith
  let x := c + r ^ 2 / D
  let y := r * s / |D|
  have hy : 0 < y := div_pos (mul_pos hr hs) (abs_pos.mpr hD)
  have hy2 : y ^ 2 = r ^ 2 * s ^ 2 / D ^ 2 := by
    dsimp [y]
    rw [div_pow, mul_pow, sq_abs]
  have hxc : x - c = r ^ 2 / D := by dsimp [x]; ring
  have hxd : x - d = -(s ^ 2) / D := by
    apply (eq_div_iff hD).mpr
    have hrel : (x - d) * D = (x - c) * D - D ^ 2 := by dsimp [D]; ring
    rw [hrel, hxc, div_mul_cancel₀ _ hD, hDsq]
    ring
  have hC : (x - c) ^ 2 + y ^ 2 = r ^ 2 := by
    rw [hxc, div_pow, hy2]
    calc
      _ = r ^ 2 * (r ^ 2 + s ^ 2) / D ^ 2 := by ring
      _ = r ^ 2 := by rw [← hDsq]; exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hD)
  have hD' : (x - d) ^ 2 + y ^ 2 = s ^ 2 := by
    rw [hxd, div_pow, neg_sq, hy2]
    calc
      _ = s ^ 2 * (r ^ 2 + s ^ 2) / D ^ 2 := by ring
      _ = s ^ 2 := by rw [← hDsq]; exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hD)
  exact ⟨UpperHalfPlane.mk ⟨x, y⟩ hy, norm_sub_real_eq_of_sq hr hC,
    norm_sub_real_eq_of_sq hs hD'⟩

/-- The coefficient criterion is equivalent to genuine Euclidean tangent orthogonality. -/
theorem HalfPlaneLine.orthogonal_iff_coefficients (L M : HalfPlaneLine) :
    L.Orthogonal M ↔ L.OrthogonalCoefficients M := by
  constructor
  · rintro ⟨z, hzL, hzM, hi⟩
    exact (L.orthogonalAt_iff_coefficients M z hzL hzM).mp ⟨hzL, hzM, hi⟩
  · intro h
    cases L with
    | vertical x =>
      cases M with
      | vertical y => exact h.elim
      | circle c r hr =>
        change x = c at h
        subst x
        let z := UpperHalfPlane.mk ⟨c, r⟩ hr
        have hzL : z ∈ (HalfPlaneLine.vertical c).carrier := rfl
        have hzM : z ∈ (HalfPlaneLine.circle c r hr).carrier := by
          apply norm_sub_real_eq_of_sq hr
          change (c - c) ^ 2 + r ^ 2 = r ^ 2
          ring
        exact ⟨z, ((HalfPlaneLine.vertical c).orthogonalAt_iff_coefficients
          (.circle c r hr) z hzL hzM).mpr rfl⟩
    | circle c r hr =>
      cases M with
      | vertical x =>
        change c = x at h
        subst x
        let z := UpperHalfPlane.mk ⟨c, r⟩ hr
        have hzL : z ∈ (HalfPlaneLine.circle c r hr).carrier := by
          apply norm_sub_real_eq_of_sq hr
          change (c - c) ^ 2 + r ^ 2 = r ^ 2
          ring
        have hzM : z ∈ (HalfPlaneLine.vertical c).carrier := rfl
        exact ⟨z, ((HalfPlaneLine.circle c r hr).orthogonalAt_iff_coefficients
          (.vertical c) z hzL hzM).mpr rfl⟩
      | circle d s hs =>
        obtain ⟨z, hzL, hzM⟩ := exists_orthogonal_circle_intersection c r d s hr hs h
        exact ⟨z, ((HalfPlaneLine.circle c r hr).orthogonalAt_iff_coefficients
          (.circle d s hs) z hzL hzM).mpr h⟩

/-- A genuine upper-half-plane point is at positive Euclidean distance from every real centre. -/
theorem norm_sub_real_pos (c : ℝ) (w : ℍ) : 0 < ‖(w : ℂ) - (c : ℂ)‖ := by
  apply norm_pos_iff.mpr
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im,
    UpperHalfPlane.coe_im] at hi
  linarith [w.im_pos]

/-- The canonical tangent used in the definition is always nonzero. -/
theorem HalfPlaneLine.tangentAt_ne_zero (L : HalfPlaneLine) (z : ℍ) : L.tangentAt z ≠ 0 := by
  cases L with
  | vertical x => exact Complex.I_ne_zero
  | circle c r hr =>
    exact mul_ne_zero Complex.I_ne_zero (norm_ne_zero_iff.mp (norm_sub_real_pos c z).ne')

/-- A genuine smooth Euclidean parametrization realizing the specified tangent. -/
def HalfPlaneLine.tangentCurve : HalfPlaneLine → ℍ → ℝ → ℂ
  | .vertical _, z => fun t => (z : ℂ) + (t : ℂ) * Complex.I
  | .circle c _ _, z => fun t => (c : ℂ) + ((z : ℂ) - (c : ℂ)) *
      Complex.exp ((t : ℂ) * Complex.I)

theorem HalfPlaneLine.tangentCurve_zero (L : HalfPlaneLine) (z : ℍ) :
    L.tangentCurve z 0 = (z : ℂ) := by
  cases L <;> simp [HalfPlaneLine.tangentCurve]

/-- The nonzero canonical tangent is the actual derivative of this circle or line curve. -/
theorem HalfPlaneLine.tangentCurve_hasDerivAt (L : HalfPlaneLine) (z : ℍ) :
    HasDerivAt (L.tangentCurve z) (L.tangentAt z) 0 := by
  have hi := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I
  cases L with
  | vertical x =>
    simpa [HalfPlaneLine.tangentCurve, HalfPlaneLine.tangentAt] using hi.const_add (z : ℂ)
  | circle c r hr =>
    simpa [HalfPlaneLine.tangentCurve, HalfPlaneLine.tangentAt, mul_comm] using
      (hi.cexp.const_mul ((z : ℂ) - (c : ℂ))).const_add (c : ℂ)

/-- Every point of the circle parametrization remains on the original Euclidean circle. -/
theorem tangentCurve_circle_norm (c r : ℝ) (hr : 0 < r) (z : ℍ)
    (hz : z ∈ (HalfPlaneLine.circle c r hr).carrier) (t : ℝ) :
    ‖(HalfPlaneLine.circle c r hr).tangentCurve z t - (c : ℂ)‖ = r := by
  change ‖(c : ℂ) + ((z : ℂ) - (c : ℂ)) * Complex.exp ((t : ℂ) * Complex.I) -
    (c : ℂ)‖ = r
  rw [add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact hz

/-- The centre of a perpendicular circle through `w` satisfies one explicit real linear equation. -/
theorem perpendicular_circle_center_equation {c r d s : ℝ} {w : ℍ}
    (hw : ‖(w : ℂ) - (d : ℂ)‖ = s) (ho : (c - d) ^ 2 = r ^ 2 + s ^ 2) :
    2 * d * (w.re - c) = r ^ 2 + w.re ^ 2 + w.im ^ 2 - c ^ 2 := by
  have hs := norm_sub_real_eq_radius_sq hw
  nlinarith

/-- A unique perpendicular through any point, first in the proved equivalent coefficient presentation. -/
theorem HalfPlaneLine.existsUnique_perpendicular_coefficients (L : HalfPlaneLine) (w : ℍ) :
    ∃! M : HalfPlaneLine, w ∈ M.carrier ∧ L.OrthogonalCoefficients M := by
  cases L with
  | vertical x =>
    let R := ‖(w : ℂ) - (x : ℂ)‖
    have hR : 0 < R := norm_sub_real_pos x w
    refine ⟨.circle x R hR, ⟨rfl, rfl⟩, ?_⟩
    intro M hM
    rcases hM with ⟨hw, ho⟩
    cases M with
    | vertical y => exact ho.elim
    | circle c r hr =>
      change x = c at ho
      subst c
      have hrR : r = R := hw.symm
      congr 1
  | circle c r hr =>
    by_cases hwr : w.re = c
    · refine ⟨.vertical c, ⟨hwr, rfl⟩, ?_⟩
      intro M hM
      rcases hM with ⟨hw, ho⟩
      cases M with
      | vertical x =>
        change c = x at ho
        exact congrArg HalfPlaneLine.vertical ho.symm
      | circle d s hs =>
        have he := perpendicular_circle_center_equation hw ho
        rw [hwr] at he
        nlinarith [sq_pos_of_pos hr, sq_nonneg w.im]
    · let d := (r ^ 2 + w.re ^ 2 + w.im ^ 2 - c ^ 2) / (2 * (w.re - c))
      let s := ‖(w : ℂ) - (d : ℂ)‖
      have hs : 0 < s := norm_sub_real_pos d w
      have hden : 2 * (w.re - c) ≠ 0 := mul_ne_zero (by norm_num) (sub_ne_zero.mpr hwr)
      have hd : 2 * d * (w.re - c) = r ^ 2 + w.re ^ 2 + w.im ^ 2 - c ^ 2 := by
        have he : d * (2 * (w.re - c)) = r ^ 2 + w.re ^ 2 + w.im ^ 2 - c ^ 2 :=
          div_mul_cancel₀ _ hden
        nlinarith
      have hsq := norm_sub_real_eq_radius_sq (show ‖(w : ℂ) - (d : ℂ)‖ = s by rfl)
      have ho : (c - d) ^ 2 = r ^ 2 + s ^ 2 := by nlinarith
      refine ⟨.circle d s hs, ⟨rfl, ho⟩, ?_⟩
      intro M hM
      rcases hM with ⟨hw, hp⟩
      cases M with
      | vertical x =>
        change c = x at hp
        change w.re = x at hw
        exact (hwr (hw.trans hp.symm)).elim
      | circle e t ht =>
        have he := perpendicular_circle_center_equation hw hp
        have hprod : (e - d) * (w.re - c) = 0 := by nlinarith
        have hed : e = d := sub_eq_zero.mp
          ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hwr))
        subst e
        have hts : t = s := hw.symm
        congr 1

/-- Every point lies on exactly one actual h-line perpendicular to the given one. -/
theorem HalfPlaneLine.existsUnique_perpendicular (L : HalfPlaneLine) (w : ℍ) :
    ∃! M : HalfPlaneLine, w ∈ M.carrier ∧ L.Orthogonal M := by
  obtain ⟨M, ⟨hw, ho⟩, huniq⟩ := L.existsUnique_perpendicular_coefficients w
  refine ⟨M, ⟨hw, (L.orthogonal_iff_coefficients M).mpr ho⟩, ?_⟩
  intro N hN
  exact huniq N ⟨hN.1, (L.orthogonal_iff_coefficients N).mp hN.2⟩

end

end LowDimensionalTopology.Geometry.Hyperbolic
