module

public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Real affine geometry of the complex plane

The complex plane is a two-dimensional real inner product space. A nonzero
vector and its quarter-turn span the plane. We use this decomposition to
describe orthogonal vectors, and prove that nontrivial affine equations
through the same two distinct points define the same line.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LowDimensionalTopology.Geometry.Euclidean

/-- A nonzero complex vector and its quarter-turn span the complex plane over the reals. -/
theorem complex_basis_direction_representation (v z : ℂ) (hv : v ≠ 0) :
    ∃ s t : ℝ, z = s • v + t • (Complex.I * v) := by
  refine ⟨(z / v).re, (z / v).im, ?_⟩
  calc
    z = (z / v) * v := (div_mul_cancel₀ z hv).symm
    _ = (((z / v).re : ℂ) + ((z / v).im : ℂ) * Complex.I) * v := by
      rw [Complex.re_add_im]
    _ = _ := by simp only [Complex.real_smul]; ring

/-- Two nontrivial real affine equations through the same two distinct points
define the same line. -/
theorem complex_affine_equations_iff_of_two_points {n m u v x : ℂ} {t s : ℝ}
    (hn : n ≠ 0) (hm : m ≠ 0) (huv : u ≠ v)
    (hnu : inner ℝ n u = t) (hnv : inner ℝ n v = t)
    (hmu : inner ℝ m u = s) (hmv : inner ℝ m v = s) :
    inner ℝ n x = t ↔ inner ℝ m x = s := by
  have core (n m d r : ℂ) (hn : n ≠ 0) (hd : d ≠ 0)
      (hnd : inner ℝ n d = 0) (hmd : inner ℝ m d = 0) (hnr : inner ℝ n r = 0) :
      inner ℝ m r = 0 := by
    simp only [complex_real_inner_coordinates] at hnd hmd hnr ⊢
    by_cases hdre : d.re = 0
    · have hdim : d.im ≠ 0 := by intro h; exact hd (Complex.ext hdre h)
      have hnim : n.im = 0 := by
        rw [hdre, mul_zero, zero_add] at hnd
        exact (mul_eq_zero.mp hnd).resolve_right hdim
      have hmim : m.im = 0 := by
        rw [hdre, mul_zero, zero_add] at hmd
        exact (mul_eq_zero.mp hmd).resolve_right hdim
      have hnre : n.re ≠ 0 := by intro h; exact hn (Complex.ext h hnim)
      have hrre : r.re = 0 := by
        rw [hnim, zero_mul, add_zero] at hnr
        exact (mul_eq_zero.mp hnr).resolve_left hnre
      rw [hrre, hmim, mul_zero, zero_mul, add_zero]
    · have hnim : n.im ≠ 0 := by
        intro h
        rw [h, zero_mul, add_zero] at hnd
        exact hn (Complex.ext ((mul_eq_zero.mp hnd).resolve_right hdre) h)
      have he : (m.re * r.re + m.im * r.im) * (n.im * d.re) = 0 := by
        linear_combination r.re * n.im * hmd - r.re * m.im * hnd + m.im * d.re * hnr
      exact (mul_eq_zero.mp he).resolve_right (mul_ne_zero hnim hdre)
  have hnd : inner ℝ n (v - u) = 0 := by rw [inner_sub_right, hnv, hnu, sub_self]
  have hmd : inner ℝ m (v - u) = 0 := by rw [inner_sub_right, hmv, hmu, sub_self]
  constructor
  · intro hx
    have hr : inner ℝ n (x - u) = 0 := by rw [inner_sub_right, hx, hnu, sub_self]
    have he := core n m (v - u) (x - u) hn (sub_ne_zero.mpr huv.symm) hnd hmd hr
    rw [inner_sub_right, hmu] at he
    exact sub_eq_zero.mp he
  · intro hx
    have hr : inner ℝ m (x - u) = 0 := by rw [inner_sub_right, hx, hmu, sub_self]
    have he := core m n (v - u) (x - u) hm (sub_ne_zero.mpr huv.symm) hmd hnd hr
    rw [inner_sub_right, hnu] at he
    exact sub_eq_zero.mp he

/-- A vector orthogonal to a nonzero complex vector is a real multiple of its quarter-turn. -/
theorem complex_orthogonal_eq_real_smul (n z : ℂ) (hn : n ≠ 0) (hz : inner ℝ n z = 0) :
    ∃ t : ℝ, z = t • (Complex.I * n) := by
  obtain ⟨s, t, he⟩ := complex_basis_direction_representation n z hn
  have horth : inner ℝ n (Complex.I * n) = 0 := by simp [Complex.inner]; ring
  have hpos : 0 < inner ℝ n n := real_inner_self_pos.mpr hn
  rw [he, inner_add_right, real_inner_smul_right, real_inner_smul_right, horth,
    mul_zero, add_zero] at hz
  have hs : s = 0 := (mul_eq_zero.mp hz).resolve_right hpos.ne'
  exact ⟨t, by rw [he, hs, zero_smul, zero_add]⟩

end LowDimensionalTopology.Geometry.Euclidean
