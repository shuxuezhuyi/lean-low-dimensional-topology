module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination

/-!
# Normalized complex lattices and the integral modular action

The normalized period lattice is the actual integer span of 1 and τ.
Nonzero complex scaling carries one complete lattice onto another precisely
when their upper-half-plane parameters are in the same SL(2,Z) orbit.
No marking, torus quotient or analytic classification is assumed here.
-/

@[expose] public section
noncomputable section

open Set Matrix
open scoped ComplexConjugate MatrixGroups

namespace LowDimensionalTopology.Geometry.Surfaces

/-- The actual normalized lattice Z + Z τ. -/
def normalizedPeriodLattice (τ : UpperHalfPlane) : Submodule ℤ ℂ :=
  Submodule.span ℤ ({1, (τ : ℂ)} : Set ℂ)

@[simp]
theorem mem_normalizedPeriodLattice (τ : UpperHalfPlane) (z : ℂ) :
    z ∈ normalizedPeriodLattice τ ↔
      ∃ m n : ℤ, (m : ℂ) + (n : ℂ) * (τ : ℂ) = z := by
  simp only [normalizedPeriodLattice, Submodule.mem_span_pair, zsmul_eq_mul, mul_one]

/-- Positive imaginary part makes the two real, hence integer, coordinates unique. -/
private theorem normalized_coeff_unique (τ : UpperHalfPlane) (m n p q : ℤ)
    (h : (m : ℂ) + (n : ℂ) * (τ : ℂ) =
      (p : ℂ) + (q : ℂ) * (τ : ℂ)) : m = p ∧ n = q := by
  have hi : (n : ℝ) * τ.im = (q : ℝ) * τ.im := by
    simpa only [Complex.add_im, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, UpperHalfPlane.coe_im, zero_mul, add_zero, zero_add] using
        congrArg Complex.im h
  have hn : n = q := by exact_mod_cast mul_right_cancel₀ τ.im_ne_zero hi
  subst q
  have hm : m = p := by exact_mod_cast add_right_cancel h
  exact ⟨hm, rfl⟩

/-- Integer inverse coordinates force determinant to be an integer unit. -/
private theorem det_unit_of_coeff_inverse (m n p q r s t u : ℤ)
    (h00 : m * r + p * s = 1) (h10 : n * r + q * s = 0)
    (h01 : m * t + p * u = 0) (h11 : n * t + q * u = 1) :
    m * q - p * n = 1 ∨ m * q - p * n = -1 := by
  have hAB : (!![m, p; n, q] : Matrix (Fin 2) (Fin 2) ℤ) *
      !![r, t; s, u] = 1 := by
    rw [Matrix.mul_fin_two, h00, h01, h10, h11, Matrix.one_fin_two]
  have hdet : (m * q - p * n) * (r * u - t * s) = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_fin_two_of, Matrix.det_one] using
      congrArg Matrix.det hAB
  exact Int.eq_one_or_neg_one_of_mul_eq_one hdet

/-- Complete lattice transport gives a genuine determinant-one integral matrix.
The inverse lattice transport, rather than just inclusion, is essential. -/
theorem normalizedPeriodLattice_modular_of_scale
    (τ σ : UpperHalfPlane) (α : ℂ) (hα0 : α ≠ 0)
    (hΛ : ∀ z : ℂ, z ∈ normalizedPeriodLattice τ ↔
      α * z ∈ normalizedPeriodLattice σ) :
    ∃ M : SL(2, ℤ), M • τ = σ := by
  have h1τ : (1 : ℂ) ∈ normalizedPeriodLattice τ :=
    (mem_normalizedPeriodLattice τ 1).2 ⟨1, 0, by simp⟩
  have hττ : (τ : ℂ) ∈ normalizedPeriodLattice τ :=
    (mem_normalizedPeriodLattice τ τ).2 ⟨0, 1, by simp⟩
  have h1σ : (1 : ℂ) ∈ normalizedPeriodLattice σ :=
    (mem_normalizedPeriodLattice σ 1).2 ⟨1, 0, by simp⟩
  have hσσ : (σ : ℂ) ∈ normalizedPeriodLattice σ :=
    (mem_normalizedPeriodLattice σ σ).2 ⟨0, 1, by simp⟩
  obtain ⟨m, n, hα⟩ := (mem_normalizedPeriodLattice σ α).1
    (by simpa only [mul_one] using (hΛ 1).1 h1τ)
  obtain ⟨p, q, hατ⟩ := (mem_normalizedPeriodLattice σ (α * τ)).1 ((hΛ τ).1 hττ)
  have hinv : α⁻¹ ∈ normalizedPeriodLattice τ := (hΛ _).2
    (by simpa only [mul_inv_cancel₀ hα0] using h1σ)
  have hinvσ : α⁻¹ * (σ : ℂ) ∈ normalizedPeriodLattice τ := (hΛ _).2
    (by simpa only [← mul_assoc, mul_inv_cancel₀ hα0, one_mul] using hσσ)
  obtain ⟨r, s, hInv⟩ := (mem_normalizedPeriodLattice τ _).1 hinv
  obtain ⟨t, u, hInvσ⟩ := (mem_normalizedPeriodLattice τ _).1 hinvσ
  have hunit1 : (((m * r + p * s : ℤ) : ℂ) +
      ((n * r + q * s : ℤ) : ℂ) * (σ : ℂ)) = 1 := by
    calc
      _ = (r : ℂ) * ((m : ℂ) + (n : ℂ) * σ) +
          (s : ℂ) * ((p : ℂ) + (q : ℂ) * σ) := by push_cast; ring
      _ = α * ((r : ℂ) + (s : ℂ) * τ) := by rw [hα, hατ]; ring
      _ = 1 := by rw [hInv, mul_inv_cancel₀ hα0]
  have hunitσ : (((m * t + p * u : ℤ) : ℂ) +
      ((n * t + q * u : ℤ) : ℂ) * (σ : ℂ)) = σ := by
    calc
      _ = (t : ℂ) * ((m : ℂ) + (n : ℂ) * σ) +
          (u : ℂ) * ((p : ℂ) + (q : ℂ) * σ) := by push_cast; ring
      _ = α * ((t : ℂ) + (u : ℂ) * τ) := by rw [hα, hατ]; ring
      _ = σ := by rw [hInvσ, ← mul_assoc, mul_inv_cancel₀ hα0, one_mul]
  have hc1 := normalized_coeff_unique σ (m * r + p * s) (n * r + q * s) 1 0
    (by simpa only [Int.cast_one, Int.cast_zero, zero_mul, add_zero] using hunit1)
  have hcσ := normalized_coeff_unique σ (m * t + p * u) (n * t + q * u) 0 1
    (by simpa only [Int.cast_zero, Int.cast_one, one_mul, zero_add] using hunitσ)
  have hunit := det_unit_of_coeff_inverse m n p q r s t u hc1.1 hc1.2 hcσ.1 hcσ.2
  have harea : (α.re ^ 2 + α.im ^ 2) * τ.im =
      ((m * q - p * n : ℤ) : ℝ) * σ.im := by
    calc
      _ = (conj α * (α * (τ : ℂ))).im := by
        simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
          UpperHalfPlane.coe_im]
        ring
      _ = (conj ((m : ℂ) + (n : ℂ) * σ) *
          ((p : ℂ) + (q : ℂ) * σ)).im := by rw [hα, hατ]
      _ = _ := by
        simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
          Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
          UpperHalfPlane.coe_im]
        push_cast
        ring
  have hnorm : 0 < α.re ^ 2 + α.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using (Complex.normSq_pos.mpr hα0)
  have hdetposR : 0 < ((m * q - p * n : ℤ) : ℝ) := by
    have hpos : 0 < ((m * q - p * n : ℤ) : ℝ) * σ.im :=
      harea ▸ mul_pos hnorm τ.im_pos
    exact pos_of_mul_pos_left hpos σ.im_pos.le
  have hdetpos : 0 < m * q - p * n := by exact_mod_cast hdetposR
  have hdet : m * q - p * n = 1 := by
    rcases hunit with h | h
    · exact h
    · have hnot : ¬ (0 : ℤ) < -1 := by decide
      exact (hnot (h ▸ hdetpos)).elim
  let M : SL(2, ℤ) := ⟨!![m, -p; -n, q], by
    simpa only [Matrix.det_fin_two_of, neg_mul_neg] using hdet⟩
  have hdenEq : α * (-(n : ℂ) * (τ : ℂ) + (q : ℂ)) = 1 := by
    calc
      _ = (q : ℂ) * α - (n : ℂ) * (α * τ) := by ring
      _ = ((m * q - p * n : ℤ) : ℂ) := by rw [← hατ, ← hα]; push_cast; ring
      _ = 1 := by exact_mod_cast hdet
  have hden : -(n : ℂ) * (τ : ℂ) + (q : ℂ) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hdenEq
    exact zero_ne_one hdenEq
  have hrel : (m : ℂ) * (τ : ℂ) - (p : ℂ) =
      (σ : ℂ) * (-(n : ℂ) * (τ : ℂ) + (q : ℂ)) := by
    linear_combination (τ : ℂ) * hα - hατ
  refine ⟨M, ?_⟩
  apply UpperHalfPlane.ext
  have haction : ((M • τ : UpperHalfPlane) : ℂ) =
      ((m : ℂ) * (τ : ℂ) - (p : ℂ)) /
        (-(n : ℂ) * (τ : ℂ) + (q : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [M, sub_eq_add_neg]
  rw [haction]
  exact (div_eq_iff hden).2 hrel

/-- A modular matrix gives an explicit nonzero scalar transporting both full
integer lattices. This is a two-sided membership equivalence, not inclusion. -/
theorem normalizedPeriodLattice_scale_of_modular
    (τ σ : UpperHalfPlane) (M : SL(2, ℤ)) (hM : M • τ = σ) :
    ∃ α : ℂ, α ≠ 0 ∧ ∀ z : ℂ, z ∈ normalizedPeriodLattice τ ↔
      α * z ∈ normalizedPeriodLattice σ := by
  let a : ℤ := M 0 0
  let b : ℤ := M 0 1
  let c : ℤ := M 1 0
  let d : ℤ := M 1 1
  have hdet : a * d - b * c = 1 := by
    simpa only [a, b, c, d, Matrix.det_fin_two] using M.property
  let den : ℂ := (c : ℂ) * (τ : ℂ) + (d : ℂ)
  have hden : den ≠ 0 := by
    intro hz
    have hcd := normalized_coeff_unique τ d c 0 0 (by simpa [den, add_comm] using hz)
    have hfalse := hdet
    rw [hcd.1, hcd.2] at hfalse
    norm_num at hfalse
  have hσ : (σ : ℂ) = ((a : ℂ) * (τ : ℂ) + (b : ℂ)) / den := by
    rw [← hM, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [a, b, c, d, den]
  have hσcross : (σ : ℂ) * den = (a : ℂ) * (τ : ℂ) + (b : ℂ) :=
    (eq_div_iff hden).1 hσ
  let α : ℂ := 1 / den
  have hα0 : α ≠ 0 := one_div_ne_zero hden
  have hαden : α * den = 1 := one_div_mul_cancel hden
  have hα : α = (a : ℂ) - (c : ℂ) * (σ : ℂ) := by
    symm
    change (a : ℂ) - (c : ℂ) * (σ : ℂ) = 1 / den
    apply (eq_div_iff hden).2
    calc
      _ = (a : ℂ) * den - (c : ℂ) * ((σ : ℂ) * den) := by ring
      _ = ((a * d - b * c : ℤ) : ℂ) := by rw [hσcross]; dsimp only [den]; push_cast; ring
      _ = 1 := by exact_mod_cast hdet
  have hατ : α * (τ : ℂ) = -(b : ℂ) + (d : ℂ) * (σ : ℂ) := by
    apply mul_right_cancel₀ hden
    calc
      _ = (τ : ℂ) := by rw [mul_right_comm α (τ : ℂ) den, hαden, one_mul]
      _ = ((a * d - b * c : ℤ) : ℂ) * (τ : ℂ) := by rw [hdet]; simp
      _ = (-(b : ℂ) + (d : ℂ) * (σ : ℂ)) * den := by
        calc
          _ = -(b : ℂ) * den + (d : ℂ) * ((σ : ℂ) * den) := by
            rw [hσcross]; dsimp only [den]; push_cast; ring
          _ = _ := by ring
  refine ⟨α, hα0, ?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨m, n, hmn⟩ := (mem_normalizedPeriodLattice τ z).1 hz
    apply (mem_normalizedPeriodLattice σ (α * z)).2
    refine ⟨m * a - n * b, -m * c + n * d, ?_⟩
    calc
      _ = (m : ℂ) * α + (n : ℂ) * (α * τ) := by rw [hατ, hα]; push_cast; ring
      _ = α * z := by rw [← hmn]; ring
  · intro hz
    obtain ⟨m, n, hmn⟩ := (mem_normalizedPeriodLattice σ (α * z)).1 hz
    apply (mem_normalizedPeriodLattice τ z).2
    refine ⟨d * m + b * n, c * m + a * n, ?_⟩
    calc
      _ = (m : ℂ) * den + (n : ℂ) * ((σ : ℂ) * den) := by
        rw [hσcross]; dsimp only [den]; push_cast; ring
      _ = den * ((m : ℂ) + (n : ℂ) * σ) := by ring
      _ = den * (α * z) := by rw [hmn]
      _ = z := by rw [← mul_assoc, mul_comm den α, hαden, one_mul]

/-- Pure normalized lattice classification, using the actual Mathlib SL action. -/
theorem normalizedPeriodLattice_scale_iff_modular (τ σ : UpperHalfPlane) :
    (∃ α : ℂ, α ≠ 0 ∧ ∀ z : ℂ, z ∈ normalizedPeriodLattice τ ↔
      α * z ∈ normalizedPeriodLattice σ) ↔
      ∃ M : SL(2, ℤ), M • τ = σ := by
  constructor
  · rintro ⟨α, hα0, hΛ⟩
    exact normalizedPeriodLattice_modular_of_scale τ σ α hα0 hΛ
  · rintro ⟨M, hM⟩
    exact normalizedPeriodLattice_scale_of_modular τ σ M hM

/-- The same classification in the literal image-of-lattice formulation. -/
theorem normalizedPeriodLattice_image_iff_modular (τ σ : UpperHalfPlane) :
    (∃ α : ℂ, α ≠ 0 ∧
      (fun z : ℂ => α * z) '' (normalizedPeriodLattice τ : Set ℂ) =
        (normalizedPeriodLattice σ : Set ℂ)) ↔
      ∃ M : SL(2, ℤ), M • τ = σ := by
  rw [← normalizedPeriodLattice_scale_iff_modular]
  constructor
  · rintro ⟨α, hα0, heq⟩
    refine ⟨α, hα0, fun z => ?_⟩
    constructor
    · intro hz
      have hset : α * z ∈ (normalizedPeriodLattice σ : Set ℂ) := by
        rw [← heq]
        exact ⟨z, SetLike.mem_coe.mpr hz, rfl⟩
      exact SetLike.mem_coe.mp hset
    · intro hz
      have hzset : α * z ∈ (normalizedPeriodLattice σ : Set ℂ) := SetLike.mem_coe.mpr hz
      rw [← heq] at hzset
      obtain ⟨w, hw, he⟩ := hzset
      have hw' : w ∈ normalizedPeriodLattice τ := SetLike.mem_coe.mp hw
      exact (mul_left_cancel₀ hα0 he) ▸ hw'
  · rintro ⟨α, hα0, hΛ⟩
    refine ⟨α, hα0, ?_⟩
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact SetLike.mem_coe.mpr ((hΛ w).1 (SetLike.mem_coe.mp hw))
    · intro hz
      have hz' : z ∈ normalizedPeriodLattice σ := SetLike.mem_coe.mp hz
      refine ⟨α⁻¹ * z, ?_, ?_⟩
      · apply SetLike.mem_coe.mpr
        apply (hΛ _).2
        simpa only [← mul_assoc, mul_inv_cancel₀ hα0, one_mul] using hz'
      · simp only [← mul_assoc, mul_inv_cancel₀ hα0, one_mul]

end LowDimensionalTopology.Geometry.Surfaces
