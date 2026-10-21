/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementFunctions
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The literal squared modulus of a real quadratic evaluated at x+iy. -/
def hQuadraticNormSq (c t b x y : ℝ) : ℝ :=
  (c * (x ^ 2 - y ^ 2) + t * x - b) ^ 2 + (2*c*x*y + t*y) ^ 2

/-- Six genuine upper-half-plane probes recover all six quadratic coefficient products. -/
theorem hQuadraticNormSq_products (c t b C T B : ℝ)
    (h : ∀ x y : ℝ, 0 < y → hQuadraticNormSq c t b x y = hQuadraticNormSq C T B x y) :
    c ^ 2 = C ^ 2 ∧ c*t = C*T ∧ t*b = T*B ∧ t ^ 2 = T ^ 2 ∧ c*b = C*B ∧ b ^ 2 = B ^ 2 := by
  have h0 := h 0 1 (by norm_num)
  have h1 := h 1 1 (by norm_num)
  have hm1 := h (-1) 1 (by norm_num)
  have h2 := h 2 1 (by norm_num)
  have hm2 := h (-2) 1 (by norm_num)
  have h02 := h 0 2 (by norm_num)
  dsimp [hQuadraticNormSq] at h0 h1 hm1 h2 hm2 h02
  have hcc : c ^ 2 = C ^ 2 := by
    linear_combination (1/24:ℝ)*h2 + (1/24:ℝ)*hm2 - (1/6:ℝ)*h1 - (1/6:ℝ)*hm1 + (1/4:ℝ)*h0
  have hct : c*t = C*T := by
    linear_combination (1/24:ℝ)*h2 - (1/24:ℝ)*hm2 - (1/12:ℝ)*h1 + (1/12:ℝ)*hm1
  have htb : t*b = T*B := by
    linear_combination 2*hct - (1/4:ℝ)*h1 + (1/4:ℝ)*hm1
  have hminus : t ^ 2 - 2*c*b = T ^ 2 - 2*C*B := by
    linear_combination (1/2:ℝ)*h1 + (1/2:ℝ)*hm1 - h0 - 3*hcc
  have hplus : t ^ 2 + 2*c*b = T ^ 2 + 2*C*B := by
    linear_combination (1/3:ℝ)*h02 - (1/3:ℝ)*h0 - 5*hcc
  have htt : t ^ 2 = T ^ 2 := by linear_combination (1/2:ℝ)*hminus + (1/2:ℝ)*hplus
  have hcb : c*b = C*B := by linear_combination (1/4:ℝ)*hplus - (1/4:ℝ)*hminus
  have hbb : b ^ 2 = B ^ 2 := by linear_combination h0 - hcc - htt - 2*hcb
  exact ⟨hcc, hct, htb, htt, hcb, hbb⟩


/-- The six recovered products determine the real coefficient triple up to its single global sign. -/
theorem hQuadraticNormSq_sign (c t b C T B : ℝ)
    (h : ∀ x y : ℝ, 0 < y → hQuadraticNormSq c t b x y = hQuadraticNormSq C T B x y) :
    (c = C ∧ t = T ∧ b = B) ∨ (c = -C ∧ t = -T ∧ b = -B) := by
  obtain ⟨hcc, hct, htb, htt, hcb, hbb⟩ := hQuadraticNormSq_products c t b C T B h
  by_cases hc : c = 0
  · have hC : C = 0 := by rw [hc] at hcc; nlinarith
    by_cases ht : t = 0
    · have hT : T = 0 := by rw [ht] at htt; nlinarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hbb with hb | hb
      · exact Or.inl ⟨by simp [hc, hC], by simp [ht, hT], hb⟩
      · exact Or.inr ⟨by simp [hc, hC], by simp [ht, hT], hb⟩
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp htt with ht' | ht'
      · rw [← ht'] at htb
        exact Or.inl ⟨by simp [hc, hC], ht', mul_left_cancel₀ ht htb⟩
      · have hT : T = -t := by linarith
        rw [hT] at htb
        have hb : b = -B := by
          apply mul_left_cancel₀ ht
          linear_combination htb
        exact Or.inr ⟨by simp [hc, hC], ht', hb⟩
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp hcc with hc' | hc'
    · rw [← hc'] at hct hcb
      exact Or.inl ⟨hc', mul_left_cancel₀ hc hct, mul_left_cancel₀ hc hcb⟩
    · have hC : C = -c := by linarith
      rw [hC] at hct hcb
      have ht : t = -T := by
        apply mul_left_cancel₀ hc
        linear_combination hct
      have hb : b = -B := by
        apply mul_left_cancel₀ hc
        linear_combination hcb
      exact Or.inr ⟨hc', ht, hb⟩

/-- Equality of the actual displacement functions recovers the centered matrix triple up to sign. -/
theorem hSL_displacement_coefficients (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : hDisplacement (hSLIsometry A) = hDisplacement (hSLIsometry B)) :
    (A 1 0 = B 1 0 ∧ A 1 1 - A 0 0 = B 1 1 - B 0 0 ∧ A 0 1 = B 0 1) ∨
      (A 1 0 = -B 1 0 ∧ A 1 1 - A 0 0 = -(B 1 1 - B 0 0) ∧ A 0 1 = -B 0 1) := by
  apply hQuadraticNormSq_sign
  intro x y hy
  let z := metricProbe x y hy
  have hz := congrArg (fun f : ℍ → ℝ => Real.sinh (f z / 2)) h
  change Real.sinh (dist z (A•z) / 2) = Real.sinh (dist z (B•z) / 2) at hz
  rw [hSL_half_displacement_polynomial, hSL_half_displacement_polynomial] at hz
  have hnorm := (div_left_inj' (show 2*z.im ≠ 0 by positivity)).mp hz
  have hsq := congrArg (fun r : ℝ => r ^ 2) hnorm
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at hsq
  norm_num [Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, z, metricProbe] at hsq
  dsimp [hQuadraticNormSq]
  linear_combination hsq


/-- The determinant condition recovers the full matrix from its centered triple,
up to the inverse and sign ambiguities inherent in displacement. -/
theorem hSL_equal_centered_coefficients (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0 = B 1 0) (ht : A 1 1 - A 0 0 = B 1 1 - B 0 0)
    (hb : A 0 1 = B 0 1) : A = B ∨ A = -B⁻¹ := by
  have hdetA := A.det_coe
  have hdetB := B.det_coe
  rw [Matrix.det_fin_two] at hdetA hdetB
  rw [← hc, ← hb] at hdetB
  have hsq : (A 0 0 + A 1 1) ^ 2 = (B 0 0 + B 1 1) ^ 2 := by
    have hs := congrArg (fun t : ℝ => t ^ 2) ht
    nlinarith [hdetA, hdetB]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hsum | hsum
  · have h00 : A 0 0 = B 0 0 := by linarith
    have h11 : A 1 1 = B 1 1 := by linarith
    left
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact hb
    · exact hc
    · exact h11
  · have h00 : A 0 0 = -B 1 1 := by linarith
    have h11 : A 1 1 = -B 0 0 := by linarith
    right
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, h00, h11, hb, hc]

/-- The full real special-linear representative is determined up to exactly
sign and inversion by its actual native displacement function. -/
theorem hSL_displacement_representatives (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : hDisplacement (hSLIsometry A) = hDisplacement (hSLIsometry B)) :
    A = B ∨ A = -B⁻¹ ∨ A = B⁻¹ ∨ A = -B := by
  rcases hSL_displacement_coefficients A B h with ⟨hc, ht, hb⟩ | ⟨hc, ht, hb⟩
  · rcases hSL_equal_centered_coefficients A B hc ht hb with he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
  · have hc' : A 1 0 = (B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 := by
      simpa [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] using hc
    have hb' : A 0 1 = (B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 := by
      simpa [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] using hb
    have ht' : A 1 1 - A 0 0 = (B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 - B⁻¹ 0 0 := by
      simpa [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] using ht
    rcases hSL_equal_centered_coefficients A B⁻¹ hc' ht' hb' with he | he
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inr (Or.inr (Or.inr (by simpa using he)))

/-- The actual native isometry is independent of its sign representative. -/
theorem hSLIsometry_neg (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    hSLIsometry (-A) = hSLIsometry A := by
  apply IsometryEquiv.ext
  intro z
  apply UpperHalfPlane.ext
  simp only [hSLIsometry_apply, UpperHalfPlane.coe_specialLinearGroup_apply,
    Algebra.algebraMap_self_apply, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply,
    Complex.ofReal_neg, neg_mul, ← neg_add, neg_div_neg_eq]

theorem hSLIsometry_inverse (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    hSLIsometry A⁻¹ = (hSLIsometry A).symm := by
  apply IsometryEquiv.ext
  intro z
  apply (hSLIsometry A).injective
  rw [(hSLIsometry A).apply_symm_apply]
  change A • (A⁻¹ • z) = z
  exact smul_inv_smul A z

/--
The complete displacement function determines precisely
the original conformal isometry and its inverse, in the native hyperbolic metric.
-/
theorem hSL_displacement_determines_inverse_pair (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    hDisplacement (hSLIsometry A) = hDisplacement (hSLIsometry B) ↔
      hSLIsometry A = hSLIsometry B ∨ hSLIsometry A = (hSLIsometry B).symm := by
  constructor
  · intro h
    rcases hSL_displacement_representatives A B h with he | he | he | he
    · exact Or.inl (congrArg hSLIsometry he)
    · right
      rw [he, hSLIsometry_neg, hSLIsometry_inverse]
    · right
      rw [he, hSLIsometry_inverse]
    · left
      rw [he, hSLIsometry_neg]
  · rintro (he | he)
    · rw [he]
    · rw [he]
      funext z
      exact hDisplacement_inverse _ z


/-- The preferred half-sinh version has exactly the same inverse-pair determination property. -/
theorem hSL_sinh_displacement_determines_inverse_pair (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    hSinhDisplacement (hSLIsometry A) = hSinhDisplacement (hSLIsometry B) ↔
      hSLIsometry A = hSLIsometry B ∨ hSLIsometry A = (hSLIsometry B).symm := by
  rw [hSinhDisplacement_eq_iff, hSL_displacement_determines_inverse_pair]

end LowDimensionalTopology.Geometry.Hyperbolic
