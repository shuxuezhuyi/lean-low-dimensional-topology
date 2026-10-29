module

public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicAxes
public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

/-!
# Wolpert distortion of native hyperbolic translation lengths

The lengths here are the existing actual infima of native hyperbolic
isometry displacements. The matrices are the actual deck transformations,
without replacing them by primitive generators or by their axis image sets.
There are no unproved comparison hypotheses or Teichmuller quotient inputs.
-/

@[expose] public section

noncomputable section

open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

private theorem qc_isHyperbolic_of_trace_sq
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : 4 < (Matrix.trace A.val) ^ 2) :
    LiZhongQC.IsHyperbolic A := by
  have ht : LiZhongQC.slTrace A = Matrix.trace A.val := by
    simp only [LiZhongQC.slTrace, Matrix.trace_fin_two]
  change 2 < |LiZhongQC.slTrace A|
  rw [ht]
  have hs : 4 < |Matrix.trace A.val| ^ 2 := by
    simpa only [sq_abs] using hA
  nlinarith [abs_nonneg (Matrix.trace A.val)]

/-- The source trace formula computes exactly the already defined native
translation length for the same actual matrix action. -/
theorem hTranslationLength_eq_qc_translationLength
    {A : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hA : 4 < (Matrix.trace A.val) ^ 2) :
    hTranslationLength (hSLIsometry A) = LiZhongQC.translationLength A := by
  change sInf (range (fun z : ℍ => dist z (A • z))) = LiZhongQC.translationLength A
  exact (LiZhongQC.translationLength_eq_inf_dist (qc_isHyperbolic_of_trace_sq hA)).1.symm

private theorem liftToC_image_upperHalf (F : ℍ ≃ₜ ℍ) :
    LiZhongQC.liftToC F '' LiZhongQC.upperHalf = LiZhongQC.upperHalf := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [LiZhongQC.h23l_liftToC_eq F hw]
    exact (F (UpperHalfPlane.ofComplex w)).im_pos
  · intro hz
    let τ : ℍ := ⟨z, hz⟩
    refine ⟨(F.symm τ : ℂ), (F.symm τ).im_pos, ?_⟩
    rw [LiZhongQC.h23l_liftToC_coe, F.apply_symm_apply]

private theorem liftToC_injOn_upperHalf (F : ℍ ≃ₜ ℍ) :
    InjOn (LiZhongQC.liftToC F) LiZhongQC.upperHalf := by
  intro w hw z hz heq
  let τ : ℍ := ⟨w, hw⟩
  let σ : ℍ := ⟨z, hz⟩
  change LiZhongQC.liftToC F (τ : ℂ) = LiZhongQC.liftToC F (σ : ℂ) at heq
  rw [LiZhongQC.h23l_liftToC_coe, LiZhongQC.h23l_liftToC_coe] at heq
  have hτσ : τ = σ := F.injective (UpperHalfPlane.ext heq)
  exact congrArg (fun x : ℍ => (x : ℂ)) hτσ

/-- The actual inverse half-plane homeomorphism is K-quasiconformal with the
same K; this follows from the plane inverse theorem on its actual domain. -/
theorem isKQC_liftToC_symm {F : ℍ ≃ₜ ℍ} {K : ℝ}
    (hF : LiZhongQC.IsKQC (LiZhongQC.liftToC F) LiZhongQC.upperHalf K) :
    LiZhongQC.IsKQC (LiZhongQC.liftToC F.symm) LiZhongQC.upperHalf K := by
  have hi := LiZhongQC.thm7_2_inv hF
  rw [liftToC_image_upperHalf F] at hi
  refine LiZhongQC.ad_isKQC_congr hi ?_
  intro z hz
  let τ : ℍ := ⟨z, hz⟩
  have hx : (F.symm τ : ℂ) ∈ LiZhongQC.upperHalf := (F.symm τ).im_pos
  have hv : LiZhongQC.liftToC F (F.symm τ : ℂ) = z := by
    rw [LiZhongQC.h23l_liftToC_coe, F.apply_symm_apply]
  have hleft := (liftToC_injOn_upperHalf F).leftInvOn_invFunOn hx
  rw [hv] at hleft
  change LiZhongQC.liftToC F.symm (τ : ℂ) = _
  rw [LiZhongQC.h23l_liftToC_coe]
  exact hleft.symm

/-- A genuine K-quasiconformal conjugacy of actual hyperbolic matrix actions
changes their native translation lengths by factors between 1/K and K.
No primitive-element premise occurs, so proper powers retain their multiplicity. -/
theorem wolpert_hTranslationLength
    {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hA : 4 < (Matrix.trace A.val) ^ 2) (hB : 4 < (Matrix.trace B.val) ^ 2)
    {F : ℍ ≃ₜ ℍ} {K : ℝ}
    (hF : LiZhongQC.IsKQC (LiZhongQC.liftToC F) LiZhongQC.upperHalf K)
    (hAB : ∀ z : ℍ, F (A • z) = B • F z) :
    hTranslationLength (hSLIsometry A) / K ≤ hTranslationLength (hSLIsometry B) ∧
      hTranslationLength (hSLIsometry B) ≤ K * hTranslationLength (hSLIsometry A) := by
  have hA' := qc_isHyperbolic_of_trace_sq hA
  have hB' := qc_isHyperbolic_of_trace_sq hB
  have hF' := isKQC_liftToC_symm hF
  have hBA : ∀ z : ℍ, F.symm (B • z) = A • F.symm z := by
    intro z
    apply F.injective
    rw [F.apply_symm_apply, hAB, F.apply_symm_apply]
  have hforward : hTranslationLength (hSLIsometry A) ≤
      K * hTranslationLength (hSLIsometry B) := by
    simpa only [← hTranslationLength_eq_qc_translationLength hA,
      ← hTranslationLength_eq_qc_translationLength hB] using
      LiZhongQC.s30w_translation_le hA' hB' hF hAB
  have hreverse : hTranslationLength (hSLIsometry B) ≤
      K * hTranslationLength (hSLIsometry A) := by
    simpa only [← hTranslationLength_eq_qc_translationLength hB,
      ← hTranslationLength_eq_qc_translationLength hA] using
      LiZhongQC.s30w_translation_le hB' hA' hF' hBA
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hF.2.1
  exact ⟨(div_le_iff₀ hK).2 (by simpa only [mul_comm] using hforward), hreverse⟩

/-- The same genuine inequality for the actual nth powers. Hyperbolicity is
checked on those actual matrices, rather than discarding a traversal exponent. -/
theorem wolpert_hTranslationLength_pow
    {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ} (n : ℕ)
    (hAn : 4 < (Matrix.trace (A ^ n).val) ^ 2)
    (hBn : 4 < (Matrix.trace (B ^ n).val) ^ 2)
    {F : ℍ ≃ₜ ℍ} {K : ℝ}
    (hF : LiZhongQC.IsKQC (LiZhongQC.liftToC F) LiZhongQC.upperHalf K)
    (hAB : ∀ z : ℍ, F (A • z) = B • F z) :
    hTranslationLength (hSLIsometry (A ^ n)) / K ≤ hTranslationLength (hSLIsometry (B ^ n)) ∧
      hTranslationLength (hSLIsometry (B ^ n)) ≤ K * hTranslationLength (hSLIsometry (A ^ n)) := by
  have hpow : ∀ m : ℕ, ∀ z : ℍ, F ((A ^ m) • z) = (B ^ m) • F z := by
    intro m
    induction m with
    | zero =>
        intro z
        simp only [pow_zero, one_smul]
    | succ m ih =>
      intro z
      rw [pow_succ', mul_smul, hAB, ih, ← mul_smul, ← pow_succ']
  exact wolpert_hTranslationLength hAn hBn hF (hpow n)

end LowDimensionalTopology.Geometry.Hyperbolic
