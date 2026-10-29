module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.TranslationPowers
public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Positive actual metric translation length excludes elliptic and parabolic actions. -/
theorem qc_isHyperbolic_of_hTranslationLength_pos
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hpos : 0 < hTranslationLength (hSLIsometry B)) : LiZhongQC.IsHyperbolic B := by
  have hbound (τ : ℍ) : hTranslationLength (hSLIsometry B) ≤ dist τ (B • τ) := by
    change sInf (range (fun z : ℍ => dist z (B • z))) ≤ _
    exact csInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact dist_nonneg⟩ ⟨τ, rfl⟩
  have hfix (τ : ℍ) : B • τ ≠ τ := by
    intro h
    have hz := hbound τ
    rw [h, dist_self] at hz
    exact (not_lt_of_ge hz) hpos
  have h1 : B ≠ 1 := by
    intro h
    apply hfix UpperHalfPlane.I
    rw [h, one_smul]
  have hm1 : B ≠ -1 := by
    intro h
    apply hfix UpperHalfPlane.I
    rw [h, LiZhongQC.s27g_neg_one_smul]
  change 2 < |LiZhongQC.slTrace B|
  by_contra hh
  rcases lt_or_eq_of_le (le_of_not_gt hh) with hlt | heq
  · obtain ⟨τ, hτ⟩ := LiZhongQC.exists_smul_eq_self_of_abs_slTrace_lt_two hlt
    exact hfix τ hτ
  · obtain ⟨τ, hτ⟩ :=
      LiZhongQC.exists_dist_smul_lt_of_isParabolic ⟨heq, h1, hm1⟩ hpos
    exact (not_lt_of_ge (hbound τ)) hτ

/-- Every positive power of the actual original hyperbolic matrix is hyperbolic. -/
theorem qc_isHyperbolic_pow (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    {n : ℕ} (hn : 0 < n) : LiZhongQC.IsHyperbolic (A ^ n) := by
  apply qc_isHyperbolic_of_hTranslationLength_pos
  rw [hSL_translationLength_pow A hA ht]
  exact mul_pos (Nat.cast_pos.mpr hn) (hHyperbolic_translationLength_pos A hA ht)


/-- The full free class covered by an actual positive power retains that power's
length. The covering matrix is not replaced by a primitive generator. -/
theorem covered_freeHomotopyLength_pow
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S}
    (hp : LiZhongQC.IsUniformization Γ p)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hΓ : A ∈ Γ)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2)
    {n : ℕ} (hn : 0 < n) (α : LiZhongQC.Loop S)
    (hcov : LiZhongQC.Covers p (A ^ n) α) :
    LiZhongQC.freeHomotopyLength p α =
      ENNReal.ofReal ((n : ℝ) * hTranslationLength (hSLIsometry A)) := by
  have hh := qc_isHyperbolic_pow A hA ht hn
  have hT : LiZhongQC.translationLength (A ^ n) =
      hTranslationLength (hSLIsometry (A ^ n)) := by
    change LiZhongQC.translationLength (A ^ n) = ⨅ τ : ℍ, dist τ (A ^ n • τ)
    exact (LiZhongQC.translationLength_eq_inf_dist hh).1
  rw [LiZhongQC.s30a_len_hyp hp (Γ.pow_mem hΓ n) hh hcov,
    hT, hSL_translationLength_pow A hA ht n]

end LowDimensionalTopology.Geometry.Hyperbolic
