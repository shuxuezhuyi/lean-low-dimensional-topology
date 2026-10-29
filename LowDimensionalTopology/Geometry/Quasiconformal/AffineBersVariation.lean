/-
The actual normalized-solution, coefficient and parameter-variation APIs are
from Wu Xiaobin's Li-Zhong-QC-formalization, pinned commit
1c0d5473c020b66ed5106331a38a61536760b9b2, under Apache 2.0.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.CanonicalBersVariation

/-!
# Actual affine directions of the nonsymmetric normalized Bers family

The direction is any bounded measurable coefficient on the upper half-plane,
extended by zero on the closed lower half-plane. Its norm need not be below
one. The small admissible parameter ball is derived from the two actual bounds.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology

namespace LowDimensionalTopology.Geometry.Quasiconformal.CanonicalBersVariation

open scoped Classical in
/-- The actual affine coefficient, with an irrelevant base-value fallback
outside its admissible parameter set. -/
def affineFamily (μ : LiZhongQC.BeltramiH) (η : ℂ → ℂ) (t : ℂ) : LiZhongQC.BeltramiH :=
  if h : (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
      LiZhongQC.IsBeltramiCoeff (fun ζ => μ.val ζ + t * η ζ) univ k) ∧
      ∀ ζ : ℂ, ζ.im ≤ 0 → μ.val ζ + t * η ζ = 0 then
    ⟨fun ζ => μ.val ζ + t * η ζ, h⟩ else μ

theorem exists_affine_common_bound (μ : LiZhongQC.BeltramiH)
    {η : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hη : LiZhongQC.IsBeltramiCoeff η univ M) :
    ∃ r > 0, ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
      ∀ t ∈ ball (0 : ℂ) r,
        LiZhongQC.IsBeltramiCoeff (fun ζ => μ.val ζ + t * η ζ) univ k := by
  obtain ⟨⟨k₁, hk₁0, hk₁1, hm₁, hb₁⟩, -⟩ := μ.property
  obtain ⟨hm₂, hb₂⟩ := hη
  have hr : 0 < (1 - k₁) / (2 * (M + 1)) := div_pos (by linarith) (by positivity)
  have hrM : (1 - k₁) / (2 * (M + 1)) * M ≤ (1 - k₁) / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨(1 - k₁) / (2 * (M + 1)), hr,
    k₁ + (1 - k₁) / (2 * (M + 1)) * M,
    add_nonneg hk₁0 (mul_nonneg hr.le hM), by linarith,
    fun t ht => ⟨hm₁.add (hm₂.const_mul t), ?_⟩⟩
  filter_upwards [hb₁, hb₂] with ζ h1 h2
  have htn : ‖t‖ ≤ (1 - k₁) / (2 * (M + 1)) := (mem_ball_zero_iff.mp ht).le
  calc
    ‖μ.val ζ + t * η ζ‖ ≤ ‖μ.val ζ‖ + ‖t‖ * ‖η ζ‖ := by
      rw [← norm_mul]
      exact norm_add_le _ _
    _ ≤ _ := add_le_add h1 (mul_le_mul htn h2 (norm_nonneg _) hr.le)

private theorem affineFamily_val (μ : LiZhongQC.BeltramiH) (η : ℂ → ℂ)
    (hzero : ∀ ζ : ℂ, ζ.im ≤ 0 → η ζ = 0) {r k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ t ∈ ball (0 : ℂ) r,
      LiZhongQC.IsBeltramiCoeff (fun ζ => μ.val ζ + t * η ζ) univ k)
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) r) :
    (affineFamily μ η t).val = fun ζ => μ.val ζ + t * η ζ := by
  have hc : (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
      LiZhongQC.IsBeltramiCoeff (fun ζ => μ.val ζ + t * η ζ) univ k) ∧
      ∀ ζ : ℂ, ζ.im ≤ 0 → μ.val ζ + t * η ζ = 0 :=
    ⟨⟨k, hk0, hk1, hb t ht⟩,
      fun ζ hz => by rw [μ.property.2 ζ hz, hzero ζ hz, mul_zero, add_zero]⟩
  unfold affineFamily
  exact congrArg Subtype.val (dite_eq_left hc)

/-- Every bounded coefficient direction gives the literal Schwarzian
variation of the ORIGINAL nonsymmetric affine normalized quotient. -/
theorem hasDerivAt_schwarzian_affineQuotient (μ : LiZhongQC.BeltramiH)
    {η : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hη : LiZhongQC.IsBeltramiCoeff η univ M)
    (hzero : ∀ ζ : ℂ, ζ.im ≤ 0 → η ζ = 0)
    {z : ℂ} (hz : z ∈ lowerImage μ) :
    HasDerivAt (fun t : ℂ => LiZhongQC.schwarzian
      (LiZhongQC.normalizedSolution (fun ζ => μ.val ζ + t * η ζ) ∘ baseInverse μ) z)
      (iteratedDeriv 3 (LiZhongQC.ahVar (LiZhongQC.ahT_dot η μ.val (baseMap μ))) z) 0 := by
  obtain ⟨r, hr, k, hk0, hk1, hb⟩ := exists_affine_common_bound μ hM hη
  let σ : ℂ → LiZhongQC.BeltramiH := affineFamily μ η
  have hval : ∀ t ∈ ball (0 : ℂ) r, (σ t).val = fun ζ => μ.val ζ + t * η ζ :=
    fun t ht => affineFamily_val μ η hzero hk0 hk1 hb ht
  have hσ0 : σ 0 = μ := by
    apply Subtype.ext
    rw [hval 0 (mem_ball_self hr)]
    funext ζ
    simp
  have hkP : ∀ t ∈ ball (0 : ℂ) r, LiZhongQC.IsBeltramiCoeff (σ t).val univ k := by
    intro t ht
    rw [hval t ht]
    exact hb t ht
  have hhol : ∀ ζ, DifferentiableOn ℂ (fun t => (σ t).val ζ) (ball 0 r) := by
    intro ζ
    exact (by fun_prop : DifferentiableOn ℂ
      (fun t : ℂ => μ.val ζ + t * η ζ) (ball 0 r)).congr
      fun t ht => by rw [hval t ht]
  have hd : (fun ζ => deriv (fun t => (σ t).val ζ) 0) = η := by
    funext ζ
    have he : (fun t => (σ t).val ζ) =ᶠ[𝓝 (0 : ℂ)] fun t => μ.val ζ + t * η ζ := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hr] with t ht
      exact congrFun (hval t ht) ζ
    rw [he.deriv_eq]
    simp
  have htransport : infinitesimalCoefficient σ = LiZhongQC.ahT_dot η μ.val (baseMap μ) := by
    dsimp only [infinitesimalCoefficient]
    rw [hd, hσ0]
  have hzσ : z ∈ lowerImage (σ 0) := by simpa only [hσ0] using hz
  have h := hasDerivAt_schwarzian_quotientFamily isOpen_ball (mem_ball_self hr)
    hk0 hk1 hkP hhol hzσ
  rw [htransport] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds (0 : ℂ) hr] with t ht
  have hq : quotientFamily σ t =
      LiZhongQC.normalizedSolution (fun ζ => μ.val ζ + t * η ζ) ∘ baseInverse μ := by
    funext w
    change LiZhongQC.normalizedSolution (σ t).val (baseInverse (σ 0) w) = _
    rw [hval t ht, hσ0]
    rfl
  exact congrArg (fun f => LiZhongQC.schwarzian f z) hq.symm

end LowDimensionalTopology.Geometry.Quasiconformal.CanonicalBersVariation
