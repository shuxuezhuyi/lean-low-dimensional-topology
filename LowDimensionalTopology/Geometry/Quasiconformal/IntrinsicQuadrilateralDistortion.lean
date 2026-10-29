module

public import LowDimensionalTopology.Geometry.Quasiconformal.IntrinsicQuadrilateral
public import LowDimensionalTopology.Geometry.Quasiconformal.AnalyticDefinition

/-!
# Intrinsic quadrilateral distortion and geometric quasiconformality

The same actual image quadrilateral satisfies both modulus bounds with the
original constant. Boundary-order comparison remains an explicit premise.

Analytic and geometric proofs are reused through the public API from
Wu Xiaobin's Apache-2.0 source at fixed commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` and its recorded local adapters.
-/

@[expose] public section
noncomputable section
open Set

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Analytic K-quasiconformality gives both modulus bounds on the same actual
image of every intrinsic quadrilateral contained in the original domain. -/
theorem intrinsic_quadrilateral_modulus_bounds_analytic
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : IsAnalyticallyKQuasiconformal f D K) (Q : IntrinsicQuadrilateral)
    (hQ : closure (LiZhongQC.toExt Q.dom) ⊆ LiZhongQC.toExt D) :
    ∃ Q' : IntrinsicQuadrilateral, Q.IsImageUnder Q' f ∧
      intrinsicQuadrilateralModulus Q / K ≤ intrinsicQuadrilateralModulus Q' ∧
        intrinsicQuadrilateralModulus Q' ≤ K * intrinsicQuadrilateralModulus Q := by
  let P : LiZhongQC.TopQuad := ⟨Q.dom, Q.vert,
    (intrinsicQuadrilateral_iff_presented hHard Q.isIntrinsic.2.1).1 Q.isIntrinsic⟩
  obtain ⟨P', hP', hlo, hhi⟩ := quadrilateral_modulus_bounds_analytic hf P hQ
  have hclosure : closure (LiZhongQC.toExt P'.dom) ⊆ LiZhongQC.toExt (f '' D) := by
    rw [hP'.1]
    exact LiZhongQC.closure_toExt_image_subset hf.2.2.1.1 hQ subset_rfl
  let Q' : IntrinsicQuadrilateral := ⟨P'.dom, P'.vert,
    (intrinsicQuadrilateral_iff_presented hHard
      (isBounded_of_quad_closure_subset hclosure)).2 P'.isTopQuad⟩
  exact ⟨Q', hP', hlo, hhi⟩

/-- Both modulus bounds for the literal ordinary-coordinate ACL definition, with unchanged K. -/
theorem intrinsic_quadrilateral_modulus_bounds_linewise
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : IsLinewiseKQuasiconformal f D K) (Q : IntrinsicQuadrilateral)
    (hQ : closure (LiZhongQC.toExt Q.dom) ⊆ LiZhongQC.toExt D) :
    ∃ Q' : IntrinsicQuadrilateral, Q.IsImageUnder Q' f ∧
      intrinsicQuadrilateralModulus Q / K ≤ intrinsicQuadrilateralModulus Q' ∧
        intrinsicQuadrilateralModulus Q' ≤ K * intrinsicQuadrilateralModulus Q :=
  intrinsic_quadrilateral_modulus_bounds_analytic hHard (linewise_iff_analytic.mp hf) Q hQ

/-- One geometric distortion constant controls all intrinsic quadrilaterals. -/
def IsIntrinsicallyQuasiconformal (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  ∃ K : ℝ, IsIntrinsicallyKQuasiconformal f D K

/-- The one-sided and two-sided geometric conditions admit exactly the same K. -/
theorem intrinsic_geometric_iff_two_sided
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ} :
    IsIntrinsicallyKQuasiconformal f D K ↔
      IsOpen D ∧ 1 ≤ K ∧ LiZhongQC.IsHomeomorphOnto f D (f '' D) ∧
        ∀ Q : IntrinsicQuadrilateral,
          closure (LiZhongQC.toExt Q.dom) ⊆ LiZhongQC.toExt D →
            ∃ Q' : IntrinsicQuadrilateral, Q.IsImageUnder Q' f ∧
              intrinsicQuadrilateralModulus Q / K ≤ intrinsicQuadrilateralModulus Q' ∧
                intrinsicQuadrilateralModulus Q' ≤ K * intrinsicQuadrilateralModulus Q := by
  constructor
  · intro hf
    refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_⟩
    exact intrinsic_quadrilateral_modulus_bounds_analytic hHard
      ((intrinsic_geometric_iff_analytic hHard).mp hf)
  · rintro ⟨hD, hK, hhomeo, hmod⟩
    refine ⟨hD, hK, hhomeo, ?_⟩
    intro Q hQ
    obtain ⟨Q', himage, _, hupper⟩ := hmod Q hQ
    exact ⟨Q', himage, hupper⟩

/-- The full intrinsic geometric definition and literal analytic definition agree. -/
theorem intrinsic_quasiconformal_iff_linewise
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    {f : ℂ → ℂ} {D : Set ℂ} :
    IsIntrinsicallyQuasiconformal f D ↔ IsLinewiseQuasiconformal f D := by
  rw [IsIntrinsicallyQuasiconformal, linewise_iff_exists_K]
  exact exists_congr fun K =>
    (intrinsic_geometric_iff_analytic hHard).trans linewise_iff_analytic.symm

/-- On a genuine nonempty domain, the geometric infimum is the actual essential
maximal dilatation. -/
theorem intrinsic_geometric_inf_eq_maxDilatation
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    {f : ℂ → ℂ} {D : Set ℂ} (hf : IsIntrinsicallyQuasiconformal f D)
    (hne : D.Nonempty) :
    sInf {K : ℝ | IsIntrinsicallyKQuasiconformal f D K} =
      (LiZhongQC.maxDilatation f D).toReal := by
  obtain ⟨K, hK⟩ := hf
  have hset : {L : ℝ | IsIntrinsicallyKQuasiconformal f D L} =
      {L : ℝ | LiZhongQC.IsKQC f D L} := by
    ext L
    exact (intrinsic_geometric_iff_analytic hHard).trans geometric_iff_analytic.symm
  rw [hset]
  exact infimalDilatation_eq_essential_quotient
    (intrinsic_quasiconformal_to_presented hHard hK) hne

end LowDimensionalTopology.Geometry.Quasiconformal
