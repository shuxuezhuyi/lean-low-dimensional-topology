module

public import LowDimensionalTopology.Geometry.Quasiconformal.IntrinsicQuadrilateral

/-!
# Rectangular models of intrinsic Jordan quadrilaterals

Every intrinsic domain with its ordered boundary vertices has an actual
conformal rectangle model, and all such models have the same side ratio.
The independent Jordan boundary-order theorem remains explicit.

The rectangular-model and rigidity proofs are reused through the public API.
They are due to Wu Xiaobin, from the fixed Apache-2.0 source recorded in
`External/LiZhongQC/UPSTREAM.json` at commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`.
-/

@[expose] public section
noncomputable section

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The raw intrinsic modulus is the ratio of any actual rectangular model. -/
theorem intrinsicQuadrilateralModulus_eq_of_rectangular_model
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    (Q : IntrinsicQuadrilateral) {a b : ℝ}
    (h : LiZhongQC.EquivRect Q.dom Q.vert a b) :
    intrinsicQuadrilateralModulus Q = a / b := by
  let P : LiZhongQC.TopQuad := ⟨Q.dom, Q.vert,
    (intrinsicQuadrilateral_iff_presented hHard Q.isIntrinsic.2.1).1 Q.isIntrinsic⟩
  exact quadrilateralModulus_eq_of_rectangular_model P h

/-- Every intrinsic quadrilateral has a genuine rectangular model; any two such
models differ by positive scaling of their sides and give the same modulus. -/
theorem intrinsic_quadrilateral_rectangular_model_complete
    (hHard : Unproved.Quasiconformal.JordanBoundaryOrderComparison)
    (Q : IntrinsicQuadrilateral) :
    (∃ a b : ℝ, LiZhongQC.EquivRect Q.dom Q.vert a b) ∧
      ∀ a b c d : ℝ,
        LiZhongQC.EquivRect Q.dom Q.vert a b →
          LiZhongQC.EquivRect Q.dom Q.vert c d →
            (∃ r : ℝ, 0 < r ∧ c = r * a ∧ d = r * b) ∧ a / b = c / d := by
  let P : LiZhongQC.TopQuad := ⟨Q.dom, Q.vert,
    (intrinsicQuadrilateral_iff_presented hHard Q.isIntrinsic.2.1).1 Q.isIntrinsic⟩
  refine ⟨LiZhongQC.thm1_1_exists_rectangle P, ?_⟩
  intro a b c d h h'
  exact ⟨quadrilateral_rectangular_model_unique P h h',
    (intrinsicQuadrilateralModulus_eq_of_rectangular_model hHard Q h).symm.trans
      (intrinsicQuadrilateralModulus_eq_of_rectangular_model hHard Q h')⟩

end LowDimensionalTopology.Geometry.Quasiconformal
