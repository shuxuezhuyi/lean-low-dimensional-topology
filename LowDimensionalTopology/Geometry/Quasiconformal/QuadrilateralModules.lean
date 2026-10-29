module

public import LowDimensionalTopology.Geometry.Quasiconformal.AnalyticGeometric

/-!
# Rectangular models and quasiconformal distortion of quadrilateral moduli

A marked quadrilateral has an actual Jordan boundary and four positively ordered
vertices. Its conformal rectangular model includes an actual continuous,
injective and surjective extension to the boundary. The modulus is a/b, with
this order fixed throughout; it is not silently replaced by its reciprocal.

The rectangular-model and modulus proofs reused here are due to Wu Xiaobin,
from commit 1c0d5473c020b66ed5106331a38a61536760b9b2. The external source
manifest retains the complete authorship, license and compatibility changes.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- A genuine marked Jordan quadrilateral, with positively cyclic vertices. -/
abbrev MarkedQuadrilateral := LiZhongQC.TopQuad

/-- The rectangular modulus is a/b, chosen from actual conformal rectangular models. -/
def quadrilateralModulus (Q : MarkedQuadrilateral) : ℝ := Q.modulus

/-- Every marked quadrilateral has a genuine conformal rectangular model. -/
theorem quadrilateral_rectangular_model (Q : MarkedQuadrilateral) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ (f : ℂ → ℂ) (F : LiZhongQC.ExtPlane → LiZhongQC.ExtPlane),
      LiZhongQC.IsConformalOnto f Q.dom (LiZhongQC.rectangle a b) ∧
        LiZhongQC.IsHomeoExtension f Q.dom (LiZhongQC.rectangle a b) F ∧
          ∀ i, F (Q.vert i) = LiZhongQC.rectVert a b i := by
  obtain ⟨a, b, f, ha, hb, hf, F, hF, hv⟩ := LiZhongQC.thm1_1_exists_rectangle Q
  exact ⟨a, b, ha, hb, f, F, hf, hF, hv⟩

/-- Any two conformal rectangular models differ by a positive similarity. -/
theorem quadrilateral_rectangular_model_unique (Q : MarkedQuadrilateral)
    {a b c d : ℝ} (h : Q.EquivRect a b) (h' : Q.EquivRect c d) :
    ∃ r : ℝ, 0 < r ∧ c = r * a ∧ d = r * b :=
  LiZhongQC.thm1_1_rectangle_unique Q h h'

/-- Every actual rectangular model gives the same quotient a/b. -/
theorem quadrilateralModulus_eq_of_rectangular_model (Q : MarkedQuadrilateral)
    {a b : ℝ} (h : Q.EquivRect a b) : quadrilateralModulus Q = a / b :=
  LiZhongQC.modulus_eq_of_equivRect Q h

/-- The modulus of a genuine marked quadrilateral is positive. -/
theorem quadrilateralModulus_pos (Q : MarkedQuadrilateral) : 0 < quadrilateralModulus Q :=
  LiZhongQC.modulus_pos Q

/-- The same actual quadrilateral image satisfies both quasiconformal modulus bounds. -/
theorem quadrilateral_modulus_bounds_geometric {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f D K) (Q : MarkedQuadrilateral)
    (hQ : closure (LiZhongQC.toExt Q.dom) ⊆ LiZhongQC.toExt D) :
    ∃ Q' : MarkedQuadrilateral, Q.IsImageUnder Q' f ∧
      quadrilateralModulus Q / K ≤ quadrilateralModulus Q' ∧
        quadrilateralModulus Q' ≤ K * quadrilateralModulus Q := by
  obtain ⟨Q', hQ', _⟩ := hf.2.2.2 Q hQ
  exact ⟨Q', hQ', LiZhongQC.IsKQC.modulus_ge hf Q Q' hQ hQ'⟩

/-- Analytic quasiconformality gives the full two-sided geometric modulus estimate. -/
theorem quadrilateral_modulus_bounds_analytic {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : IsAnalyticallyKQuasiconformal f D K) (Q : MarkedQuadrilateral)
    (hQ : closure (LiZhongQC.toExt Q.dom) ⊆ LiZhongQC.toExt D) :
    ∃ Q' : MarkedQuadrilateral, Q.IsImageUnder Q' f ∧
      quadrilateralModulus Q / K ≤ quadrilateralModulus Q' ∧
        quadrilateralModulus Q' ≤ K * quadrilateralModulus Q :=
  quadrilateral_modulus_bounds_geometric (geometric_iff_analytic.mpr hf) Q hQ

/-- Conformal maps preserve the actual quadrilateral modulus. -/
theorem quadrilateralModulus_conformal_invariant {Q Q' : MarkedQuadrilateral}
    (h : Q.ConfEquiv Q') : quadrilateralModulus Q = quadrilateralModulus Q' :=
  LiZhongQC.thm1_3_modulus_conformal_invariant h

end LowDimensionalTopology.Geometry.Quasiconformal
