module

public import LowDimensionalTopology.Unproved.Teichmuller.FiniteKahlerCoordinateCurvature

/-! Generic finite-coordinate curvature notions.
The metric is `g = 2 Re h`; source directions are Hermitian unit vectors.
Geometric interpretation and reality use the explicit classical comparison. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped ContDiff ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace LowDimensionalTopology.Geometry.Teichmuller.FiniteKahlerCurvatureNotions
open LowDimensionalTopology.Unproved.Teichmuller.FiniteKahlerCoordinateContract

/-- The real sectional quotient of the actual plane spanned by `v` and `i v`.
Its geometric use requires a genuine smooth positive Hermitian metric. -/
def holomorphicSectional {n : ℕ} (H : Coeff n) (x v : E n) : ℝ :=
  metric H x (realCurvature H x v (Complex.I • v) (Complex.I • v)) v /
    (metric H x v v * metric H x (Complex.I • v) (Complex.I • v) -
      (metric H x v (Complex.I • v)) ^ 2)

/-- Negative normalized real Ricci at every domain point and every H-unit direction. -/
def NegativeRicciOn {n : ℕ} (H : Coeff n) (domain : Set (E n)) : Prop :=
  ∀ x ∈ domain, ∀ v : E n, hermitian H x v v = 1 →
    realRicci H x v v / metric H x v v < 0

/-- Negative actual J-plane curvature at every domain point and H-unit direction. -/
def NegativeHolomorphicSectionalOn {n : ℕ} (H : Coeff n) (domain : Set (E n)) : Prop :=
  ∀ x ∈ domain, ∀ v : E n, hermitian H x v v = 1 → holomorphicSectional H x v < 0

variable {n : ℕ} (H : Coeff n) (domain : Set (E n))
    (hclassical : ClassicalFiniteKahlerCoordinateCurvature)
    (hopen : IsOpen domain) (hsmooth : ContDiffOn ℝ ∞ H domain)
    (hpos : ∀ x ∈ domain, (H x).PosDef)
    (hclosed : ∀ x ∈ domain, ∀ u v w : E n,
      fderiv ℝ (fun t => omega H t v w) x u -
        fderiv ℝ (fun t => omega H t u w) x v +
        fderiv ℝ (fun t => omega H t u v) x w = 0)

include hclassical hopen hsmooth hpos hclosed

/-- On source unit directions, both real curvatures equal the real source formulas;
the source formulas themselves are real under the same classical hypotheses. -/
theorem sourceUnitCurvatures (x : E n) (hx : x ∈ domain) (v : E n)
    (hunit : hermitian H x v v = 1) :
    (realRicci H x v v / metric H x v v = (ricciQ H x v).re ∧
      (ricciQ H x v).im = 0) ∧
    (holomorphicSectional H x v = -(lower4 H x v v v v).re ∧
      (lower4 H x v v v v).im = 0) := by
  have h := (hclassical n domain H hopen hsmooth hpos hclosed).2 x hx
  rcases h with ⟨_, _, _, _, _, hLower, hRic, _, hPlane⟩
  refine ⟨⟨?_, (hRic v).1⟩, ⟨?_, hLower v v⟩⟩
  · rw [(hRic v).2, metric, hunit]
    simp only [Complex.one_re, mul_one]
    exact mul_div_cancel_left₀ _ two_ne_zero
  · have hv : v ≠ 0 := by
      intro hv
      subst v
      simp [hermitian] at hunit
    simpa only [holomorphicSectional, hunit, Complex.one_re, one_pow, div_one]
      using hPlane v hv

/-- The geometric domain predicate agrees with the book Ricci inequality. -/
theorem negativeRicciOn_iff_book :
    NegativeRicciOn H domain ↔
      ∀ x ∈ domain, ∀ v : E n, hermitian H x v v = 1 → (ricciQ H x v).re < 0 := by
  unfold NegativeRicciOn
  constructor
  · intro h x hx v hv
    rw [← (sourceUnitCurvatures H domain hclassical hopen hsmooth hpos hclosed x hx v hv).1.1]
    exact h x hx v hv
  · intro h x hx v hv
    rw [(sourceUnitCurvatures H domain hclassical hopen hsmooth hpos hclosed x hx v hv).1.1]
    exact h x hx v hv

/-- The geometric domain predicate agrees with the source's leading-minus quartic. -/
theorem negativeHolomorphicSectionalOn_iff_book :
    NegativeHolomorphicSectionalOn H domain ↔
      ∀ x ∈ domain, ∀ v : E n, hermitian H x v v = 1 →
        -(lower4 H x v v v v).re < 0 := by
  unfold NegativeHolomorphicSectionalOn
  constructor
  · intro h x hx v hv
    rw [← (sourceUnitCurvatures H domain hclassical hopen hsmooth hpos hclosed x hx v hv).2.1]
    exact h x hx v hv
  · intro h x hx v hv
    rw [(sourceUnitCurvatures H domain hclassical hopen hsmooth hpos hclosed x hx v hv).2.1]
    exact h x hx v hv

end LowDimensionalTopology.Geometry.Teichmuller.FiniteKahlerCurvatureNotions
