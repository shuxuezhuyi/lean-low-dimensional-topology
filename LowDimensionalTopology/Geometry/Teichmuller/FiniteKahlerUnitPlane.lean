module

public import LowDimensionalTopology.Geometry.Teichmuller.FiniteKahlerCurvatureNotions
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-! Unit directions and the real Gram denominator of their actual J-planes. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.FiniteKahlerCurvatureNotions
open LowDimensionalTopology.Unproved.Teichmuller.FiniteKahlerCoordinateContract

private theorem hermitian_smul_smul {n : ℕ} (H : Coeff n) (x u v : E n) (a b : ℂ) :
    hermitian H x (a • u) (b • v) = a * conj b * hermitian H x u v := by
  simp only [hermitian, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem metric_smul_smul_of_unit {n : ℕ} (H : Coeff n) (x v : E n)
    (hunit : hermitian H x v v = 1) (a b : ℂ) :
    metric H x (a • v) (b • v) = 2 * (a * conj b).re := by
  rw [metric, hermitian_smul_smul, hunit, mul_one]

/-- A unit Hermitian direction spans a real orthogonal J-plane with both squared lengths two. -/
theorem unitPlane_metric_values {n : ℕ} (H : Coeff n) (x v : E n)
    (hunit : hermitian H x v v = 1) :
    metric H x v v = 2 ∧
      metric H x v (Complex.I • v) = 0 ∧
      metric H x (Complex.I • v) (Complex.I • v) = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using metric_smul_smul_of_unit H x v hunit (1 : ℂ) (1 : ℂ)
  · simpa using metric_smul_smul_of_unit H x v hunit (1 : ℂ) Complex.I
  · simpa using metric_smul_smul_of_unit H x v hunit Complex.I Complex.I

/-- For g = 2 Re h the actual Gram denominator of a unit direction's J-plane is four. -/
theorem unitPlane_gram_denominator {n : ℕ} (H : Coeff n) (x v : E n)
    (hunit : hermitian H x v v = 1) :
    metric H x v v * metric H x (Complex.I • v) (Complex.I • v) -
      (metric H x v (Complex.I • v)) ^ 2 = 4 := by
  rcases unitPlane_metric_values H x v hunit with ⟨hvv, hvI, hII⟩
  rw [hvv, hvI, hII]
  norm_num

/-- The existing actual J-plane quotient is its same real-curvature numerator divided by four. -/
theorem holomorphicSectional_eq_numerator_div_four_of_unit {n : ℕ}
    (H : Coeff n) (x v : E n) (hunit : hermitian H x v v = 1) :
    holomorphicSectional H x v =
      metric H x (realCurvature H x v (Complex.I • v) (Complex.I • v)) v / 4 := by
  unfold holomorphicSectional
  rw [unitPlane_gram_denominator H x v hunit]

end LowDimensionalTopology.Geometry.Teichmuller.FiniteKahlerCurvatureNotions
