module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.QuotientMetric
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.PoincareLineElement
public import Mathlib.Tactic.Linarith

/-!
# Bilinear invariance of the disk Poincaré tensor

The actual differential of a normalized disk Möbius map preserves the full real
bilinear tensor. This follows by polarizing the existing all-vector line-element
identity and supplies the tensor covariance needed for covering-branch descent.
-/

@[expose] public section
noncomputable section

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Hyperbolic

/-- Squaring the existing normalized-disc line-element identity gives its
literal Poincaré tensor identity on every diagonal vector. -/
theorem normalizedDisc_discPoincareTensor_self
    (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1)
    (z : Complex.UnitDisc) (v : ℂ) :
    discPoincareTensor (discFractionalHomeomorph a c hdet z : ℂ)
      (deriv (discFractionalMap a c) (z : ℂ) * v)
      (deriv (discFractionalMap a c) (z : ℂ) * v) =
        discPoincareTensor (z : ℂ) v v := by
  rw [discPoincareTensor_self, discPoincareTensor_self]
  have h := congrArg (fun t : ℝ => t ^ 2)
    (normalizedDisc_tangentNorm a c hdet z v)
  simpa only [discHyperbolicTangentNorm_formula, div_pow, mul_pow,
    show (2 : ℝ) ^ 2 = 4 by norm_num] using h

/-- The actual normalized-disc derivative preserves both slots of the literal
Poincaré tensor. Real polarization supplies the bilinear identity. -/
theorem normalizedDisc_discPoincareTensor_pullback
    (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1)
    (z : Complex.UnitDisc) (v w : ℂ) :
    discPoincareTensor (discFractionalHomeomorph a c hdet z : ℂ)
      (deriv (discFractionalMap a c) (z : ℂ) * v)
      (deriv (discFractionalMap a c) (z : ℂ) * w) =
        discPoincareTensor (z : ℂ) v w := by
  have h := normalizedDisc_discPoincareTensor_self a c hdet z (v + w)
  simp only [mul_add, map_add, add_apply] at h
  rw [discPoincareTensor_symmetric (discFractionalHomeomorph a c hdet z : ℂ)
    (deriv (discFractionalMap a c) (z : ℂ) * w)
    (deriv (discFractionalMap a c) (z : ℂ) * v),
    discPoincareTensor_symmetric (z : ℂ) w v] at h
  linarith [normalizedDisc_discPoincareTensor_self a c hdet z v,
    normalizedDisc_discPoincareTensor_self a c hdet z w]

end LowDimensionalTopology.Geometry.Surfaces
