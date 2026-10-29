module

public import LowDimensionalTopology.External.LiZhongQC.Basic

/-!
# Intrinsic positively ordered Jordan quadrilaterals

The data use only a genuine circle parametrization, ordered parameters and
an actual winding lift about an interior point. No analytic presentation,
rectangle model or quasiconformal classification is included.
-/

@[expose] public section
noncomputable section

open Set Metric
open scoped Topology OnePoint

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Four vertices encountered in order on a positively winding Jordan loop. -/
def HasPositiveJordanVertexOrder (D : Set ℂ) (v : Fin 4 → LiZhongQC.ExtPlane) : Prop :=
  ∃ γ : Circle → ℂ, Continuous γ ∧ Function.Injective γ ∧ range γ = frontier D ∧
    ∃ t : Fin 4 → ℝ, StrictMono t ∧ (∀ i, 0 ≤ t i ∧ t i < 1) ∧
      (∀ i, v i = (γ (Circle.exp (2 * Real.pi * t i)) : LiZhongQC.ExtPlane)) ∧
      ∃ p ∈ D, ∃ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) ∧
        (∀ s ∈ Icc (0 : ℝ) 1,
          Complex.exp (L s) = γ (Circle.exp (2 * Real.pi * s)) - p) ∧
        L 1 - L 0 = 2 * (Real.pi : ℂ) * Complex.I

/-- A bounded Jordan region with four genuinely positively ordered vertices. -/
def IsIntrinsicQuadrilateral (D : Set ℂ) (v : Fin 4 → LiZhongQC.ExtPlane) : Prop :=
  LiZhongQC.IsJordanDomain D ∧ Bornology.IsBounded D ∧
    (∀ i, v i ∈ frontier (LiZhongQC.toExt D)) ∧ HasPositiveJordanVertexOrder D v

structure IntrinsicQuadrilateral where
  dom : Set ℂ
  vert : Fin 4 → LiZhongQC.ExtPlane
  isIntrinsic : IsIntrinsicQuadrilateral dom vert

def IntrinsicQuadrilateral.IsImageUnder
    (Q Q' : IntrinsicQuadrilateral) (f : ℂ → ℂ) : Prop :=
  Q'.dom = f '' Q.dom ∧ ∀ i, Q'.vert i = OnePoint.map f (Q.vert i)

end LowDimensionalTopology.Geometry.Quasiconformal
