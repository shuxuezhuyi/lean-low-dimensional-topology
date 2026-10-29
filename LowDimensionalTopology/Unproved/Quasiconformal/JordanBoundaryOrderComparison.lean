module

public import LowDimensionalTopology.Geometry.Quasiconformal.IntrinsicQuadrilateralData

/-!
# Boundary order of an actual Jordan uniformizer

This concrete proposition compares genuine positive winding order with the
finite real boundary order of an actual conformal uniformizer. Importing the
definition supplies no proof. Analytic existence of the uniformizer is separate.
-/

@[expose] public section
noncomputable section

open Set

namespace LowDimensionalTopology.Unproved.Quasiconformal

open Geometry.Quasiconformal

/-- Concrete missing boundary-orientation theorem. The analytic uniformizer
and its genuine homeomorphic extension are given; only the independent
positive winding order is compared with the finite real boundary coordinates. -/
def JordanBoundaryOrderComparison : Prop :=
  ∀ (D : Set ℂ) (v : Fin 4 → LiZhongQC.ExtPlane),
    LiZhongQC.IsJordanDomain D → Bornology.IsBounded D →
    (∀ i, v i ∈ frontier (LiZhongQC.toExt D)) →
    ∀ (φ : ℂ → ℂ) (Φ : LiZhongQC.ExtPlane → LiZhongQC.ExtPlane) (x : Fin 4 → ℝ),
      LiZhongQC.IsConformalOnto φ D LiZhongQC.upperHalf →
      LiZhongQC.IsHomeoExtension φ D LiZhongQC.upperHalf Φ →
      (∀ i, Φ (v i) = (((x i : ℝ) : ℂ) : LiZhongQC.ExtPlane)) →
      (HasPositiveJordanVertexOrder D v ↔ ∃ k : Fin 4, StrictMono (fun i => x (i + k)))

end LowDimensionalTopology.Unproved.Quasiconformal
