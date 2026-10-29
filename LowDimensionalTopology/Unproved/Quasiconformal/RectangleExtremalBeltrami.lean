module

public import LowDimensionalTopology.External.LiZhongQC.Ch07.S26_TeichmullerUniqueness

/-!
# The general rectangle equality step

Equality in the length–area estimate forces the complex dilatation to be
the real affine stretch parameter almost everywhere. The existing rectangle
equality theorem assumes C¹ regularity. This proposition records the
missing step for general quasiconformal maps. It is an explicit proposition,
with no axiom or claimed proof.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory

namespace LowDimensionalTopology.Unproved.Quasiconformal

/-- Equality in the general quasiconformal rectangle length–area argument
forces the constant Beltrami coefficient. The actual homeomorphic boundary
extension, including its ordered vertices, is retained. -/
def RectangleExtremalBeltrami : Prop :=
  ∀ (r s : ℝ), 0 < r → r ≤ s →
    ∀ (h : ℂ → ℂ) (H : LiZhongQC.ExtPlane → LiZhongQC.ExtPlane),
      LiZhongQC.IsKQC h (LiZhongQC.rectangle r 1) (s / r) →
      h '' LiZhongQC.rectangle r 1 = LiZhongQC.rectangle s 1 →
      LiZhongQC.IsHomeoExtension h (LiZhongQC.rectangle r 1)
        (LiZhongQC.rectangle s 1) H →
      (∀ i, H (LiZhongQC.rectVert r 1 i) = LiZhongQC.rectVert s 1 i) →
        ∀ᵐ z ∂(volume.restrict (LiZhongQC.rectangle r 1)),
          LiZhongQC.complexDilatation h z = (((s / r - 1) / (s / r + 1) : ℝ) : ℂ)

end LowDimensionalTopology.Unproved.Quasiconformal
