module

public import LowDimensionalTopology.Geometry.Teichmuller.RectangleExtremality
public import LowDimensionalTopology.Geometry.Teichmuller.RectangleExtremalBeltramiProof

/-!
# Unique affine extremality for a closed rectangle

The actual almost-everywhere equality producer supplies the analytic
step internally. The conclusion concerns the literal maximal dilatation
and equality of the actual maps on the whole closed rectangle.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set LiZhongQC
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- Every admissible quasiconformal rectangle map has maximal dilatation
at least the affine value. Equality holds exactly when its actual closed
extension equals the affine map on the closed rectangle. -/
theorem rectangle_unique_extremal_unconditional
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) {h : ℂ → ℂ}
    (hqc : IsQuasiconformal h (rectangle r 1))
    (himg : h '' rectangle r 1 = rectangle s 1) {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h (rectangle r 1) (rectangle s 1) H)
    (hv : ∀ i, H (rectVert r 1 i) = rectVert s 1 i) :
    ENNReal.ofReal (s / r) ≤ maxDilatation h (rectangle r 1) ∧
      (maxDilatation h (rectangle r 1) = ENNReal.ofReal (s / r) ↔
        EqOn H (OnePoint.map (affineStretch r s)) (closure (toExt (rectangle r 1)))) :=
  rectangle_unique_extremal rectangleExtremalBeltrami hr hrs hqc himg hH hv

end LowDimensionalTopology.Geometry.Teichmuller
