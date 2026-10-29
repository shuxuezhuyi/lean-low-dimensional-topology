module

public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceWeilPeterssonCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCoefficientMatrix
public import LowDimensionalTopology.Unproved.Teichmuller.FiniteKahlerCoordinateCurvature

/-!
# Real curvature under the actual WP reference change

This concrete classical obligation concerns only the established native
coefficient matrices and the established deformed-reference coordinate map.
Importing the definition supplies no proof of its naturality assertion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller.TeichmullerSpace
open Geometry.Teichmuller.GammaMeasurableBeltrami Geometry.Teichmuller.NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "hP" => canonicalHandleGroupPresentation g
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "M" => nativeWeilPeterssonCoefficientMatrix
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

/-- The same real Koszul curvature is natural under the specific actual
reference isometry at its genuine coefficient centre. Target smoothness is
derived separately from the fixed original input, rather than assumed here. -/
def WeilPeterssonDeformedReferenceRealCurvatureNaturality : Prop :=
  ∀ ν : Ball Γ,
    let Y := deformedNativeSurface R hgenus hΓ hp ν
    let hpY := deformedNativeSurface_uniformization R hgenus hΓ hp ν
    let hY := deformedNativeSurface_hasGenus R hgenus hΓ hp ν
    let hΔ := (Geometry.Teichmuller.NormalizedCoefficientTransport.deformedGroup_spec hΓ ν).1
    let hfY := deformedNativeSurface_actsFreely R hgenus hΓ hp ν
    let MY := nativeWeilPeterssonCoefficientMatrix Y hpY hg hY hΔ hfY hsmooth (basePoint Y)
    let x := BC (β ν.val)
    let J := fderiv ℝ (deformedReferenceWeilPeterssonCoordinateMap R hp hg hgenus hΓ ν) x
    WeilPeterssonLocalCoefficientSmoothness R hp hg hgenus hΓ hfree hsmooth →
    ∀ u v w : E,
      J (FiniteKahlerCoordinateContract.realCurvature M x u v w) =
        FiniteKahlerCoordinateContract.realCurvature MY 0 (J u) (J v) (J w)

end LowDimensionalTopology.Unproved.Teichmuller
