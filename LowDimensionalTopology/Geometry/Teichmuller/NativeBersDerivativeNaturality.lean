module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeNonzeroBersDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.NativeDeformedBersNaturality
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# The actual coordinate derivative is natural at the original Teichmüller point

Equality of the independently defined original projection values gives equality
of their actual weighted Bers points through the existing coordinate map.
The whole coordinate translations agree after the proved identity isometry
between their actual deformed weighted spaces. Differentiating this genuine
function equality at that same original point gives derivative naturality.

Every operator is the already proved actual Fréchet derivative, with the
original weighted norms and the exact normalized deformed groups retained.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)

/-- The original projection coordinates retain the actual weighted Bers base point. -/
theorem baseBersValue_eq_of_sameNativePoint (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν') :
    baseBersValue hΓ ν = baseBersValue hΓ ν' := by
  apply (TeichmullerSpace.weightedLinearBersCoordinates R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hp).injective
  have he := congrArg (TeichmullerSpace.bersCoordinates R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp) hpoint
  rw [TeichmullerSpace.coefficientProjectionBall_coordinates R hg hgenus
      (canonicalHandleGroupPresentation g) hΓ hfree hp ν,
    TeichmullerSpace.coefficientProjectionBall_coordinates R hg hgenus
      (canonicalHandleGroupPresentation g) hΓ hfree hp ν'] at he
  exact he

/-- The genuine inverse-coordinate derivatives are natural under the actual identity isometry. -/
theorem nativePointDeformedBersEquiv_comp_inverseBersDerivativeEquiv_symm (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν') :
    (nativePointDeformedBersEquiv R hp hg hgenus hΓ hfree ν ν' hpoint).toContinuousLinearMap.comp
        (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm.toContinuousLinearMap =
      (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν').symm.toContinuousLinearMap := by
  let I := nativePointDeformedBersEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
  have hmaps : (fun φ : BersWeighted.Automorphic Γ => I (bersTranslation hΓ ν φ)) =
      bersTranslation hΓ ν' := by
    funext φ
    exact nativePointDeformedBersEquiv_bersTranslation R hp hg hgenus hΓ hfree ν ν' hpoint φ
  have hcomp : HasFDerivAt (fun φ : BersWeighted.Automorphic Γ => I (bersTranslation hΓ ν φ))
      (I.toContinuousLinearMap.comp
        (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm.toContinuousLinearMap)
      (baseBersValue hΓ ν) :=
    I.toContinuousLinearMap.hasFDerivAt.comp (baseBersValue hΓ ν)
      (hasFDerivAt_bersTranslation R hp hg hgenus hΓ ν)
  rw [hmaps] at hcomp
  have hbase := baseBersValue_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint
  have hother : HasFDerivAt (bersTranslation hΓ ν')
      (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν').symm.toContinuousLinearMap
      (baseBersValue hΓ ν) := by
    rw [hbase]
    exact hasFDerivAt_bersTranslation R hp hg hgenus hΓ ν'
  exact hcomp.unique hother

/-- Actual derivatives of the whole coordinate maps agree at the same original point. -/
theorem nativePointDeformedBersEquiv_comp_fderiv_bersTranslation (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν') :
    (nativePointDeformedBersEquiv R hp hg hgenus hΓ hfree ν ν' hpoint).toContinuousLinearMap.comp
        (fderiv ℂ (bersTranslation hΓ ν) (baseBersValue hΓ ν)) =
      fderiv ℂ (bersTranslation hΓ ν') (baseBersValue hΓ ν') := by
  rw [fderiv_bersTranslation R hp hg hgenus hΓ ν,
    fderiv_bersTranslation R hp hg hgenus hΓ ν']
  exact nativePointDeformedBersEquiv_comp_inverseBersDerivativeEquiv_symm
    R hp hg hgenus hΓ hfree ν ν' hpoint

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
