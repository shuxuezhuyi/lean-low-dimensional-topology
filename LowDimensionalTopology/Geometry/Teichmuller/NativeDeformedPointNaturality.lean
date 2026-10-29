module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeDeformedCoefficientNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientProjection
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge

/-!
# The same original marked-surface point has the same deformed coefficient codomain

The source fixed-point density premise is proved from the actual compact
uniformization. Equality refers to the independently defined coefficient
projection into the original native marked-surface quotient. Its normalized
source equivalence then gives the genuine source Teichmüller point equality.
The resulting native coefficient identification retains every actual class
and the unchanged infinity norm. No smoothing premise or unfinished handle
presentation is required for this codomain result.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

include R hp in
/-- The actual compact uniformization proves the density used in point naturality. -/
theorem native_fixedPoints_dense : Dense (LiZhongQC.fuchsianFixedPoints Γ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  exact LiZhongQC.fuchsianFixedPoints_dense hp

variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)

/-- Equality of the original native projection values is genuine source point equality. -/
theorem sourcePoint_eq_of_sameNativePoint (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν') :
    (Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν) :
        LiZhongQC.TeichGamma Γ) =
      Quotient.mk (LiZhongQC.teichSetoidGamma Γ) (toSourceGamma ν') := by
  let e := TeichmullerSpace.gammaEquiv R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp
  have he := congrArg e hpoint
  change e (e.symm (Quotient.mk _ (toSourceGamma ν))) =
    e (e.symm (Quotient.mk _ (toSourceGamma ν'))) at he
  exact (e.apply_symm_apply _).symm.trans (he.trans (e.apply_symm_apply _))

/-- Same original marked-surface point gives equality of actual deformed compatible submodules. -/
theorem compatibleSubmodule_eq_of_sameNativePoint (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν') :
    compatibleSubmodule (deformedGroup hΓ ν) =
      compatibleSubmodule (deformedGroup hΓ ν') :=
  compatibleSubmodule_eq_of_samePoint hΓ (native_fixedPoints_dense R hp) ν ν'
    (sourcePoint_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint)

/-- The true original-point deformed coefficient identification, using proved native density. -/
def nativePointDeformedCoefficientEquiv (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν') :
    Space (deformedGroup hΓ ν) ≃L[ℂ] Space (deformedGroup hΓ ν') :=
  deformedCoefficientEquiv hΓ (native_fixedPoints_dense R hp) ν ν'
    (sourcePoint_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint)

@[simp] theorem nativePointDeformedCoefficientEquiv_val (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν')
    (μ : Space (deformedGroup hΓ ν)) :
    (nativePointDeformedCoefficientEquiv R hp hg hgenus hΓ hfree ν ν' hpoint μ).val = μ.val :=
  deformedCoefficientEquiv_val hΓ (native_fixedPoints_dense R hp) ν ν' _ μ

/-- The actual original-point identification is isometric for the original infinity norm. -/
theorem norm_nativePointDeformedCoefficientEquiv (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν')
    (μ : Space (deformedGroup hΓ ν)) :
    ‖nativePointDeformedCoefficientEquiv R hp hg hgenus hΓ hfree ν ν' hpoint μ‖ = ‖μ‖ :=
  norm_deformedCoefficientEquiv hΓ (native_fixedPoints_dense R hp) ν ν' _ μ

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
