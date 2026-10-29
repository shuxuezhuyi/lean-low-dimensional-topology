module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeNonzeroCoefficientProjectionDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedNativeTarget

/-!
# The original nonzero derivative quotient and actual marked-surface tangent

The kernel is that of the genuine nonzero Bers derivative on all original
compatible coefficients. Surjectivity follows from the actual deformed Bers
integral and the two proved genuine linear equivalences. The resulting
quotient retains its original L-infinity quotient norm. Its original tangent
identification is induced by the manifold derivative of the independently
defined marked-surface coefficient projection at the actual coefficient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)

/-- The actual entire nonzero derivative kernel, with its original coefficient-space norm. -/
def nonzeroInfinitesimalSubmodule : Submodule ℂ (Space Γ) :=
  (nonzeroBersDerivative R hp hg hgenus hΓ ν).ker

instance nonzeroInfinitesimalSubmodule_isClosed :
    IsClosed (nonzeroInfinitesimalSubmodule R hp hg hgenus hΓ ν : Set (Space Γ)) :=
  (nonzeroBersDerivative R hp hg hgenus hΓ ν).isClosed_ker

/-- The original L-infinity quotient by the genuine derivative kernel at the actual coefficient. -/
abbrev NonzeroTangentQuotient := Space Γ ⧸ nonzeroInfinitesimalSubmodule R hp hg hgenus hΓ ν

/-- The kernel is that of the independently defined actual Bers projection at nu. -/
theorem mem_nonzeroInfinitesimalSubmodule_iff_fderiv (μ : Space Γ) :
    μ ∈ nonzeroInfinitesimalSubmodule R hp hg hgenus hΓ ν ↔
      fderiv ℂ (BersWeighted.automorphicProjection hΓ) ν.val μ = 0 := by
  rw [fderiv_automorphicProjection_nonzero R hp hg hgenus hΓ ν]
  rfl

/-- Every original automorphic target direction has an actual nonzero derivative preimage. -/
theorem nonzeroBersDerivative_surjective :
    Function.Surjective (nonzeroBersDerivative R hp hg hgenus hΓ ν) := by
  intro φ
  let Y := deformedNativeSurface R hgenus hΓ hp ν
  let q := deformedTargetCover R hgenus hΓ hp ν
  have hq := deformedNativeSurface_uniformization R hgenus hΓ hp ν
  let e := inverseBersDerivativeEquiv R hp hg hgenus hΓ ν
  obtain ⟨κ, hκ⟩ := BersWeighted.automorphicIntegralOperator_surjective Y q hq
    (deformedGroup_spec hΓ ν).1 (e.symm φ)
  refine ⟨gammaInverse hΓ ν κ, ?_⟩
  change e ((BersWeighted.automorphicIntegralOperator (deformedGroup_spec hΓ ν).1)
    (gammaDerivative hΓ ν (gammaInverse hΓ ν κ))) = φ
  rw [gammaDerivative_gammaInverse, hκ]
  exact e.apply_symm_apply φ

/-- The actual derivative descends through its exact original closed kernel. -/
def quotientNonzeroDerivative :
    NonzeroTangentQuotient R hp hg hgenus hΓ ν →L[ℂ] BersWeighted.Automorphic Γ :=
  (nonzeroInfinitesimalSubmodule R hp hg hgenus hΓ ν).liftQL
    (nonzeroBersDerivative R hp hg hgenus hΓ ν) le_rfl

theorem quotientNonzeroDerivative_ker :
    (quotientNonzeroDerivative R hp hg hgenus hΓ ν).ker = ⊥ :=
  Submodule.ker_liftQ_eq_bot (nonzeroInfinitesimalSubmodule R hp hg hgenus hΓ ν)
    (nonzeroBersDerivative R hp hg hgenus hΓ ν).toLinearMap le_rfl le_rfl

/-- The descended derivative is a genuine equivalence in the original quotient and weighted norms. -/
def nonzeroDerivativeQuotientEquiv :
    NonzeroTangentQuotient R hp hg hgenus hΓ ν ≃L[ℂ] BersWeighted.Automorphic Γ := by
  letI : CompleteSpace (BersWeighted.Automorphic Γ) := BersWeighted.automorphic_completeSpace Γ
  have hs : Function.Surjective (quotientNonzeroDerivative R hp hg hgenus hΓ ν) := by
    intro φ
    obtain ⟨μ, hμ⟩ := nonzeroBersDerivative_surjective R hp hg hgenus hΓ ν φ
    exact ⟨Submodule.Quotient.mk μ, hμ⟩
  exact ContinuousLinearEquiv.ofBijective (quotientNonzeroDerivative R hp hg hgenus hΓ ν)
    (quotientNonzeroDerivative_ker R hp hg hgenus hΓ ν) (LinearMap.range_eq_top.mpr hs)

@[simp] theorem nonzeroDerivativeQuotientEquiv_apply_mk (μ : Space Γ) :
    nonzeroDerivativeQuotientEquiv R hp hg hgenus hΓ ν (Submodule.Quotient.mk μ) =
      nonzeroBersDerivative R hp hg hgenus hΓ ν μ := rfl

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces NormalizedCoefficientTransport

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (ν : GammaMeasurableBeltrami.Ball Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})

/-- The genuine original quotient identifies with the tangent at the actual original marked point. -/
def nonzeroDerivativeQuotientTangentEquiv :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    NonzeroTangentQuotient R hp hg hgenus hΓ ν ≃L[ℂ]
      TangentSpace 𝓘(ℂ, Fin (3 * g - 3) → ℂ)
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val) :=
  (nonzeroDerivativeQuotientEquiv R hp hg hgenus hΓ ν).trans
    (canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
      (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val)).symm

/-- This tangent identification is induced by the actual original projection derivative. -/
theorem nonzeroDerivativeQuotientTangentEquiv_apply_mk (μ : GammaMeasurableBeltrami.Space Γ) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    nonzeroDerivativeQuotientTangentEquiv R hp hg hgenus hΓ hfree ν hsmooth
        (Submodule.Quotient.mk μ) =
      mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ)
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp) ν.val μ := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  let e := canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
    (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val)
  apply e.injective
  change e (e.symm (nonzeroDerivativeQuotientEquiv R hp hg hgenus hΓ ν
    (Submodule.Quotient.mk μ))) = _
  rw [e.apply_symm_apply, nonzeroDerivativeQuotientEquiv_apply_mk]
  exact (canonicalBersTangentEquiv_mfderiv_coefficientProjection_nonzero R hg hgenus
    hΓ hfree hp hsmooth ν μ).symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
