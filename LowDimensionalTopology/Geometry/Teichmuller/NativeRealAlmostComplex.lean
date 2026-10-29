module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealTangent

/-!
# The pointwise real almost-complex operator

The operator J is multiplication by i under the same-point real/holomorphic
tangent identification. This file constructs that real-linear operator and
its square. No smooth section or global bundle-regularity theorem is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
local notation "E" => Fin (3*g-3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "RI" => 𝓘(ℝ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "K" => nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth

/-- The actual same-point real tangent endomorphism K-inverse(i*K). -/
def nativeRealAlmostComplex (q : TeichmullerSpace.{0,0} R) :
    letI := C
    TangentSpace RI q →ₗ[ℝ] TangentSpace RI q := by
  let := C
  exact (K q).symm.toLinearEquiv.toLinearMap.comp
    (((LinearMap.lsmul ℂ (TangentSpace TI q) Complex.I).restrictScalars ℝ).comp
      (K q).toLinearEquiv.toLinearMap)

/-- The source's real operator squares to minus the identity in every native fibre. -/
theorem nativeRealAlmostComplex_sq (q : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v : TangentSpace RI q,
      nativeRealAlmostComplex R hp hg hgenus hΓ hfree hsmooth q
        (nativeRealAlmostComplex R hp hg hgenus hΓ hfree hsmooth q v) = -v := by
  let := C
  intro v
  simp only [nativeRealAlmostComplex, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearMap.lsmul_apply,
    LinearEquiv.coe_toLinearMap, ContinuousLinearEquiv.coe_toLinearEquiv]
  rw [(K q).apply_symm_apply, smul_smul, Complex.I_mul_I, neg_smul,
    one_smul, map_neg, (K q).symm_apply_apply]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
