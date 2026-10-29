module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalNativeTTQuadraticEquivalence
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHorizontalQuadraticTensors
public import LowDimensionalTopology.Geometry.Teichmuller.BasePointHarmonicTangent

/-!
# The actual horizontal image and original base-point tangent

The existing original harmonic tangent equivalence sends the literal harmonic
coefficient of each original quadratic differential to its genuine projection
derivative. The same quadratic differential gives the unchanged horizontal
tensor. Their actual inverse maps identify the two original carriers.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The canonical real action on the unchanged original symmetric-tensor submodule. -/
local instance canonicalHorizontalTangentTensorSMul :
    SMul ℝ (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact Submodule.smul (symmetricTwoTensorSubmodule R)

private def quadraticHorizontalEquiv :
    HolomorphicQuadraticDifferential R.toRiemannAtlas ≃
      {h : SmoothSymmetricTwoTensor R // h ∈ horizontalQuadraticTensors R} := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let f : HolomorphicQuadraticDifferential R.toRiemannAtlas →
      {h : SmoothSymmetricTwoTensor R // h ∈ horizontalQuadraticTensors R} :=
    fun Q => ⟨(2 : ℝ) • quadraticDifferentialTensor R Q, ⟨Q, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro Q S h
    apply quadraticDifferentialTensor_injective R
    have ht := congrArg Subtype.val h
    have hh := congrArg (fun t : SmoothSymmetricTwoTensor R => (1 / 2 : ℝ) • t) ht
    change (1 / 2 : ℝ) • ((2 : ℝ) • quadraticDifferentialTensor R Q) =
      (1 / 2 : ℝ) • ((2 : ℝ) • quadraticDifferentialTensor R S) at hh
    have htwo : (1 / 2 : ℝ) * 2 = 1 := by norm_num
    simpa only [smul_smul, htwo, one_smul] using hh
  have hsurj : Function.Surjective f := by
    intro h
    obtain ⟨Q, hQ⟩ := h.property
    exact ⟨Q, Subtype.ext hQ⟩
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

private def quadraticHarmonicEquiv
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    HolomorphicQuadraticDifferential R.toRiemannAtlas ≃
      NativePetersson.Harmonic R P p hp F hF := by
  let f : HolomorphicQuadraticDifferential R.toRiemannAtlas →
      NativePetersson.Harmonic R P p hp F hF := fun Q =>
    ⟨NativeHarmonicBeltrami.ofQuadratic R p hp Q,
      (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic R P p hp F hF _).mpr
        ⟨Q, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro Q S h
    have hv := congrArg Subtype.val h
    change NativeHarmonicBeltrami.ofQuadratic R p hp Q =
      NativeHarmonicBeltrami.ofQuadratic R p hp S at hv
    have hr := congrArg (fun μ : GammaMeasurableBeltrami.Space Γ =>
      NativePetersson.toQuadratic R P p hp F hF
        (NativePetersson.rieszQuadratic R P p hp F hF μ)) hv
    simpa only [NativePetersson.rieszQuadratic_ofQuadratic,
      LinearEquiv.apply_symm_apply] using hr
  have hsurj : Function.Surjective f := by
    intro μ
    obtain ⟨Q, hQ⟩ :=
      (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic R P p hp F hF μ.val).mp
        μ.property
    exact ⟨Q, Subtype.ext hQ⟩
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})

local notation "TI" => 𝓘(ℂ, Fin (3 * g - 3) → ℂ)
local notation "C" => TeichmullerSpace.canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "E" => TeichmullerSpace.baseTangentHarmonicEquiv
  R hg hgenus hΓ hfree hp hsmooth

/-- The same actual horizontal tensor image is in bijection with the tangent
at the original identity marking, through its literal harmonic coefficients. -/
@[no_expose] def horizontalOriginalTangentEquiv
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    letI := C
    {h : SmoothSymmetricTwoTensor R // h ∈ horizontalQuadraticTensors R} ≃
      TangentSpace TI (TeichmullerSpace.basePoint R) := by
  let := C
  exact (quadraticHorizontalEquiv R).symm.trans
    ((quadraticHarmonicEquiv R P p hp F hF).trans (E P F hF).symm.toEquiv)

/-- Every displayed horizontal tensor maps to the genuine derivative of the
original coefficient quotient projection in its actual harmonic direction. -/
theorem horizontalOriginalTangentEquiv_apply_quadratic
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    letI := C
    horizontalOriginalTangentEquiv R hg hgenus hΓ hfree hp hsmooth P F hF
        ⟨(2 : ℝ) • quadraticDifferentialTensor R Q, ⟨Q, rfl⟩⟩ =
      mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) TI
        (TeichmullerSpace.baseCoefficientProjection R hg hgenus hΓ hfree hp) 0
        (NativeHarmonicBeltrami.ofQuadratic R p hp Q) := by
  let := C
  let h : {t : SmoothSymmetricTwoTensor R // t ∈ horizontalQuadraticTensors R} :=
    ⟨(2 : ℝ) • quadraticDifferentialTensor R Q, ⟨Q, rfl⟩⟩
  have hback : (quadraticHorizontalEquiv R).symm h = Q :=
    (quadraticHorizontalEquiv R).symm_apply_apply Q
  change (E P F hF).symm
      (quadraticHarmonicEquiv R P p hp F hF ((quadraticHorizontalEquiv R).symm h)) = _
  rw [hback]
  apply (E P F hF).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,
    TeichmullerSpace.baseTangentHarmonicEquiv_derivative]
  apply Subtype.ext
  change NativeHarmonicBeltrami.ofQuadratic R p hp Q =
    NativePetersson.harmonicProjection R P p hp F hF
      (NativeHarmonicBeltrami.ofQuadratic R p hp Q)
  exact (NativePetersson.harmonicProjection_fixes_ofQuadratic R P p hp F hF Q).symm

end LowDimensionalTopology.Geometry.Teichmuller
