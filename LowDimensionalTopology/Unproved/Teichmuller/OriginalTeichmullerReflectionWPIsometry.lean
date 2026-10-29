module

public import LowDimensionalTopology.Geometry.Teichmuller.CompactQCMetricTopologyTransport
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMarkedReflectionInvolution
public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonRealTangentForm

/-!
# The concrete WP metric assertion for the same original marked reflection

The map is the existing original marked-quotient reflection, read through its
actual original group homeomorphism. The metric is the existing real WP form
on the actual real tangent fibres, and the operator is the real manifold
derivative of that same map. No pairing or tangent transport is supplied.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Unproved.Teichmuller

open LowDimensionalTopology.Geometry
open LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Teichmuller
open GeneralQC TeichmullerSpace GammaMeasurableBeltrami

/-- The actual given-J reflection preserves the original real Weil-Petersson metric. -/
def OriginalTeichmullerReflectionWPIsometry
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ)
    (J : X ≃ₜ X)
    (hJ : @LiZhongQC.IsAnticonformalInvolution X inferInstance
      R.toRiemannAtlas.toChartedSpace J)
    (hsmooth : QuasiconformalSmoothing.{0}) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  letI : TopologicalSpace (ClosedSpace R) :=
    GeneralQC.distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface)
  letI := gammaQCMetricSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  letI := gammaBersChartedSpace R hg hgenus hΓ (LiZhongQC.s27g_actsFreely hp) hp
  let HR := closedGammaHomeomorph R hg hgenus hΓ hp
  let rΓ : LiZhongQC.TeichGamma Γ → LiZhongQC.TeichGamma Γ := fun a =>
    HR (originalTeichmullerReflection R J hJ (HR.symm a))
  ∀ (a : LiZhongQC.TeichGamma Γ)
    (v w : TangentSpace 𝓘(ℝ, Fin (3 * g - 3) → ℂ) a),
    gammaWeilPeterssonRealTangentForm R hp hg hgenus hΓ hsmooth (rΓ a)
      (mfderiv 𝓘(ℝ, Fin (3 * g - 3) → ℂ) 𝓘(ℝ, Fin (3 * g - 3) → ℂ) rΓ a v)
      (mfderiv 𝓘(ℝ, Fin (3 * g - 3) → ℂ) 𝓘(ℝ, Fin (3 * g - 3) → ℂ) rΓ a w) =
      gammaWeilPeterssonRealTangentForm R hp hg hgenus hΓ hsmooth a v w

end LowDimensionalTopology.Unproved.Teichmuller
