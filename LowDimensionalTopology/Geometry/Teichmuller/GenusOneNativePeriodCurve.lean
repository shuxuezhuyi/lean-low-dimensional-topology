module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneNativePeriodBasis
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The actual marked-torus family has the native period basis as derivative

Differentiability is read in the original quotient's actual period chart. The
chain rule identifies the derivative of the literal marked family with the
coordinate basis, at the actual value of that same curve at zero.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces

/-- The original normalized marked-family curve is differentiable at zero. -/
theorem mdifferentiableAt_nativePeriodCurve_zero (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀) (τ : ℍ) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun t : ℂ => normalizedFamilyPoint τ₀ (nearbyPeriod τ t)) 0 := by
  let := nativePeriodChartedSpace τ₀ hperiod
  let f : ℂ → TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) :=
    fun t => normalizedFamilyPoint τ₀ (nearbyPeriod τ t)
  have hcoord : HasDerivAt (nativePeriodChart τ₀ hperiod ∘ f) 1 0 :=
    hasDerivAt_nativePeriodChart_nearbyFamily τ₀ hperiod τ
  have hcont : ContinuousAt f 0 :=
    ((nativePeriodChart τ₀ hperiod).continuousAt_iff_continuousAt_comp_left
      (by rw [nativePeriodChart_source]; simp)).2 hcoord.continuousAt
  apply (mdifferentiableAt_iff_target (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ))).2
  refine ⟨hcont, ?_⟩
  change MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
    (nativePeriodChart τ₀ hperiod ∘ f) 0
  exact hcoord.differentiableAt.mdifferentiableAt

/-- The derivative of the literal original marked-family curve sends the
unit complex direction to the native period basis vector in the same fibre. -/
theorem mfderiv_nativePeriodCurve_zero_eq_basis (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀) (τ : ℍ) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun t : ℂ => normalizedFamilyPoint τ₀ (nearbyPeriod τ t)) 0
        ((NormedSpace.fromTangentSpace (0 : ℂ)).symm 1) =
      nativePeriodTangentBasis τ₀ hperiod
        (normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))) 0 := by
  let := nativePeriodChartedSpace τ₀ hperiod
  let : IsManifold 𝓘(ℂ, ℂ) ω
      (TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :=
    nativePeriod_isManifold τ₀ hperiod
  let f : ℂ → TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) :=
    fun t => normalizedFamilyPoint τ₀ (nearbyPeriod τ t)
  let s1 : TangentSpace 𝓘(ℂ, ℂ) (0 : ℂ) :=
    (NormedSpace.fromTangentSpace (0 : ℂ)).symm 1
  have hf : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f 0 :=
    mdifferentiableAt_nativePeriodCurve_zero τ₀ hperiod τ
  have he : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (nativePeriodChart τ₀ hperiod) (f 0) :=
    (mdifferentiable_chart (I := 𝓘(ℂ, ℂ)) (f 0)).mdifferentiableAt
      (mem_chart_source ℂ (f 0))
  have hcoord : HasDerivAt (nativePeriodChart τ₀ hperiod ∘ f) 1 0 :=
    hasDerivAt_nativePeriodChart_nearbyFamily τ₀ hperiod τ
  change mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f 0 s1 =
    nativePeriodTangentBasis τ₀ hperiod (f 0) 0
  apply (nativePeriodTangentCoordinateEquiv τ₀ hperiod (f 0)).injective
  rw [nativePeriodTangentCoordinateEquiv_basis,
    nativePeriodTangentCoordinateEquiv_apply]
  rw [← mfderiv_comp_apply (x := (0 : ℂ)) he hf s1,
    mfderiv_eq_fderiv, hcoord.hasFDerivAt.fderiv]
  simp [s1]

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
