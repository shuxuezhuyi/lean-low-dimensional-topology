module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneNativePeriodCurve
public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneNativeRelativeTensor
public import LowDimensionalTopology.Geometry.Teichmuller.GenusOnePeriodBeltramiPairing

/-!
# Native period directions and the original marked-family tensor derivative

The actual period-chart differential gives the scalar direction. Its tensor
representative is tied below to the derivative of the same fixed-reference
marked family's relative tensors, and then to the original torus integral.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces

/-- The actual coordinate differential, valued in the original source-atlas
tensor space using the same marked-family infinitesimal tensor. -/
def nativePeriodBeltramiRepresentative (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀) (τ : ℍ) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    TangentSpace 𝓘(ℂ, ℂ)
        (normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))) →L[ℂ]
      BeltramiDifferential.BanachSpace
        (normalizedTorusModel τ).surface.toRiemannAtlas := by
  letI := nativePeriodChartedSpace τ₀ hperiod
  exact (nativePeriodTangentCoordinateEquiv τ₀ hperiod
    (normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ)))).toContinuousLinearMap.smulRight
      (periodTangentBeltrami τ)

/-- The relative tensor curve and the literal original quotient curve have
the stated native representative relation between their actual derivatives. -/
theorem hasDerivAt_nativeRelativePeriodCurve_nativeDerivative (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀) (τ : ℍ) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    HasDerivAt (nativeRelativePeriodBeltramiCurve τ₀ τ)
      (nativePeriodBeltramiRepresentative τ₀ hperiod τ
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun t : ℂ => normalizedFamilyPoint τ₀ (nearbyPeriod τ t)) 0
          ((NormedSpace.fromTangentSpace (0 : ℂ)).symm 1))) 0 := by
  let := nativePeriodChartedSpace τ₀ hperiod
  let q₀ := normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))
  have hrep : nativePeriodBeltramiRepresentative τ₀ hperiod τ
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun t : ℂ => normalizedFamilyPoint τ₀ (nearbyPeriod τ t)) 0
        ((NormedSpace.fromTangentSpace (0 : ℂ)).symm 1)) = periodTangentBeltrami τ := by
    rw [mfderiv_nativePeriodCurve_zero_eq_basis]
    change (nativePeriodTangentCoordinateEquiv τ₀ hperiod q₀
      (nativePeriodTangentBasis τ₀ hperiod q₀ 0)) • periodTangentBeltrami τ = _
    rw [nativePeriodTangentCoordinateEquiv_basis, one_smul]
  rw [hrep]
  exact hasDerivAt_nativeRelativePeriodBeltramiCurve_zero τ₀ τ

/-- The literal original torus integral of the actual native representatives
has the period-coordinate Hermitian coefficient. -/
theorem torusAtlasBeltramiPairing_nativePeriodRepresentative (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀) (τ : ℍ) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    ∀ v w : TangentSpace 𝓘(ℂ, ℂ)
        (normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))),
      torusAtlasBeltramiPairing τ
        (BeltramiDifferential.toTensor
          (nativePeriodBeltramiRepresentative τ₀ hperiod τ v))
        (BeltramiDifferential.toTensor
          (nativePeriodBeltramiRepresentative τ₀ hperiod τ w)) =
        ((1 / (4 * τ.im ^ 2) : ℝ) : ℂ) *
          nativePeriodTangentCoordinateEquiv τ₀ hperiod
            (normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))) v *
          conj (nativePeriodTangentCoordinateEquiv τ₀ hperiod
            (normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))) w) := by
  let := nativePeriodChartedSpace τ₀ hperiod
  intro v w
  exact torusAtlasBeltramiPairing_periodTangentBeltrami τ
    (nativePeriodTangentCoordinateEquiv τ₀ hperiod
      (normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))) v)
    (nativePeriodTangentCoordinateEquiv τ₀ hperiod
      (normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))) w)

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
