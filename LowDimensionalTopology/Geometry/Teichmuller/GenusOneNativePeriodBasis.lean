module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneNativePeriodChart
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The original marked-torus period tangent basis

The singleton atlas uses the actual period chart and the existing quotient
topology. Its actual differential carries the native tangent basis to one.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces

/-- The period atlas on the existing original marked-torus quotient. -/
@[instance_reducible] def nativePeriodChartedSpace (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀) :
    ChartedSpace ℂ (TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :=
  (nativePeriodChart τ₀ hperiod).singletonChartedSpace
    (nativePeriodChart_source τ₀ hperiod)

/-- The original quotient is a complex manifold in its period atlas. -/
theorem nativePeriod_isManifold (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    IsManifold 𝓘(ℂ, ℂ) ω
      (TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :=
  (nativePeriodChart τ₀ hperiod).isManifold_singleton
    (nativePeriodChart_source τ₀ hperiod)

/-- The actual period-chart differential identifies each native tangent fibre
with the target complex line. -/
def nativePeriodTangentCoordinateEquiv (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀)
    (q : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    TangentSpace 𝓘(ℂ, ℂ) q ≃L[ℂ] ℂ := by
  letI := nativePeriodChartedSpace τ₀ hperiod
  letI : IsManifold 𝓘(ℂ, ℂ) ω
      (TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :=
    nativePeriod_isManifold τ₀ hperiod
  exact ((mdifferentiable_chart (I := 𝓘(ℂ, ℂ)) q).mfderiv
    (mem_chart_source ℂ q)).trans
      (NormedSpace.fromTangentSpace (nativePeriodChart τ₀ hperiod q))

/-- The coordinate equivalence is precisely the original chart differential. -/
theorem nativePeriodTangentCoordinateEquiv_apply (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀)
    (q : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    ∀ v : TangentSpace 𝓘(ℂ, ℂ) q,
      nativePeriodTangentCoordinateEquiv τ₀ hperiod q v =
        (NormedSpace.fromTangentSpace (nativePeriodChart τ₀ hperiod q))
          (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (nativePeriodChart τ₀ hperiod) q v) := by
  let := nativePeriodChartedSpace τ₀ hperiod
  intro v
  rfl

/-- The native coordinate basis is the inverse actual period differential
applied to the singleton basis of the complex line. -/
def nativePeriodTangentBasis (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀)
    (q : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    Module.Basis (Fin 1) ℂ (TangentSpace 𝓘(ℂ, ℂ) q) := by
  letI := nativePeriodChartedSpace τ₀ hperiod
  exact (Module.Basis.singleton (Fin 1) ℂ).map
    (nativePeriodTangentCoordinateEquiv τ₀ hperiod q).symm.toLinearEquiv

/-- The actual differential sends the native period basis vector to one. -/
theorem nativePeriodTangentCoordinateEquiv_basis (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀)
    (q : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    nativePeriodTangentCoordinateEquiv τ₀ hperiod q
      (nativePeriodTangentBasis τ₀ hperiod q 0) = 1 := by
  let := nativePeriodChartedSpace τ₀ hperiod
  simp [nativePeriodTangentBasis]

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
