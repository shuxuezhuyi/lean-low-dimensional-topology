module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneNativeRepresentative
public import LowDimensionalTopology.Geometry.Teichmuller.HarmonicPeterssonCore
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Hermitian data on the original marked-torus period tangent fibres

The same chosen period homeomorphism fixes the period at every original quotient
point. The actual chart differential defines positive Hermitian data, with its
full original torus integral and native basis coefficient proved below.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces

/-- Positive Hermitian data on every actual original native tangent fibre. -/
@[instance_reducible]
def nativePeriodHermitianCore (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀)
    (q : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    InnerProductSpace.Core ℂ (TangentSpace 𝓘(ℂ, ℂ) q) := by
  letI := nativePeriodChartedSpace τ₀ hperiod
  let E : ℍ ≃ₜ TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) := Classical.choose hperiod
  let σ := E.symm q
  have ha : tangentBeltrami σ ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr one_ne_zero) (periodGap_ne_zero σ)
  exact NativePetersson.pullbackHermitianCore (InnerProductSpace.toCore (𝕜 := ℂ) (E := ℂ))
    ((nativePeriodTangentCoordinateEquiv τ₀ hperiod q).trans
      (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (tangentBeltrami σ) ha)))

/-- Reversing the Core slots gives the full original native representative integral. -/
theorem nativePeriodHermitianCore_integral (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀) (τ : ℍ) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    ∀ v w : TangentSpace 𝓘(ℂ, ℂ)
        (normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))),
      (nativePeriodHermitianCore τ₀ hperiod
        (normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ)))).inner w v =
      torusAtlasBeltramiPairing τ
        (BeltramiDifferential.toTensor (nativePeriodBeltramiRepresentative τ₀ hperiod τ v))
        (BeltramiDifferential.toTensor (nativePeriodBeltramiRepresentative τ₀ hperiod τ w)) := by
  let := nativePeriodChartedSpace τ₀ hperiod
  intro v w
  let E : ℍ ≃ₜ TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) := Classical.choose hperiod
  let q₀ := normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))
  have h0 : nearbyPeriod τ (0 : ℂ) = τ := by simp [nearbyPeriod, τ.im_pos]
  have hE : E.symm q₀ = τ := by
    change E.symm (normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))) = τ
    rw [h0, ← (Classical.choose_spec hperiod) τ, E.symm_apply_apply]
  rw [torusAtlasBeltramiPairing_nativePeriodRepresentative]
  change inner ℂ
    (nativePeriodTangentCoordinateEquiv τ₀ hperiod q₀ w * tangentBeltrami (E.symm q₀))
    (nativePeriodTangentCoordinateEquiv τ₀ hperiod q₀ v * tangentBeltrami (E.symm q₀)) = _
  rw [RCLike.inner_apply, hE, map_mul]
  calc
    _ = (tangentBeltrami τ * conj (tangentBeltrami τ)) *
        nativePeriodTangentCoordinateEquiv τ₀ hperiod q₀ v *
        conj (nativePeriodTangentCoordinateEquiv τ₀ hperiod q₀ w) := by ring
    _ = _ := by rw [tangentBeltrami_mul_conj]

/-- The native period basis has the original Hermitian coefficient. -/
theorem nativePeriodHermitianCore_basis (τ₀ : ℍ)
    (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀) (τ : ℍ) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    let q₀ := normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))
    (nativePeriodHermitianCore τ₀ hperiod q₀).inner
      (nativePeriodTangentBasis τ₀ hperiod q₀ 0)
      (nativePeriodTangentBasis τ₀ hperiod q₀ 0) = ((1 / (4 * τ.im ^ 2) : ℝ) : ℂ) := by
  let := nativePeriodChartedSpace τ₀ hperiod
  let q₀ := normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))
  change (nativePeriodHermitianCore τ₀ hperiod q₀).inner
    (nativePeriodTangentBasis τ₀ hperiod q₀ 0)
    (nativePeriodTangentBasis τ₀ hperiod q₀ 0) = _
  rw [nativePeriodHermitianCore_integral, torusAtlasBeltramiPairing_nativePeriodRepresentative,
    nativePeriodTangentCoordinateEquiv_basis]
  simp only [map_one, mul_one]

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
