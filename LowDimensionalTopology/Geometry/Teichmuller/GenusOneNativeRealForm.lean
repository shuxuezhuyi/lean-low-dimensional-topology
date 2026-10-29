module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneNativeHermitianCore
public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneLengthTwistForm
public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.Tactic.FinCases

/-!
# The original native real period metric and fundamental form

Both data use the actual real period-chart differential on the original
quotient fibres. Their comparison retains the English metric normalization,
the same native Hermitian data and the actual length–twist differentials.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces
variable (τ₀ : ℍ) (hperiod : Unproved.Teichmuller.OriginalGenusOnePeriodCoordinates τ₀)

/-- The real parameter tensor pulled back by the actual original real period differential. -/
def nativePeriodRealTensor (q : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) q →L[ℝ] ℝ := by
  letI := nativePeriodChartedSpace τ₀ hperiod
  let E : ℍ ≃ₜ TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) := Classical.choose hperiod
  letI : IsManifold 𝓘(ℝ, ℂ) ω
      (TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :=
    (nativePeriodChart τ₀ hperiod).isManifold_singleton (nativePeriodChart_source τ₀ hperiod)
  let K := ((mdifferentiable_chart (I := 𝓘(ℝ, ℂ)) q).mfderiv
    (mem_chart_source ℂ q)).trans
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (nativePeriodChart τ₀ hperiod q))
  letI : IsNormableSpace ℝ (TangentSpace 𝓘(ℝ, ℂ) q) := K.isNormableSpace
  exact (parameterTensor (E.symm q)).bilinearComp K.toContinuousLinearMap K.toContinuousLinearMap

/-- The continuous alternating pullback of the actual twist and length differentials. -/
def nativePeriodFundamentalForm (q : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀)) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    TangentSpace 𝓘(ℝ, ℂ) q [⋀^Fin 2]→L[ℝ] ℝ := by
  letI := nativePeriodChartedSpace τ₀ hperiod
  let E : ℍ ≃ₜ TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) := Classical.choose hperiod
  let D := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (nativePeriodChart τ₀ hperiod q)).toContinuousLinearMap.comp
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (nativePeriodChart τ₀ hperiod) q)
  let α := (fderiv ℝ parameterTwist (E.symm q : ℂ)).comp D
  let β := (fderiv ℝ parameterLength (E.symm q : ℂ)).comp D
  let A : TangentSpace 𝓘(ℝ, ℂ) q [⋀^Fin 2]→ₗ[ℝ] ℝ :=
    { MultilinearMap.mk' (fun v => α (v 0) * β (v 1) - α (v 1) * β (v 0))
        (fun v i x y => by fin_cases i <;> simp [add_mul, mul_add] <;> ring)
        (fun v i r x => by fin_cases i <;> simp [smul_eq_mul] <;> ring) with
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        have h01 : v 0 = v 1 := by fin_cases i <;> fin_cases j <;> simp_all
        change α (v 0) * β (v 1) - α (v 1) * β (v 0) = 0
        rw [h01, sub_self] }
  refine { A with cont := ?_ }
  change Continuous (fun v : Fin 2 → TangentSpace 𝓘(ℝ, ℂ) q =>
    α (v 0) * β (v 1) - α (v 1) * β (v 0))
  exact ((α.continuous.comp (continuous_apply 0)).mul
    (β.continuous.comp (continuous_apply 1))).sub
      ((α.continuous.comp (continuous_apply 1)).mul (β.continuous.comp (continuous_apply 0)))

/-- The same actual native real differential gives twice the Hermitian real part,
the English line element, and the positively oriented length–twist form. -/
theorem nativePeriodRealTensor_form_at_period (τ : ℍ) :
    letI := nativePeriodChartedSpace τ₀ hperiod
    let q₀ := normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))
    let dτ : TangentSpace 𝓘(ℝ, ℂ) q₀ → ℂ := fun v =>
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (nativePeriodChart τ₀ hperiod q₀))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (nativePeriodChart τ₀ hperiod) q₀ v)
    ∀ v w : TangentSpace 𝓘(ℝ, ℂ) q₀,
      nativePeriodRealTensor τ₀ hperiod q₀ v w =
        2 * ((nativePeriodHermitianCore τ₀ hperiod q₀).inner
          ((nativePeriodTangentCoordinateEquiv τ₀ hperiod q₀).symm (dτ w))
          ((nativePeriodTangentCoordinateEquiv τ₀ hperiod q₀).symm (dτ v))).re ∧
      nativePeriodRealTensor τ₀ hperiod q₀ v v = ‖dτ v‖ ^ 2 / (2 * τ.im ^ 2) ∧
      nativePeriodFundamentalForm τ₀ hperiod q₀ ![v, w] =
        parameterTensor τ (Complex.I * dτ v) (dτ w) ∧
      nativePeriodFundamentalForm τ₀ hperiod q₀ ![v, w] =
        fderiv ℝ parameterTwist (τ : ℂ) (dτ v) * fderiv ℝ parameterLength (τ : ℂ) (dτ w) -
        fderiv ℝ parameterTwist (τ : ℂ) (dτ w) * fderiv ℝ parameterLength (τ : ℂ) (dτ v) := by
  let := nativePeriodChartedSpace τ₀ hperiod
  let q₀ := normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))
  let E : ℍ ≃ₜ TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) := Classical.choose hperiod
  let D := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (nativePeriodChart τ₀ hperiod q₀)).toContinuousLinearMap.comp
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (nativePeriodChart τ₀ hperiod) q₀)
  have h0 : nearbyPeriod τ (0 : ℂ) = τ := by simp [nearbyPeriod, τ.im_pos]
  have hE : E.symm q₀ = τ := by
    change E.symm (normalizedFamilyPoint τ₀ (nearbyPeriod τ (0 : ℂ))) = τ
    rw [h0, ← (Classical.choose_spec hperiod) τ, E.symm_apply_apply]
  have hg (v w : TangentSpace 𝓘(ℝ, ℂ) q₀) :
      nativePeriodRealTensor τ₀ hperiod q₀ v w = parameterTensor τ (D v) (D w) := by
    change parameterTensor (E.symm q₀) (D v) (D w) = _
    rw [hE]
  have hω (v w : TangentSpace 𝓘(ℝ, ℂ) q₀) :
      nativePeriodFundamentalForm τ₀ hperiod q₀ ![v, w] =
        fderiv ℝ parameterTwist (τ : ℂ) (D v) * fderiv ℝ parameterLength (τ : ℂ) (D w) -
        fderiv ℝ parameterTwist (τ : ℂ) (D w) * fderiv ℝ parameterLength (τ : ℂ) (D v) := by
    change fderiv ℝ parameterTwist (E.symm q₀ : ℂ) (D v) *
        fderiv ℝ parameterLength (E.symm q₀ : ℂ) (D w) -
      fderiv ℝ parameterTwist (E.symm q₀ : ℂ) (D w) *
        fderiv ℝ parameterLength (E.symm q₀ : ℂ) (D v) = _
    rw [hE]
  dsimp only
  intro v w
  refine ⟨?_, ?_, ?_, hω v w⟩
  · rw [hg, nativePeriodHermitianCore_integral, torusAtlasBeltramiPairing_nativePeriodRepresentative]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    simpa only [pairing_eq, D, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using
      parameterTensor_apply τ (D v) (D w)
  · rw [hg]
    exact parameterTensor_self τ (D v)
  · rw [hω]
    exact (parameterTensor_eq_twist_wedge_length τ (D v) (D w)).symm

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
