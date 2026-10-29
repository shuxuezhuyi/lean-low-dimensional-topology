module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHorizontalTangentMap
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHorizontalFundamentalIntegral
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonBasePointIntegral

/-!
# The original horizontal integral and the selected native Weil–Petersson form

For the same canonical covering metric, the book-normalized pairing on the
actual horizontal tensor image equals twice the real part of the selected
native form on its original tangent representatives. The literal harmonic
coefficient correspondence reverses the quadratic pairing slots; conjugate
symmetry preserves their real part.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The canonical real action on the original symmetric-tensor submodule. -/
local instance canonicalHorizontalWPTensorSMul :
    SMul ℝ (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact Submodule.smul (symmetricTwoTensorSubmodule R)

variable (M : HyperbolicSurfaceModel R.toRiemannSurface)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (hp : letI := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

include hF in
private theorem harmonicQuadratic_pairing_swapped
    (Q S : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    beltramiPairing F (NativeHarmonicBeltrami.ofQuadratic R M.halfPlaneCover hp Q).val
        (NativeHarmonicBeltrami.ofQuadratic R M.halfPlaneCover hp S).val =
      nativeQuadraticPairing R.toRiemannAtlas M.halfPlaneCover F S Q := by
  rw [beltramiPairing_eq_hyperbolicIntegral F hF.1.measurableSet,
    nativeQuadraticPairing, quadraticPairing_eq_hyperbolicIntegral F hF.1.measurableSet]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
      (NativeHarmonicBeltrami.ofQuadratic_coe_ae R M.halfPlaneCover hp Q),
    ae_restrict_of_ae (NativeHarmonicBeltrami.ofQuadratic_coe_ae R M.halfPlaneCover hp S)]
    with z hQ hS
  rw [hQ, hS]
  exact (mul_comm _ _).trans
    (quadraticPointwiseLift_eq_coefficients R M.halfPlaneCover S Q z).symm

variable (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R
      (discCoverAtlasInducedMetric M).metric)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "C" => TeichmullerSpace.canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "BH" => TeichmullerSpace.baseTangentHarmonicEquiv
  R hg hgenus hΓ hfree hp hsmooth P F hF
local notation "T" => horizontalOriginalTangentEquiv R hg hgenus hΓ hfree hp hsmooth P F hF
local notation "K" => TeichmullerSpace.nativeWeilPeterssonCore
  R hp hg hgenus hΓ hfree hsmooth (TeichmullerSpace.basePoint R)

/-- The same canonical metric's actual horizontal tensor pairing gives the
selected original WP real metric on its genuine coefficient tangent vectors. -/
theorem metricTensorBookL2Pairing_horizontal_nativeWeilPetersson :
    letI := C
    ∀ h k : {t : SmoothSymmetricTwoTensor R // t ∈ horizontalQuadraticTensors R},
      metricTensorBookL2Pairing R (discCoverAtlasInducedMetric M).metric harea h.val k.val =
        2 * ((K).inner (T k) (T h)).re := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := C
  have he (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
      (BH (T ⟨(2 : ℝ) • quadraticDifferentialTensor R Q, ⟨Q, rfl⟩⟩)).val =
        NativeHarmonicBeltrami.ofQuadratic R M.halfPlaneCover hp Q := by
    rw [horizontalOriginalTangentEquiv_apply_quadratic,
      TeichmullerSpace.baseTangentHarmonicEquiv_derivative]
    exact NativePetersson.harmonicProjection_fixes_ofQuadratic R P M.halfPlaneCover hp F hF Q
  have hw (Q S : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
      (K).inner (T ⟨(2 : ℝ) • quadraticDifferentialTensor R S, ⟨S, rfl⟩⟩)
          (T ⟨(2 : ℝ) • quadraticDifferentialTensor R Q, ⟨Q, rfl⟩⟩) =
        nativeQuadraticPairing R.toRiemannAtlas M.halfPlaneCover F S Q := by
    rw [TeichmullerSpace.nativeWeilPeterssonCore_basePoint_integral
      R hp hg hgenus hΓ hfree hsmooth P F hF, he Q, he S]
    exact harmonicQuadratic_pairing_swapped R M hp P F hF Q S
  intro h k
  obtain ⟨Q, hQ⟩ := h.property
  obtain ⟨S, hS⟩ := k.property
  have hh : h = ⟨(2 : ℝ) • quadraticDifferentialTensor R Q, ⟨Q, rfl⟩⟩ :=
    Subtype.ext hQ.symm
  have hk : k = ⟨(2 : ℝ) • quadraticDifferentialTensor R S, ⟨S, rfl⟩⟩ :=
    Subtype.ext hS.symm
  rw [hh, hk, hw]
  have hpair := (metricTensorBookL2Pairing_horizontal_fundamental_integral R M harea hp P hF Q S).2
  simpa only [← nativeQuadraticPairing_conj R.toRiemannAtlas M.halfPlaneCover F Q S,
    Complex.conj_re] using hpair

end LowDimensionalTopology.Geometry.Teichmuller
