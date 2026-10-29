module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNNativeCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalNativeReflectionAntiSymplectic
public import LowDimensionalTopology.Geometry.Teichmuller.ComplexTopologicalProperties
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The global integer reflection shift of every actual full real FN branch

The lower squared geometric circle-phase law gives a continuous real function
with constant circle exponential. Existing covering uniqueness makes it
constant; the actual base point then supplies one integer per original cuff.
No integer shift, derivative, frame action or branch normalization is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation GeneralQC TeichmullerSpace GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : LiZhongQC.IsFuchsian Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0,0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc) (J : X ≃ₜ X)
    (hJ : @LiZhongQC.IsAnticonformalInvolution X inferInstance
      R.toRiemannAtlas.toChartedSpace J)
    (hJcuffs : ∀ j, J '' range (D₀.cuff j).curve = range (D₀.cuff j).curve)
    (hJpants : ∀ a, J '' (D₀.component a).val = (D₀.component a).val)

local notation "T" => TeichmullerSpace R
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "rN" => originalNativeTeichmullerReflection R hg hgenus J hJ

include hp hΓ hsmooth in
/-- The actual lower geometric phase law gives one global integer shift for
every admissible original continuous full real branch. -/
theorem originalFNReflection_real_value_law
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0,0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hGeom : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
      R hg hgenus hA hAlt D₀ J hJ hJcuffs hJpants) :
    letI := C
    let FN := originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
    ∃ n : Fin (3 * g - 3) → ℤ, ∀ q : T,
      (FN (rN q)).1 = (FN q).1 ∧
      ∀ j, (FN (rN q)).2 j = -(FN q).2 j + (n j : ℝ) / 2 * (FN q).1 j := by
  classical
  let := C
  let : PathConnectedSpace T := canonical_pathConnected_of_smoothing
    R hg hgenus hP hΓ hfree hp hsmooth
  let t : T → nativeFrickeImage hA := fun q =>
    ⟨finiteFrickeCoordinates hA q, ⟨q, rfl⟩⟩
  let θ : T → Fin (3 * g - 3) → ℝ := fun q => Θ (t q)
  let FN := originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
  let A : OriginalFNGeometricFamily hA D₀ := Classical.choose hU
  have hrep := (Classical.choose_spec hU).1
  have hchoices := (Classical.choose_spec hU).2.1
  have hφA (q : T) (j : Fin (3 * g - 3)) :
      φ (t q) j = originalFNFamilyPhase hA hAlt D₀ A (t q) j := by
    refine Quotient.inductionOn q ?_
    intro m
    exact (hφ m (chosenCanonicalModel hA m).model (A m).1 (A m).2 j).trans
      (originalFNFamilyPhase_coordinates hA hAlt D₀ A hrep m j).symm
  have hexp (q : T) (j : Fin (3 * g - 3)) :
      Circle.exp (θ q j) = originalFNFamilyPhase hA hAlt D₀ A (t q) j :=
    (congrFun (hΘ j) (t q)).trans (hφA q j)
  have hc : Continuous (finiteFrickeCoordinates hA) := by
    change @Continuous T _ (beltramiTopology R) _ (finiteFrickeCoordinates hA)
    rw [beltramiTopology_eq_fromQC_of_smoothing R hg hgenus hP hsmooth]
    exact nativeFrickeCoordinateContinuity R hg hgenus e hA
  have ht : Continuous t := hc.subtype_mk (fun q => mem_range_self q)
  have hθ : Continuous θ := Θ.continuous.comp ht
  have hr : Continuous rN :=
    (originalNativeTeichmullerReflection_real_mdifferentiable
      R hp hg hgenus hΓ hsmooth J hJ).continuous
  have hdouble (x : ℝ) : Circle.exp (2 * x) = (Circle.exp x) ^ 2 := by
    rw [two_mul, Circle.exp_add, pow_two]
  have hshift (j : Fin (3 * g - 3)) :
      ∃ n : ℤ, ∀ q : T, θ (rN q) j + θ q j = (n : ℝ) * Real.pi := by
    let U : T → ℝ := fun q => 2 * (θ (rN q) j + θ q j)
    have hUc : Continuous U := continuous_const.mul
      (((continuous_apply j).comp (hθ.comp hr)).add ((continuous_apply j).comp hθ))
    have hUexp (q : T) : Circle.exp (U q) = 1 := by
      change Circle.exp (2 * (θ (rN q) j + θ q j)) = 1
      rw [mul_add, Circle.exp_add, hdouble, hdouble, hexp, hexp,
        (hGeom A hrep hchoices q j).2, inv_mul_cancel]
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp (hUexp (TeichmullerSpace.basePoint R))
    refine ⟨n, fun q => ?_⟩
    have hconst := Circle.isCoveringMap_exp.const_of_comp hUc
      (fun a b => (hUexp a).trans (hUexp b).symm) q (TeichmullerSpace.basePoint R)
    have h := hconst.trans hn
    change 2 * (θ (rN q) j + θ q j) = (n : ℝ) * (2 * Real.pi) at h
    linarith only [h]
  let n : Fin (3 * g - 3) → ℤ := fun j => Classical.choose (hshift j)
  have hn (j : Fin (3 * g - 3)) (q : T) :
      θ (rN q) j + θ q j = (n j : ℝ) * Real.pi :=
    Classical.choose_spec (hshift j) q
  have hlength (q : T) (j : Fin (3 * g - 3)) : (FN (rN q)).1 j = (FN q).1 j :=
    (hGeom A hrep hchoices q j).1
  have htwist (q : T) (j : Fin (3 * g - 3)) :
      (FN q).2 j = (FN q).1 j / (2 * Real.pi) * θ q j := by
    have h := congrArg (fun z : (Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ) => z.1 j)
      (originalFNNativeRescaledCoordinateMap_eq_original R hg hgenus hA hAlt D₀ Θ q)
    change (((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ (t q)).1 j : ℝ) /
      (2 * Real.pi)) * θ q j = (FN q).1 j / (2 * Real.pi) * θ q j
    exact congrArg (fun x : ℝ => x / (2 * Real.pi) * θ q j) h.symm
  refine ⟨n, fun q => ⟨funext (hlength q), fun j => ?_⟩⟩
  rw [htwist, htwist, hlength]
  have hangle : θ (rN q) j = (n j : ℝ) * Real.pi - θ q j := by
    linarith only [hn j q]
  rw [hangle]
  field_simp [Real.pi_ne_zero]
  ring

end LowDimensionalTopology.Geometry.Teichmuller
