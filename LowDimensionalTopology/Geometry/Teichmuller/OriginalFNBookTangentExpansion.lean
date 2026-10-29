module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookUnitCurve
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Finite tangent expansion in the actual original book FN basis

The coordinates and every basis field are the literal existing native maps
and public pullbacks. The same original local-inverse input yields the book
differential inverse after the fixed sign correction. Finite product sums
then reconstruct each actual tangent vector. No WP block or Darboux identity
is a premise.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3 * g - 3) → ℂ
local notation "F" => (Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ)
local notation "RI" => 𝓘(ℝ, E)
local notation "FI" => 𝓘(ℝ, F)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)

variable
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D₁ : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D₁)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D₁.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)

local notation "Nraw" => originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
local notation "Nbook" => originalFNBookNativeCoordinateMap R hg hgenus hA hAlt D₀ Θ
local notation "Compat" => Unproved.Teichmuller.OriginalFNNativeSmoothInverse
  R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
local notation "unitLength" => (fun j : Fin (3 * g - 3) =>
  (Pi.single (M := fun _ => ℝ) j (1 : ℝ), (0 : Fin (3 * g - 3) → ℝ)))
local notation "unitTwist" => (fun j : Fin (3 * g - 3) =>
  ((0 : Fin (3 * g - 3) → ℝ), Pi.single (M := fun _ => ℝ) j (1 : ℝ)))

/-- The actual book native differential is invertible, and its actual length
and twist pullbacks reconstruct every tangent with the literal DN coefficients. -/
theorem sameOriginalFN_book_tangent_expansion (hCompat : Compat)
    (left : Fin (3 * g - 3) → Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ContMDiff RI FI ∞ (Nbook left) ∧
      (∀ a : T, (mfderiv RI FI (Nbook left) a).IsInvertible) ∧
      ∀ (a : T) (v : TangentSpace RI a),
        v = (∑ j, (mvfderiv RI (Nbook left) a v).1 j •
          VectorField.mpullback RI FI (Nbook left)
            (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitLength j)) a) +
          ∑ j, (mvfderiv RI (Nbook left) a v).2 j •
            VectorField.mpullback RI FI (Nbook left)
              (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)) a := by
  classical
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  let S := originalFNBookCoordinateSignEquiv left
  have heq := originalFNBookNativeCoordinateMap_eq R hg hgenus hA hAlt D₀ Θ left
  have hreg := sameOriginalFN_native_regular_and_isInvertible
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  have hBookSmooth : ContMDiff RI FI ∞ (Nbook left) := by
    rw [heq]
    exact S.toContinuousLinearMap.contMDiff.comp hreg.1
  have hchain (a : T) : mvfderiv RI (Nbook left) a =
      S.toContinuousLinearMap.comp (mvfderiv RI Nraw a) := by
    rw [heq]
    have hS : MDifferentiableAt FI FI S (Nraw a) :=
      (S.toContinuousLinearMap.contMDiffAt (n := ∞)).mdifferentiableAt (by simp)
    have h := mvfderiv_comp a hS ((hreg.1 a).mdifferentiableAt (by simp))
    rw [mvfderiv_eq_fderiv, S.fderiv] at h
    simpa only [mvfderiv, Function.comp_apply, ContinuousLinearMap.comp_assoc] using h
  have hDInv (a : T) : (mvfderiv RI (Nbook left) a).IsInvertible := by
    have hrawInv : (mvfderiv RI Nraw a).IsInvertible := by
      simpa only [mvfderiv, ContinuousLinearMap.isInvertible_equiv_comp] using hreg.2 a
    rw [hchain]
    simpa only [ContinuousLinearMap.isInvertible_equiv_comp] using hrawInv
  have hMfInv (a : T) : (mfderiv RI FI (Nbook left) a).IsInvertible := by
    simpa only [mvfderiv, ContinuousLinearMap.isInvertible_equiv_comp] using hDInv a
  refine ⟨hBookSmooth, hMfInv, ?_⟩
  intro a v
  let DN := mvfderiv RI (Nbook left) a
  have hPB (y : F) : VectorField.mpullback RI FI (Nbook left)
      (fun z : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm y) a = DN.inverse y := by
    change (mfderiv RI FI (Nbook left) a).inverse
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook left a)).symm y) =
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook left a)).toContinuousLinearMap.comp
        (mfderiv RI FI (Nbook left) a)).inverse y
    rw [ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.comp_apply]
    simp only [ContinuousLinearEquiv.coe_coe]
  have hsum (x : F) : x =
      (∑ j, x.1 j • unitLength j) + ∑ j, x.2 j • unitTwist j := by
    apply Prod.ext
    · simpa only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero,
        Finset.sum_const_zero, add_zero] using pi_eq_sum_univ' x.1
    · simpa only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero,
        Finset.sum_const_zero, zero_add] using pi_eq_sum_univ' x.2
  calc
    v = DN.inverse (DN v) := ((hDInv a).inverse_apply_self v).symm
    _ = DN.inverse ((∑ j, (DN v).1 j • unitLength j) +
        ∑ j, (DN v).2 j • unitTwist j) := congrArg DN.inverse (hsum (DN v))
    _ = _ := by
      simp only [map_add, map_sum, map_smul]
      simp only [← hPB]
      rfl

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
