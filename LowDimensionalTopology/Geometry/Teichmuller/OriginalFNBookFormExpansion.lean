module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookTangentExpansion
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSmoothForm
public import Mathlib.Tactic.FinCases

/-!
# Finite block expansion of the actual native WP form in the book FN basis

The form is the existing English-normalized native real WP form. The vectors
are the literal book-coordinate pullbacks, and coefficients are their actual
native coordinate differentials. Only the already proved tangent expansion
and the actual form's two real linearities are used. No LL, TL, TT, duality,
reflection, invariance, or final Darboux formula is a premise.
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
local notation "omega" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth

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
    (left : Fin (3 * g - 3) → Fin 2)

local notation "Nbook" => originalFNBookNativeCoordinateMap R hg hgenus hA hAlt D₀ Θ left
local notation "Compat" => Unproved.Teichmuller.OriginalFNNativeSmoothInverse
  R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
local notation "L" => (fun (j : Fin (3 * g - 3)) (a : T) =>
  VectorField.mpullback RI FI Nbook (fun y : F =>
    (ContinuousLinearEquiv.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) y))
      (Pi.single (M := fun _ => ℝ) j (1 : ℝ), (0 : Fin (3 * g - 3) → ℝ))) a)
local notation "V" => (fun (j : Fin (3 * g - 3)) (a : T) =>
  VectorField.mpullback RI FI Nbook (fun y : F =>
    (ContinuousLinearEquiv.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) y))
      ((0 : Fin (3 * g - 3) → ℝ), Pi.single (M := fun _ => ℝ) j (1 : ℝ))) a)

/-- The actual form on arbitrary tangents is its finite four-block expansion
on the literal book FN pullbacks, with actual DN coefficients. -/
theorem sameOriginalFN_book_form_block_expansion (hCompat : Compat) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (a : T) (v w : TangentSpace RI a),
      omega a ![v, w] =
        (∑ j, (mvfderiv RI Nbook a v).1 j *
          ((∑ k, (mvfderiv RI Nbook a w).1 k * omega a ![L j a, L k a]) +
            ∑ k, (mvfderiv RI Nbook a w).2 k * omega a ![L j a, V k a])) +
        ∑ j, (mvfderiv RI Nbook a v).2 j *
          ((∑ k, (mvfderiv RI Nbook a w).1 k * omega a ![V j a, L k a]) +
            ∑ k, (mvfderiv RI Nbook a w).2 k * omega a ![V j a, V k a]) := by
  classical
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  intro a v w
  let A := omega a
  let DN := mvfderiv RI Nbook a
  have hdecomp := (sameOriginalFN_book_tangent_expansion
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat left).2.2 a
  let leftLinear (y : TangentSpace RI a) : TangentSpace RI a →ₗ[ℝ] ℝ :=
    A.toAlternatingMap.toMultilinearMap.toLinearMap ![0, y] 0
  let rightLinear (x : TangentSpace RI a) : TangentSpace RI a →ₗ[ℝ] ℝ :=
    A.toAlternatingMap.toMultilinearMap.toLinearMap ![x, 0] 1
  have hleftValue (x y : TangentSpace RI a) : leftLinear y x = A ![x, y] := by
    change A (Function.update ![0, y] 0 x) = A ![x, y]
    exact congrArg A (by funext i; fin_cases i <;> rfl)
  have hrightValue (x y : TangentSpace RI a) : rightLinear x y = A ![x, y] := by
    change A (Function.update ![x, 0] 1 y) = A ![x, y]
    exact congrArg A (by funext i; fin_cases i <;> rfl)
  have hleft (x y : TangentSpace RI a) : A ![x, y] =
      (∑ j, (DN x).1 j * A ![L j a, y]) + ∑ j, (DN x).2 j * A ![V j a, y] := by
    calc
      A ![x, y] = leftLinear y x := (hleftValue x y).symm
      _ = leftLinear y ((∑ j, (DN x).1 j • L j a) +
          ∑ j, (DN x).2 j • V j a) := congrArg (leftLinear y) (hdecomp x)
      _ = _ := by
        simp only [map_add, map_sum, map_smul]
        simp only [hleftValue, smul_eq_mul]
  have hright (x y : TangentSpace RI a) : A ![x, y] =
      (∑ k, (DN y).1 k * A ![x, L k a]) + ∑ k, (DN y).2 k * A ![x, V k a] := by
    calc
      A ![x, y] = rightLinear x y := (hrightValue x y).symm
      _ = rightLinear x ((∑ k, (DN y).1 k • L k a) +
          ∑ k, (DN y).2 k • V k a) := congrArg (rightLinear x) (hdecomp y)
      _ = _ := by
        simp only [map_add, map_sum, map_smul]
        simp only [hrightValue, smul_eq_mul]
  calc
    A ![v, w] = (∑ j, (DN v).1 j * A ![L j a, w]) +
        ∑ j, (DN v).2 j * A ![V j a, w] := hleft v w
    _ = _ := by
      apply congrArg₂ (fun x y : ℝ => x + y)
      · apply Finset.sum_congr rfl
        intro j _hj
        exact congrArg (fun r : ℝ => (DN v).1 j * r) (hright (L j a) w)
      · apply Finset.sum_congr rfl
        intro j _hj
        exact congrArg (fun r : ℝ => (DN v).2 j * r) (hright (V j a) w)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
