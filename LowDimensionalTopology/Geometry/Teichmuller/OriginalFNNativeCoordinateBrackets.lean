module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNNativeFrame
public import LowDimensionalTopology.Geometry.Teichmuller.SmoothFormInterior
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Commuting coordinate fields of the same original FN map

The literal native coordinate fields are pullbacks of constant model fields.
Public pullback naturality gives their zero Lie brackets, including every
fixed real rescaling of the length and twist coordinate directions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

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
    (hAlt : ∀ m : MarkedRiemannSurface.{0,0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3*g-3) → ℂ
local notation "F" => (Fin (3*g-3) → ℝ) × (Fin (3*g-3) → ℝ)
local notation "RI" => 𝓘(ℝ, E)
local notation "FI" => 𝓘(ℝ, F)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "c" => nativeWeilPeterssonCoordinateChart
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)

variable
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3*g-3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3*g-3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0,0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D₁ : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D₁)
      (j : Fin (3*g-3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m,rfl⟩⟩ j = D₁.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)

local notation "FN" => originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
local notation "K" => FN ∘ OpenPartialHomeomorph.symm c
local notation "Compat" => Unproved.Teichmuller.OriginalFNNativeSmoothInverse
  R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize

local notation "J" => Fin (3*g-3) ⊕ Fin (3*g-3)
local notation "b" => (fun a : J => match a with
  | Sum.inl j => (Pi.single j (1 : ℝ), (0 : Fin (3*g-3) → ℝ))
  | Sum.inr j => ((0 : Fin (3*g-3) → ℝ), Pi.single j (1 : ℝ)))

/-- Every pair of literal native FN coordinate fields commutes, and fixed
real multiples retain this property. -/
theorem sameOriginalFN_native_coordinate_brackets (hCompat : Compat) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (a d : J) (r s : ℝ) (q : T),
      VectorField.mlieBracket RI
        (fun x : T => r • VectorField.mpullback RI FI FN
          (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b a)) x)
        (fun x : T => s • VectorField.mpullback RI FI FN
          (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b d)) x) q = 0 := by
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  have hreg := sameOriginalFN_native_regular_and_isInvertible
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  let B : J → ℝ → ∀ y : F, TangentSpace FI y :=
    fun a r y => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (r • b a)
  have hB (a : J) (r : ℝ) : ContMDiff FI (FI).tangent ∞
      (fun y : F => (⟨y, B a r y⟩ : TangentBundle FI F)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hzero (a d : J) (r s : ℝ) :
      VectorField.mlieBracket FI (B a r) (B d s) = 0 := by
    funext y
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).injective
    rw [Pi.zero_apply, map_zero, ← VectorField.mlieBracketWithin_univ,
      VectorField.mlieBracketWithin_eq_lieBracketWithin]
    change VectorField.lieBracketWithin ℝ
      (fun _ : F => r • b a) (fun _ : F => s • b d) univ y = 0
    rw [VectorField.lieBracketWithin_univ]
    change fderiv ℝ (fun _ : F => s • b d) y (r • b a) -
      fderiv ℝ (fun _ : F => r • b a) y (s • b d) = 0
    simp only [fderiv_const_apply, zero_apply, sub_self]
  have hscale (a : J) (r : ℝ) : VectorField.mpullback RI FI FN (B a r) =
      (fun x : T => r • VectorField.mpullback RI FI FN
        (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b a)) x) := by
    funext x
    simp only [VectorField.mpullback_apply, B, map_smul]
  intro a d r s q
  have h := VectorField.mpullback_mlieBracket
    ((hB a r (FN q)).mdifferentiableAt (by simp))
    ((hB d s (FN q)).mdifferentiableAt (by simp))
    (hreg.1 q) (by simp)
  rw [hzero a d r s, VectorField.mpullback_zero, Pi.zero_apply] at h
  simpa only [hscale] using h.symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
