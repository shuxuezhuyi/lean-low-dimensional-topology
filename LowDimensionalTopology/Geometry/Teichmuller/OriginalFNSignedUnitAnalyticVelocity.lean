module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNNativeAnalyticFields
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNUnitNativeTwist

/-!
# The real-analytic signed field of the same original FN unit curve

The original analytic coordinate field retains its fixed side scalar. Its
value is exactly the native velocity already proved for the actual unit
curve. No WP or Cartan input enters this field construction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami NormalizedCoefficientTransport

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

local notation "unitTwist" => (fun j : Fin (3*g-3) =>
  ((0 : Fin (3*g-3) → ℝ), Pi.single (M := fun _ => ℝ) j (1 : ℝ)))
local notation "sigma" => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
  hU φ Θ hφ hΘ hRigid hRealize

/-- The same signed unit curve has its exact real-analytic native field,
with the original affine coordinate line and native velocity at every point. -/
theorem sameOriginalFN_signed_unit_field_realAnalytic_and_velocity
    (hFrickeBers : Unproved.Teichmuller.NativeFrickeBersRealAnalyticCompatibility
      R hg hgenus hΓ hfree hp hsmooth hA) (hCompat : Compat)
    (j : Fin (3*g-3)) (side : Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ContMDiff RI (RI).tangent ω
      (fun q : T => (⟨q, originalFNUnitSideSign side • VectorField.mpullback RI FI FN
        (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)) q⟩ :
          TangentBundle RI T)) ∧
    ∀ a : T,
      sigma a j side 0 = a ∧
      (∀ t : ℝ, FN (sigma a j side t) =
        FN a + (originalFNUnitSideSign side * t) • unitTwist j) ∧
      ContMDiffAt 𝓘(ℝ) RI ∞ (sigma a j side) 0 ∧
      HasDerivAt (fun t : ℝ => c (sigma a j side t))
        (D a (originalFNUnitSideSign side • VectorField.mpullback RI FI FN
          (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)) a)) 0 := by
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  have hraw := (sameOriginalFN_native_analytic_coordinate_fields
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
    hFrickeBers hCompat).2 (Sum.inr j)
  refine ⟨?_, ?_⟩
  · exact hraw.const_smul_section (a := originalFNUnitSideSign side)
  · intro a
    exact sameOriginalFN_unitCurve_native_twistDerivative
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat a j side

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
