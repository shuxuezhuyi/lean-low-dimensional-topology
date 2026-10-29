module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNNativeFrame
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNAnalyticRealCoordinates
public import LowDimensionalTopology.Unproved.Teichmuller.NativeFrickeBersRealAnalyticCompatibility
public import LowDimensionalTopology.Geometry.Teichmuller.SmoothFormInterior
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Real analyticity of the same native FN coordinate fields

The existing forward Fricke/Bers compatibility and the proved original FN
analytic map give analyticity of the literal rescaled native map. The public
pullback-vector-field theorem then applies to its actual invertible differential.
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


private def fnRealCoordinateRescale (v : F) : F :=
  (v.1, fun j => v.1 j / (2 * Real.pi) * v.2 j)

private theorem fnRealCoordinateRescale_contDiff :
    ContDiff ℝ ω (fnRealCoordinateRescale (g := g)) := by
  apply contDiff_fst.prodMk
  apply contDiff_pi.mpr
  intro j
  have hfirst : ContDiff ℝ ω (fun v : F => v.1 j) := contDiff_pi.mp contDiff_fst j
  have hsecond : ContDiff ℝ ω (fun v : F => v.2 j) := contDiff_pi.mp contDiff_snd j
  have hscale : ContDiff ℝ ω (fun _ : F => (2 * Real.pi)⁻¹) := contDiff_const
  simpa only [div_eq_mul_inv] using (hfirst.mul hscale).mul hsecond

include hU φ hφ hΘ in
/-- The literal original length/rescaled-angle map is real analytic in the
same native Bers atlas under its existing forward analytic compatibility. -/
theorem sameOriginalFN_native_realAnalytic
    (hFrickeBers : Unproved.Teichmuller.NativeFrickeBersRealAnalyticCompatibility
      R hg hgenus hΓ hfree hp hsmooth hA) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ContMDiff RI FI ω FN := by
  let := C
  let : IsManifold RI ω T := realManifold
  change ContMDiff RI FI ω FN
  let Fraw := originalFNRealCoordinateZeroExtension R hg hgenus hA hAlt D₀ Θ
  have hFraw : AnalyticOnNhd ℝ Fraw (nativeFrickeImage hA) :=
    (originalFNRealCoordinateMap_analytic_and_coordinates R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ).1
  have hFC : ContMDiff RI 𝓘(ℝ, Fin (6*g-6) → ℝ) ω (finiteFrickeCoordinates hA) :=
    hFrickeBers
  have hvalue (q : T) :
      FN q = fnRealCoordinateRescale (Fraw (finiteFrickeCoordinates hA q)) := by
    rw [originalFNNativeRescaledCoordinateMap_eq_original R hg hgenus hA hAlt D₀ Θ q]
    simp only [Fraw, originalFNRealCoordinateZeroExtension,
      dite_eq_left (show finiteFrickeCoordinates hA q ∈ nativeFrickeImage hA from ⟨q, rfl⟩),
      fnRealCoordinateRescale]
    rfl
  intro q
  have hraw : ContMDiffAt RI FI ω (Fraw ∘ finiteFrickeCoordinates hA) q :=
    (hFraw (finiteFrickeCoordinates hA q) ⟨q, rfl⟩).contDiffAt.comp_contMDiffAt (hFC q)
  have hrescaled : ContMDiffAt RI FI ω
      (fnRealCoordinateRescale ∘ Fraw ∘ finiteFrickeCoordinates hA) q :=
    fnRealCoordinateRescale_contDiff.comp_contMDiffAt hraw
  apply hrescaled.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall hvalue

local notation "J" => Fin (3*g-3) ⊕ Fin (3*g-3)
local notation "b" => (fun a : J => match a with
  | Sum.inl j => (Pi.single j (1 : ℝ), (0 : Fin (3*g-3) → ℝ))
  | Sum.inr j => ((0 : Fin (3*g-3) → ℝ), Pi.single j (1 : ℝ)))

/-- The actual same-map pullbacks of every unit FN direction are real-analytic
native vector fields, using only the existing differential invertibility. -/
theorem sameOriginalFN_native_analytic_coordinate_fields
    (hFrickeBers : Unproved.Teichmuller.NativeFrickeBersRealAnalyticCompatibility
      R hg hgenus hΓ hfree hp hsmooth hA) (hCompat : Compat) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ContMDiff RI FI ω FN ∧
      ∀ a : J, ContMDiff RI (RI).tangent ω
        (fun q : T => (⟨q, VectorField.mpullback RI FI FN
          (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b a)) q⟩ :
            TangentBundle RI T)) := by
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  have hFN : ContMDiff RI FI ω FN :=
    sameOriginalFN_native_realAnalytic R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hFrickeBers
  have hreg := sameOriginalFN_native_regular_and_isInvertible
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  refine ⟨hFN, ?_⟩
  intro a
  have hconstant : ContMDiff FI (FI).tangent ω
      (fun y : F => (⟨y, (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b a)⟩ :
        TangentBundle FI F)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  exact hconstant.mpullback_vectorField hFN hreg.2 (by simp)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
