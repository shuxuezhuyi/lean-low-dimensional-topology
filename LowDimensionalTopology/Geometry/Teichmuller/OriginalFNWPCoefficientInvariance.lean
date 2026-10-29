module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNUnitNativeFlow
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNNativeCoordinateBrackets
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalWPCartanLieForm
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalWPTwistCoefficientInvariance
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCoordinateClosedness
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceHarmonicNaturalityProof
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalGeodesicLengthDifferential

/-!
# Original WP coefficient invariance for the actual signed FN family

The actual unit family, coordinate brackets, marked-length regularity and
proved harmonic-reference naturality feed the existing Cartan argument.
Length duality is an explicit internal input for this same signed field.
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

local notation "J" => Fin (3*g-3) ⊕ Fin (3*g-3)
local notation "b" => (fun a : J => match a with
  | Sum.inl j => (Pi.single j (1 : ℝ), (0 : Fin (3*g-3) → ℝ))
  | Sum.inr j => ((0 : Fin (3*g-3) → ℝ), Pi.single j (1 : ℝ)))
local notation "sigma" => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
  hU φ Θ hφ hΘ hRigid hRealize
local notation "W" => sameOriginalFNSignedTwistField R hp hg hgenus hΓ hfree hsmooth
  hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
local notation "omegaWP" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "lengthOf" => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus

/-- The actual signed FN family realizes the field-defined WP Lie form,
using only its explicit Cartan identity and no length-duality input. -/
theorem sameOriginalFN_unitCurve_wpLieDerivative_eq_field
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hCompat : Compat) (k : Fin (3*g-3)) (side : Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    let Φ : ℝ → T → T := fun t a => sigma a k side t
    let Wk := W hCompat k side
    let h := sameOriginalFN_unitCurve_localFlowData R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k side
    Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
      R hp hg hgenus hΓ hfree hsmooth hWP ⊤ 1 (by norm_num) Φ Wk 0 0
      h.1 h.2.1 h.2.2.1 h.2.2.2 →
    ∀ q : T,
      sameOriginalFNUnitWPLieDerivative R hp hg hgenus hΓ hfree hsmooth
        hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k side q =
      nativeWeilPeterssonFormLieDerivative R hp hg hgenus hΓ hfree hsmooth hWP Wk q := by
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  intro hCartan q
  have h := sameOriginalFN_unitCurve_localFlowData R hp hg hgenus hΓ hfree hsmooth
    hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k side
  exact nativeWP_formLieDerivativeAlong_eq_field R hp hg hgenus hΓ hfree hsmooth
    hWP ⊤ 1 (by norm_num) (fun t a => sigma a k side t) (W hCompat k side) 0 0
    h.1 h.2.1 h.2.2.1 h.2.2.2 hCartan q (by trivial)

/-- Exact duality for this actual signed FN field makes every original FN
coordinate coefficient invariant in its actual native twist direction. -/
theorem sameOriginalFN_wpCoefficient_twistDerivative_zero
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hFrickeBers : Unproved.Teichmuller.NativeFrickeBersRealAnalyticCompatibility
      R hg hgenus hΓ hfree hp hsmooth hA)
    (hvariation : ∀ ν : Ball Γ,
      Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
        (deformedNativeSurface R hgenus hΓ hp ν)
        (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hg
        (deformedNativeSurface_hasGenus R hgenus hΓ hp ν)
        (deformedGroup_spec hΓ ν).1
        (deformedNativeSurface_actsFreely R hgenus hΓ hp ν) hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (hCompat : Compat) (k : Fin (3*g-3)) (side : Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    let Φ : ℝ → T → T := fun t a => sigma a k side t
    let Wk := W hCompat k side
    let h := sameOriginalFN_unitCurve_localFlowData R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k side
    (∀ Y Z : FormInterior.SmoothVectorField RI (M := T),
      Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
        R hp hg hgenus hΓ hfree hsmooth hWP ⊤ 1 (by norm_num) Φ Wk Y Z
        h.1 h.2.1 h.2.2.1 h.2.2.2) →
    (∀ (q : T) (v : TangentSpace RI q),
      omegaWP q ![Wk q,v] = mfderiv RI 𝓘(ℝ) (lengthOf (D₀.cuff k).toLoop) q v) →
    (∀ q : T,
      sameOriginalFNUnitWPLieDerivative R hp hg hgenus hΓ hfree hsmooth
        hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k side q =
      nativeWeilPeterssonFormLieDerivative R hp hg hgenus hΓ hfree hsmooth hWP Wk q) ∧
    ∃ frame : J → FormInterior.SmoothVectorField RI (M := T),
      (∀ a q, frame a q = VectorField.mpullback RI FI FN
        (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b a)) q) ∧
      ∀ (a d : J) (r s : ℝ) (q : T),
        mfderiv RI 𝓘(ℝ)
          (fun x => omegaWP x ![(r • frame a) x,(s • frame d) x]) q (Wk q) = 0 := by
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  intro hCartan hDual
  let Φ : ℝ → T → T := fun t a => sigma a k side t
  let Wk := W hCompat k side
  have hFlow := sameOriginalFN_unitCurve_localFlowData R hp hg hgenus hΓ hfree hsmooth
    hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k side
  have hClosed := nativeWeilPeterssonCoordinateForm_closed_of_harmonicVariation
    R hp hg hgenus hΓ hsmooth hfree hWP
    (deformedReferenceHarmonicNaturality R hp hg hgenus hΓ hfree hsmooth) hvariation hjets
  have hLengthOmega := (originalClosedGeodesic_nativeLength_realAnalytic_differential
    R hg hgenus hΓ hfree hp hsmooth hA hAlt hFrickeBers (D₀.cuff k)).1
  have hLength : ContMDiff RI 𝓘(ℝ) ∞ (lengthOf (D₀.cuff k).toLoop) :=
    hLengthOmega.of_le (by simp)
  have hDualAt (q : T) : Unproved.Teichmuller.WolpertLengthDualityAt
      R hp hg hgenus hΓ hfree hsmooth q (D₀.cuff k).toLoop (Wk q) := hDual q
  rcases exists_same_originalFN_native_coordinate_frame R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat with
    ⟨hFN, hInvertible, frame, hframe, hinverse, hunit⟩
  have hBracket (a : J) (r : ℝ) (q : T) :
      VectorField.mlieBracket RI Wk (r • frame a) q = 0 := by
    change VectorField.mlieBracket RI
      (fun x : T => originalFNUnitSideSign side • VectorField.mpullback RI FI FN
        (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b (Sum.inr k))) x)
      (fun x : T => r • frame a x) q = 0
    have hscaled : (fun x : T => r • frame a x) =
        (fun x : T => r • VectorField.mpullback RI FI FN
          (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b a)) x) :=
      funext fun x => congrArg (fun v : TangentSpace RI x => r • v) (hframe a x)
    have h := sameOriginalFN_native_coordinate_brackets R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
      (Sum.inr k) a (originalFNUnitSideSign side) r q
    exact (congrArg (fun V : (x : T) → TangentSpace RI x =>
      VectorField.mlieBracket RI Wk V q) hscaled).trans h
  refine ⟨?_, frame, hframe, ?_⟩
  · intro q
    exact sameOriginalFN_unitCurve_wpLieDerivative_eq_field
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
      hWP hCompat k side (hCartan 0 0) q
  · intro a d r s q
    exact nativeWP_coefficient_twistDerivative_zero_of_lengthDuality
      R hp hg hgenus hΓ hfree hsmooth hWP (D₀.cuff k).toLoop ⊤ 1 (by norm_num) Φ
      Wk (r • frame a) (s • frame d) hFlow.1 hFlow.2.1 hFlow.2.2.1 hFlow.2.2.2
      (hCartan (r • frame a) (s • frame d)) hLength.contMDiffOn
      (fun x _ => hDualAt x) hClosed
      (fun x _ => hBracket a r x) (fun x _ => hBracket d s x) q (by trivial)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
