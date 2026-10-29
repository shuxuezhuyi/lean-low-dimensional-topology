module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNWPAllTimeConstancy
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNAllPointLengthDuality

/-!
# Original FN invariance from the actual same-curve geometry

The genuine all-point physical length-duality producer supplies the exact
signed field used by the actual FN family. Its original coefficient
derivatives vanish and its coefficients are constant for every real time.
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

/-- The actual same-curve geometric input implies both native coefficient
invariance and constancy along the entire physical signed FN family. -/
theorem sameOriginalFN_wpCoefficients_invariant_of_geometric_family
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
    (hCompat : Compat) (left : Fin (3*g-3) → Fin 2)
    (hRebase : Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
      R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left)
    (k : Fin (3*g-3)) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    let Phi : ℝ → T → T := fun t a => sigma a k (left k) t
    let Wk := W hCompat k (left k)
    let h := sameOriginalFN_unitCurve_localFlowData R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)
    (∀ Y Z : FormInterior.SmoothVectorField RI (M := T),
      Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
        R hp hg hgenus hΓ hfree hsmooth hWP ⊤ 1 (by norm_num) Phi Wk Y Z
        h.1 h.2.1 h.2.2.1 h.2.2.2) →
    ∃ frame : J → FormInterior.SmoothVectorField RI (M := T),
      (∀ a q, frame a q = VectorField.mpullback RI FI FN
        (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b a)) q) ∧
      (∀ (a d : J) (r s : ℝ) (q : T),
        mfderiv RI 𝓘(ℝ) (fun x => omegaWP x ![(r • frame a) x,(s • frame d) x])
          q (Wk q) = 0) ∧
      ∀ (a d : J) (r s : ℝ) (q : T) (t : ℝ),
        omegaWP (sigma q k (left k) t)
          ![(r • frame a) (sigma q k (left k) t),(s • frame d) (sigma q k (left k) t)] =
        omegaWP q ![(r • frame a) q,(s • frame d) q] := by
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  intro hCartan
  have hsigned := sameOriginalFN_signed_twist_length_duality
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
    left hCompat hRebase
  have hDual (q : T) (v : TangentSpace RI q) :
      omegaWP q ![W hCompat k (left k) q,v] =
        mfderiv RI 𝓘(ℝ) (lengthOf (D₀.cuff k).toLoop) q v := by
    change omegaWP q ![originalFNUnitSideSign (left k) •
      VectorField.mpullback RI FI FN
        (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b (Sum.inr k))) q,v] = _
    exact hsigned q k v
  rcases (sameOriginalFN_wpCoefficient_twistDerivative_zero
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
      hWP hFrickeBers hvariation hjets hCompat k (left k) hCartan hDual).2 with
    ⟨frame,hframe,hzero⟩
  rcases sameOriginalFN_wpCoefficient_unitCurve_constant
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
      hWP hFrickeBers hvariation hjets hCompat k (left k) hCartan hDual with
    ⟨frame',hframe',hconstant⟩
  have hsame : frame' = frame := by
    funext a
    apply ContMDiffSection.ext
    intro q
    exact (hframe' a q).trans (hframe a q).symm
  rw [hsame] at hconstant
  exact ⟨frame,hframe,hzero,hconstant⟩

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
