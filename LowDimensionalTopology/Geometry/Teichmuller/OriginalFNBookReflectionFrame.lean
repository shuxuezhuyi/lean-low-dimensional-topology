module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookTangentExpansion
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNReflectionCovectors

/-!
# The given original reflection on the actual book FN frame

The existing raw reflection producer supplies its actual inverse-coordinate
frame and derived integer shift. The same book differential identifies its
literal length pullback with that raw length field; the literal book twist
pullback is the fixed signed raw twist. This transports the derived integer
and reflection action without a WP or duality premise. A compatible reflection
is given throughout; existence on an arbitrary surface is not asserted.
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
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc) (J : X ≃ₜ X)
    (hJ : @LiZhongQC.IsAnticonformalInvolution X inferInstance
      R.toRiemannAtlas.toChartedSpace J)
    (hJcuffs : ∀ j, J '' range (D₀.cuff j).curve = range (D₀.cuff j).curve)
    (hJpants : ∀ a, J '' (D₀.component a).val = (D₀.component a).val)

local notation "T" => TeichmullerSpace R
local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "F" => (I → ℝ) × (I → ℝ)
local notation "RI" => 𝓘(ℝ, E)
local notation "FI" => 𝓘(ℝ, F)
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  («I» := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)
local notation "rN" => originalNativeTeichmullerReflection R hg hgenus J hJ

variable
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D₁ : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D₁)
      (j : Fin (3 * g - 3)), φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D₁.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)
    (left : Fin (3 * g - 3) → Fin 2)

local notation "Nraw" => originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
local notation "Nbook" => originalFNBookNativeCoordinateMap R hg hgenus hA hAlt D₀ Θ left
local notation "Compat" => Unproved.Teichmuller.OriginalFNNativeSmoothInverse
  R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
local notation "b" => (fun a : I ⊕ I => match a with
  | Sum.inl j => (Pi.single (M := fun _ => ℝ) j (1 : ℝ), (0 : I → ℝ))
  | Sum.inr j => ((0 : I → ℝ), Pi.single (M := fun _ => ℝ) j (1 : ℝ)))
local notation "L" => (fun (j : I) (q : T) => VectorField.mpullback RI FI Nbook
  (fun y : F => (ContinuousLinearEquiv.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) y)) (b (Sum.inl j))) q)
local notation "V" => (fun (j : I) (q : T) => VectorField.mpullback RI FI Nbook
  (fun y : F => (ContinuousLinearEquiv.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) y)) (b (Sum.inr j))) q)

include left in
/-- The derived raw reflection geometry gives an actual book integer and
reflection law on the literal book length/twist coordinate pullbacks. -/
theorem exists_originalFNBookReflection_native_frame
    (hCompat : Compat)
    (hGeom : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
      R hg hgenus hA hAlt D₀ J hJ hJcuffs hJpants) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∃ n : I → ℤ,
      (∀ (q : T) (j : I), mfderiv RI RI rN q (L j q) =
        L j (rN q) + ((n j : ℝ) / 2) • V j (rN q)) ∧
      ∀ (q : T) (j : I), mfderiv RI RI rN q (V j q) = -V j (rN q) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  obtain ⟨n, frame, hpb, hunit, _hcov, hL, hV⟩ :=
    exists_originalFNReflection_native_covectors_and_frame
      R hp hg hgenus hΓ hsmooth hA hAlt D₀ J hJ hJcuffs hJpants
      hU φ Θ hφ hΘ hRigid hRealize hCompat hGeom
  have hbook := sameOriginalFN_book_tangent_expansion
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat left
  let S := originalFNBookCoordinateSignEquiv left
  have heq := originalFNBookNativeCoordinateMap_eq R hg hgenus hA hAlt D₀ Θ left
  have hraw := sameOriginalFN_native_regular_and_isInvertible
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  have hchain (q : T) : mvfderiv RI Nbook q =
      S.toContinuousLinearMap.comp (mvfderiv RI Nraw q) := by
    rw [heq]
    have hS : MDifferentiableAt FI FI S (Nraw q) :=
      (S.toContinuousLinearMap.contMDiffAt (n := ∞)).mdifferentiableAt (by simp)
    have h := mvfderiv_comp q hS ((hraw.1 q).mdifferentiableAt (by simp))
    rw [mvfderiv_eq_fderiv, S.fderiv] at h
    simpa only [mvfderiv, Function.comp_apply, ContinuousLinearMap.comp_assoc] using h
  have hinjective (q : T) : Function.Injective (mvfderiv RI Nbook q) := by
    intro v w h
    apply (hbook.2.1 q).injective
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook q)).injective h
  have hbookUnit (q : T) (j : I) : mvfderiv RI Nbook q (L j q) = b (Sum.inl j) := by
    change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook q))
      (mfderiv RI FI Nbook q ((mfderiv RI FI Nbook q).inverse
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook q)).symm (b (Sum.inl j))))) = _
    rw [(hbook.2.1 q).self_apply_inverse]
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook q)).apply_symm_apply _
  have hLraw (q : T) (j : I) : L j q = frame (Sum.inl j) q := by
    apply hinjective q
    rw [hbookUnit, hchain, ContinuousLinearMap.comp_apply, hunit]
    apply Prod.ext
    · rfl
    · funext k
      change (0 : ℝ) = originalFNBookSideSign (left k) * 0
      rw [mul_zero]
  have hVraw (q : T) (j : I) : V j q =
      originalFNBookSideSign (left j) • frame (Sum.inr j) q := by
    rw [hpb (Sum.inr j) q]
    exact sameOriginalFN_book_twistVector_eq
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat left j q
  dsimp only at hLraw hVraw
  let nbook : I → ℤ := fun j => if left j = 0 then n j else -n j
  have hnscale (j : I) : ((nbook j : ℝ) / 2) * originalFNBookSideSign (left j) =
      (n j : ℝ) / 2 := by
    by_cases h : left j = 0 <;>
      simp only [nbook, originalFNBookSideSign, h, ite_true, ite_false, Int.cast_neg] <;> ring
  refine ⟨nbook, ?_, ?_⟩
  · intro q j
    rw [hLraw q j, hL q j, hLraw (rN q) j, hVraw (rN q) j, smul_smul, hnscale j]
  · intro q j
    rw [hVraw q j, map_smul, hV q j, hVraw (rN q) j, smul_neg]

end LowDimensionalTopology.Geometry.Teichmuller
