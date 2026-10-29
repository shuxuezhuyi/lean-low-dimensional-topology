module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNReflectionRealBranch
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNNativeFrame
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# The actual original FN reflection covectors and inverse coordinate frame

Differentiating the derived full real branch law gives the length and twist
covector identities. The invertible differential of the same original FN map
then gives the action on its actual pullbacks of constant coordinate fields.
No integer shift, differential identity, frame action or WP premise is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation GeneralQC TeichmullerSpace GammaMeasurableBeltrami

private def originalFNReflectionCoordinateOperator (g : ℕ) (n : Fin (3 * g - 3) → ℤ) :
    ((Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ)) →L[ℝ]
      ((Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ)) :=
  let V := Fin (3 * g - 3) → ℝ
  let A : V →L[ℝ] V := ContinuousLinearMap.pi fun j =>
    ((n j : ℝ) / 2) • (ContinuousLinearMap.proj j : V →L[ℝ] ℝ)
  let P := ContinuousLinearMap.fst ℝ V V
  let Q := ContinuousLinearMap.snd ℝ V V
  P.prod (-Q + A.comp P)

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
    (hφ : ∀ (m : MarkedRiemannSurface.{0,0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D₁ : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D₁)
      (j : Fin (3 * g - 3)), φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D₁.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)

local notation "FN" => originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
local notation "Compat" => Unproved.Teichmuller.OriginalFNNativeSmoothInverse
  R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
local notation "b" => (fun a : I ⊕ I => match a with
  | Sum.inl j => (Pi.single j (1 : ℝ), (0 : I → ℝ))
  | Sum.inr j => ((0 : I → ℝ), Pi.single j (1 : ℝ)))

include φ Θ hφ hΘ in
/-- The lower actual phase geometry determines the genuine FN covectors and the
reflection action on the same actual inverse-differential coordinate frame. -/
theorem exists_originalFNReflection_native_covectors_and_frame
    (hCompat : Compat)
    (hGeom : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
      R hg hgenus hA hAlt D₀ J hJ hJcuffs hJpants) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∃ n : I → ℤ, ∃ frame : (I ⊕ I) → FormInterior.SmoothVectorField RI (M := T),
      (∀ a q, frame a q = VectorField.mpullback RI FI FN
        (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b a)) q) ∧
      (∀ a q, mvfderiv RI FN q (frame a q) = b a) ∧
      (∀ (q : T) (v : TangentSpace RI q),
        (mvfderiv RI FN (rN q) (mfderiv RI RI rN q v)).1 = (mvfderiv RI FN q v).1 ∧
        ∀ j, (mvfderiv RI FN (rN q) (mfderiv RI RI rN q v)).2 j =
          -(mvfderiv RI FN q v).2 j + (n j : ℝ) / 2 * (mvfderiv RI FN q v).1 j) ∧
      (∀ (q : T) j, mfderiv RI RI rN q (frame (Sum.inl j) q) =
        frame (Sum.inl j) (rN q) + ((n j : ℝ) / 2) • frame (Sum.inr j) (rN q)) ∧
      (∀ (q : T) j, mfderiv RI RI rN q (frame (Sum.inr j) q) =
        -frame (Sum.inr j) (rN q)) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := C
  let : IsManifold RI ω T := realManifold
  obtain ⟨n, hn⟩ := originalFNReflection_real_value_law
    R hp hg hgenus hΓ hsmooth hA hAlt D₀ J hJ hJcuffs hJpants hU φ Θ hφ hΘ hGeom
  obtain ⟨hFN, hinv, frame, hpb, _hvalue, hunit⟩ :=
    exists_same_originalFN_native_coordinate_frame R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  have hr := originalNativeTeichmullerReflection_real_mdifferentiable
    R hp hg hgenus hΓ hsmooth J hJ
  let S := originalFNReflectionCoordinateOperator g n
  have hglobal : FN ∘ rN = (S : F → F) ∘ FN := by
    funext q
    apply Prod.ext
    · exact (hn q).1
    · funext j
      exact (hn q).2 j
  have hchain (q : T) : (mvfderiv RI FN (rN q)).comp (mfderiv RI RI rN q) =
      S.comp (mvfderiv RI FN q) := by
    have hl : mvfderiv RI (FN ∘ rN) q =
        (mvfderiv RI FN (rN q)).comp (mfderiv RI RI rN q) :=
      mvfderiv_comp q (hFN.mdifferentiableAt (by simp)) (hr q)
    have hs : MDifferentiableAt FI FI S (FN q) := S.differentiableAt.mdifferentiableAt
    have hh : mvfderiv RI ((S : F → F) ∘ FN) q =
        (mvfderiv FI (S : F → F) (FN q)).comp (mfderiv RI FI FN q) :=
      mvfderiv_comp q hs (hFN.mdifferentiableAt (by simp))
    have hS : mvfderiv FI (S : F → F) (FN q) =
        S.comp (NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q)).toContinuousLinearMap := by
      simpa only [S.hasFDerivAt.fderiv] using
        (mvfderiv_eq_fderiv (𝕜 := ℝ) (f := (S : F → F)) (x := FN q))
    calc
      (mvfderiv RI FN (rN q)).comp (mfderiv RI RI rN q) =
          mvfderiv RI (FN ∘ rN) q := hl.symm
      _ = mvfderiv RI ((S : F → F) ∘ FN) q :=
        congrArg (fun f : T → F => mvfderiv RI f q) hglobal
      _ = (mvfderiv FI (S : F → F) (FN q)).comp (mfderiv RI FI FN q) := hh
      _ = S.comp (mvfderiv RI FN q) :=
        (congrArg (fun A : TangentSpace FI (FN q) →L[ℝ] F =>
          A.comp (mfderiv RI FI FN q)) hS).trans
            (ContinuousLinearMap.comp_assoc S
              (NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q)).toContinuousLinearMap
              (mfderiv RI FI FN q))
  have hunit' (a : I ⊕ I) (q : T) : mvfderiv RI FN q (frame a q) = b a := hunit a q
  have hinjective (q : T) : Function.Injective (mvfderiv RI FN q) := by
    intro v w h
    apply (hinv q).injective
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN q)).injective h
  have hSL (j : I) : S (b (Sum.inl j)) =
      b (Sum.inl j) + ((n j : ℝ) / 2) • b (Sum.inr j) := by
    ext k <;> by_cases h : j = k <;>
      simp [S, originalFNReflectionCoordinateOperator, Pi.single_apply, h]
    exact fun hkj => False.elim (h hkj.symm)
  have hST (j : I) : S (b (Sum.inr j)) = -b (Sum.inr j) := by
    ext k <;> by_cases h : j = k <;>
      simp [S, originalFNReflectionCoordinateOperator, h]
  refine ⟨n, frame, hpb, hunit', ?_, ?_, ?_⟩
  · intro q v
    have h := congrArg (fun A : TangentSpace RI q →L[ℝ] F => A v) (hchain q)
    change mvfderiv RI FN (rN q) (mfderiv RI RI rN q v) = S (mvfderiv RI FN q v) at h
    constructor
    · simpa [S, originalFNReflectionCoordinateOperator] using congrArg Prod.fst h
    · intro j
      simpa [S, originalFNReflectionCoordinateOperator] using
        congrArg (fun z : F => z.2 j) h
  · intro q j
    apply hinjective (rN q)
    rw [map_add, map_smul, hunit' (Sum.inl j) (rN q), hunit' (Sum.inr j) (rN q)]
    simpa only [ContinuousLinearMap.comp_apply, hunit' (Sum.inl j) q, hSL j] using
      congrArg (fun A : TangentSpace RI q →L[ℝ] F => A (frame (Sum.inl j) q)) (hchain q)
  · intro q j
    apply hinjective (rN q)
    rw [map_neg, hunit' (Sum.inr j) (rN q)]
    simpa only [ContinuousLinearMap.comp_apply, hunit' (Sum.inr j) q, hST j] using
      congrArg (fun A : TangentSpace RI q →L[ℝ] F => A (frame (Sum.inr j) q)) (hchain q)

end LowDimensionalTopology.Geometry.Teichmuller
