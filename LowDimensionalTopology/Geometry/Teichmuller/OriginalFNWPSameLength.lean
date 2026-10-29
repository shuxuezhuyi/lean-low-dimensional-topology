module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNWPAllTimeConstancy
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.Ring

/-!
# The actual original WP length block on one fixed length fibre

Each step is the actual signed unit FN curve and changes just one full-real
rescaled twist coordinate. The proved all-time coefficient theorem preserves
the actual length-block coefficient at every step. The same FN injectivity
identifies the final marked point with the prescribed same-length target.
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
local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "F" => (I → ℝ) × (I → ℝ)
local notation "RI" => 𝓘(ℝ, E)
local notation "FI" => 𝓘(ℝ, F)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  («I» := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)

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
local notation "sigma" => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
  hU φ Θ hφ hΘ hRigid hRealize
local notation "W" => sameOriginalFNSignedTwistField R hp hg hgenus hΓ hfree hsmooth
  hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
local notation "omegaWP" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "lengthOf" => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus
local notation "L" => (fun (j : I) (q : T) => VectorField.mpullback RI FI FN
  (fun y : F =>
    (ContinuousLinearEquiv.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) y))
      (Pi.single (M := fun _ => ℝ) j (1 : ℝ), (0 : I → ℝ))) q)

variable
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
    (hCompat : Unproved.Teichmuller.OriginalFNNativeSmoothInverse
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize)
    (side : Fin (3 * g - 3) → Fin 2)

local notation "hFlow" => sameOriginalFN_unitCurve_localFlowData
  R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat

include hFrickeBers hvariation hjets hCompat
/-- The same actual FN data give equal WP length-block coefficients at any two
native marked points with equal full original cuff-length vectors. -/
theorem sameOriginalFN_wpLengthBlock_eq_of_same_lengths
    (hCartan : letI := C
      letI : IsManifold RI ω T := realManifold
      ∀ (k : I) (Y Z : FormInterior.SmoothVectorField RI (M := T)),
        Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
          R hp hg hgenus hΓ hfree hsmooth hWP ⊤ 1 (by norm_num)
          (fun t a => sigma a k (side k) t) (W hCompat k (side k)) Y Z
          (hFlow k (side k)).1 (hFlow k (side k)).2.1
          (hFlow k (side k)).2.2.1 (hFlow k (side k)).2.2.2)
    (hDual : letI := C
      ∀ (q : T) (k : I) (v : TangentSpace RI q),
        omegaWP q ![W hCompat k (side k) q, v] =
          mfderiv RI 𝓘(ℝ) (lengthOf (D₀.cuff k).toLoop) q v) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (p q : T), (FN p).1 = (FN q).1 → ∀ i j : I,
      omegaWP p ![L i p, L j p] = omegaWP q ![L i q, L j q] := by
  classical
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only at hCartan hDual ⊢
  intro p q hlength i j
  let A : T → ℝ := fun a => omegaWP a ![L i a, L j a]
  have hsigma (k : I) (a : T) (t : ℝ) : A (sigma a k (side k) t) = A a := by
    obtain ⟨frame, hframe, hconstant⟩ :=
      sameOriginalFN_wpCoefficient_unitCurve_constant
        R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
        hWP hFrickeBers hvariation hjets hCompat k (side k) (hCartan k)
        (fun a v => hDual a k v)
    simpa only [one_smul, hframe] using hconstant (Sum.inl i) (Sum.inl j) 1 1 a t
  have hsign (k : I) :
      originalFNUnitSideSign (side k) * originalFNUnitSideSign (side k) = 1 := by
    by_cases hk : side k = 0 <;> simp [originalFNUnitSideSign, hk]
  let step : T → I → T := fun a k => sigma a k (side k)
    (originalFNUnitSideSign (side k) * ((FN q).2 k - (FN a).2 k))
  have hstep (a : T) (k : I) :
      (FN (step a k)).1 = (FN a).1 ∧
      (FN (step a k)).2 = Function.update (FN a).2 k ((FN q).2 k) := by
    have hline := (sameOriginalFN_unitCurve_native_coordinates
      R hg hgenus hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize a k (side k)).2
      (originalFNUnitSideSign (side k) * ((FN q).2 k - (FN a).2 k))
    rw [← mul_assoc, hsign k, one_mul] at hline
    change FN (step a k) = FN a + ((FN q).2 k - (FN a).2 k) •
      ((0 : I → ℝ), Pi.single k (1 : ℝ)) at hline
    rw [hline]
    constructor
    · funext u
      simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]
    · funext u
      by_cases huk : u = k
      · subst u
        simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
          Pi.single_eq_same, smul_eq_mul, mul_one, Function.update_self]
        ring
      · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
          Pi.single_eq_of_ne huk, smul_eq_mul, mul_zero, add_zero,
          Function.update_of_ne huk]
  let seq : ℕ → T := Nat.rec p (fun m a =>
    if hm : m < 3 * g - 3 then step a ⟨m, hm⟩ else a)
  have hnext (m : ℕ) (hm : m < 3 * g - 3) :
      seq (m + 1) = step (seq m) ⟨m, hm⟩ := by
    change (if h : m < 3 * g - 3 then step (seq m) ⟨m, h⟩ else seq m) = _
    simp only [dite_eq_left hm]
  have hcoordinates : ∀ m : ℕ, m ≤ 3 * g - 3 →
      (FN (seq m)).1 = (FN p).1 ∧
      ∀ k : I, k.val < m → (FN (seq m)).2 k = (FN q).2 k := by
    intro m
    induction m with
    | zero =>
        intro _
        refine ⟨rfl, ?_⟩
        intro k hk
        omega
    | succ m ih =>
        intro hmn
        have hm : m < 3 * g - 3 := by omega
        have hprev := ih (by omega)
        rw [hnext m hm]
        refine ⟨(hstep (seq m) ⟨m, hm⟩).1.trans hprev.1, ?_⟩
        intro k hk
        rw [(hstep (seq m) ⟨m, hm⟩).2]
        by_cases hkm : k = ⟨m, hm⟩
        · subst k
          exact Function.update_self _ _ _
        · rw [Function.update_of_ne hkm]
          apply hprev.2 k
          have hv : k.val ≠ m := by
            intro he
            exact hkm (Fin.ext he)
          omega
  have hend : seq (3 * g - 3) = q := by
    apply sameOriginalFN_native_injective
      R hg hgenus hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
    apply Prod.ext
    · exact (hcoordinates _ le_rfl).1.trans hlength
    · funext k
      exact (hcoordinates _ le_rfl).2 k k.isLt
  have hvalue : ∀ m : ℕ, m ≤ 3 * g - 3 → A (seq m) = A p := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
        intro hmn
        have hm : m < 3 * g - 3 := by omega
        rw [hnext m hm]
        exact (hsigma ⟨m, hm⟩ (seq m)
          (originalFNUnitSideSign (side ⟨m, hm⟩) *
            ((FN q).2 ⟨m, hm⟩ - (FN (seq m)).2 ⟨m, hm⟩))).trans (ih (by omega))
  have h := hvalue (3 * g - 3) le_rfl
  rw [hend] at h
  exact h.symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
