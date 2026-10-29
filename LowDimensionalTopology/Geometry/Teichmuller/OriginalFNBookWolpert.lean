module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookReflectionLengthBlock
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookFormExpansion
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNWPSameLength
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNAllPointLengthDuality
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The actual English-normalized book Wolpert formula on a compatible reference

The same geometric book-left witness may be supplied explicitly or selected
by the unchanged canonical-choice wrappers. No equality of choices is needed. The true
all-point physical length-duality producer, real FN all-time coefficient
comparison, given-reflection frame and anti-symplectic producers kill LL.
The actual native tangent/form expansions then give the complete coefficient
one formula, with no duality, block value or final formula assumed.

The compatible reflection preserves this full original pants data. Transport
from an arbitrary original reference/decomposition remains a separate genuine
reference-change assembly; no reflection is asserted for every surface or
arbitrary pants system on a fixed reflected surface.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation GeneralQC TeichmullerSpace GammaMeasurableBeltrami
open NormalizedCoefficientTransport

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

section ExplicitBookLeft
variable (left : Fin (3 * g - 3) → Fin 2)

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

local notation "omega" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "length" => (fun j : I =>
  markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus (OriginalClosedGeodesic.toLoop (D₀.cuff j)))

local notation "Rebase" => Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
  R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left
local notation "Lraw" => (fun (j : I) (q : T) => VectorField.mpullback RI FI Nraw
  (fun y : F => (ContinuousLinearEquiv.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) y)) (b (Sum.inl j))) q)


local notation "sigma" => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
  hU φ Θ hφ hΘ hRigid hRealize
local notation "W" => sameOriginalFNSignedTwistField R hp hg hgenus hΓ hfree hsmooth
  hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize

/-- The actual physical producer discharges book length duality; this is not
a new hypothesis or Unproved input to either final consumer below. -/
private theorem fixedLeft_length_duality
    (hCompat : Unproved.Teichmuller.OriginalFNNativeSmoothInverse
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize)
    (hRebase : Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
      R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left) :
    letI := C
    ∀ (a : T) (j : I) (z : TangentSpace RI a),
      omega a ![V j a, z] = mfderiv RI 𝓘(ℝ) (length j) a z := by
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  have hsigned := sameOriginalFN_signed_twist_length_duality
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left hCompat hRebase
  intro a j z
  rw [sameOriginalFN_book_twistVector_eq
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat left j a]
  simpa only [originalFNBookSideSign, originalFNUnitSideSign] using hsigned a j z


/-- Actual all-time same-length comparison and actual reflection negation
force the book LL block to vanish at every point of this fixed original space. -/
private theorem fixedLeft_length_length_zero
    (hWPForm : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
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
    (hRebase : Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
      R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left)
    (hGeom : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
      R hg hgenus hA hAlt D₀ J hJ hJcuffs hJpants)
    (hWPReflection : Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
      R hp hg hgenus hΓ J hJ hsmooth)
    (hCartan :
      let freeR := closedUniformization_deckActsFreely R hp
      letI := canonicalComplexChartedSpace R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth
      letI : IsManifold 𝓘(ℝ, Fin (3 * g - 3) → ℂ) ω (TeichmullerSpace R) :=
        Topology.IsOpenEmbedding.isManifold_singleton
          («I» := 𝓘(ℝ, Fin (3 * g - 3) → ℂ)) (n := ω)
          (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
            (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth)
      ∀ (k : Fin (3 * g - 3))
        (Y Z : FormInterior.SmoothVectorField 𝓘(ℝ, Fin (3 * g - 3) → ℂ)
          (M := TeichmullerSpace R)),
        let data := sameOriginalFN_unitCurve_localFlowData
          R hp hg hgenus hΓ freeR hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)
        Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
          R hp hg hgenus hΓ freeR hsmooth hWPForm ⊤ 1 (by norm_num)
          (fun t a => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
            hU φ Θ hφ hΘ hRigid hRealize a k (left k) t)
          (sameOriginalFNSignedTwistField R hp hg hgenus hΓ freeR hsmooth
            hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)) Y Z
          data.1 data.2.1 data.2.2.1 data.2.2.2) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (q : T) (j k : I), omega q ![L j q, L k q] = 0 := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  have hDualBook := fixedLeft_length_duality
    R hp hg hgenus hΓ hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left hCompat hRebase
  have hsigned := sameOriginalFN_signed_twist_length_duality
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left hCompat hRebase
  have hDualW (q : T) (j : I) (z : TangentSpace RI q) :
      omega q ![W hCompat j (left j) q, z] = mfderiv RI 𝓘(ℝ) (length j) q z := by
    change omega q ![originalFNUnitSideSign (left j) •
      VectorField.mpullback RI FI Nraw
        (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b (Sum.inr j))) q, z] = _
    exact hsigned q j z
  have hsame := sameOriginalFN_wpLengthBlock_eq_of_same_lengths
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
    hWPForm hFrickeBers hvariation hjets hCompat left hCartan hDualW
  have hnegative := originalFNBook_length_length_reflection_negates
    R hp hg hgenus hΓ hsmooth hA hAlt D₀ J hJ hJcuffs hJpants
    hU φ Θ hφ hΘ hRigid hRealize left hCompat hGeom hWPReflection hDualBook
  obtain ⟨_n, hvalue⟩ := originalFNReflection_real_value_law
    R hp hg hgenus hΓ hsmooth hA hAlt D₀ J hJ hJcuffs hJpants hU φ Θ hφ hΘ hGeom
  have hbook := sameOriginalFN_book_tangent_expansion
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat left
  have hraw := sameOriginalFN_native_regular_and_isInvertible
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  let S := originalFNBookCoordinateSignEquiv left
  have heq := originalFNBookNativeCoordinateMap_eq R hg hgenus hA hAlt D₀ Θ left
  have hchain (q : T) : mvfderiv RI Nbook q =
      S.toContinuousLinearMap.comp (mvfderiv RI Nraw q) := by
    rw [heq]
    have hS : MDifferentiableAt FI FI S (Nraw q) :=
      (S.toContinuousLinearMap.contMDiffAt (n := ∞)).mdifferentiableAt (by simp)
    have h := mvfderiv_comp q hS ((hraw.1 q).mdifferentiableAt (by simp))
    rw [mvfderiv_eq_fderiv, S.fderiv] at h
    simpa only [mvfderiv, Function.comp_apply, ContinuousLinearMap.comp_assoc] using h
  have hbookUnit (q : T) (y : F) : mvfderiv RI Nbook q
      (VectorField.mpullback RI FI Nbook
        (fun z : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm y) q) = y := by
    change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook q))
      (mfderiv RI FI Nbook q ((mfderiv RI FI Nbook q).inverse
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook q)).symm y))) = y
    rw [(hbook.2.1 q).self_apply_inverse]
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook q)).apply_symm_apply y
  have hrawUnit (q : T) (y : F) : mvfderiv RI Nraw q
      (VectorField.mpullback RI FI Nraw
        (fun z : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm y) q) = y := by
    change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nraw q))
      (mfderiv RI FI Nraw q ((mfderiv RI FI Nraw q).inverse
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nraw q)).symm y))) = y
    rw [(hraw.2 q).self_apply_inverse]
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nraw q)).apply_symm_apply y
  have hinjective (q : T) : Function.Injective (mvfderiv RI Nbook q) := by
    intro v w h
    apply (hbook.2.1 q).injective
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook q)).injective h
  have hLraw (q : T) (j : I) : L j q = Lraw j q := by
    apply hinjective q
    rw [hbookUnit, hchain, ContinuousLinearMap.comp_apply, hrawUnit]
    apply Prod.ext
    · rfl
    · funext k
      change (0 : ℝ) = originalFNBookSideSign (left k) * 0
      rw [mul_zero]
  intro q j k
  have hequal : omega (rN q) ![L j (rN q), L k (rN q)] = omega q ![L j q, L k q] := by
    simpa only [hLraw] using hsame (rN q) q (hvalue q).1 j k
  have hnegative' := hnegative q j k
  linarith

/-- The complete English coefficient-one Wolpert formula on the literal
certified book coordinates of this compatible original reference. -/
private theorem fixedLeft_Wolpert
    (hWPForm : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
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
    (hRebase : Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
      R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left)
    (hGeom : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
      R hg hgenus hA hAlt D₀ J hJ hJcuffs hJpants)
    (hWPReflection : Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
      R hp hg hgenus hΓ J hJ hsmooth)
    (hCartan :
      let freeR := closedUniformization_deckActsFreely R hp
      letI := canonicalComplexChartedSpace R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth
      letI : IsManifold 𝓘(ℝ, Fin (3 * g - 3) → ℂ) ω (TeichmullerSpace R) :=
        Topology.IsOpenEmbedding.isManifold_singleton
          («I» := 𝓘(ℝ, Fin (3 * g - 3) → ℂ)) (n := ω)
          (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
            (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth)
      ∀ (k : Fin (3 * g - 3))
        (Y Z : FormInterior.SmoothVectorField 𝓘(ℝ, Fin (3 * g - 3) → ℂ)
          (M := TeichmullerSpace R)),
        let data := sameOriginalFN_unitCurve_localFlowData
          R hp hg hgenus hΓ freeR hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)
        Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
          R hp hg hgenus hΓ freeR hsmooth hWPForm ⊤ 1 (by norm_num)
          (fun t a => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
            hU φ Θ hφ hΘ hRigid hRealize a k (left k) t)
          (sameOriginalFNSignedTwistField R hp hg hgenus hΓ freeR hsmooth
            hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)) Y Z
          data.1 data.2.1 data.2.2.1 data.2.2.2) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (q : T) (v w : TangentSpace RI q),
      omega q ![v, w] = ∑ j,
        ((mvfderiv RI Nbook q v).2 j * (mvfderiv RI Nbook q w).1 j -
          (mvfderiv RI Nbook q v).1 j * (mvfderiv RI Nbook q w).2 j) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := C
  let : IsManifold RI ω T := realManifold
  have hLL := fixedLeft_length_length_zero
    R hp hg hgenus hΓ hsmooth hA hAlt D₀ J hJ hJcuffs hJpants hU φ Θ hφ hΘ hRigid hRealize left
    hWPForm hFrickeBers hvariation hjets hCompat hRebase hGeom hWPReflection hCartan
  have hDualBook := fixedLeft_length_duality
    R hp hg hgenus hΓ hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left hCompat hRebase
  have hblocks := sameOriginalFN_book_twist_blocks_of_length_duality
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left hCompat hDualBook
  intro q v w
  let DN := mvfderiv RI Nbook q
  have hLT (j k : I) : omega q ![L j q, V k q] = -(if k = j then (1 : ℝ) else 0) := by
    have hswap : omega q ![L j q, V k q] = -(omega q ![V k q, L j q]) := by
      simpa only [ContinuousAlternatingMap.coe_toAlternatingMap,
        Matrix.cons_cons_comp_swap_zero_one] using
        (omega q).toAlternatingMap.map_swap ![V k q, L j q] (by decide : (0 : Fin 2) ≠ 1)
    exact hswap.trans (congrArg Neg.neg (hblocks q k j).1)
  have hTL (j k : I) : omega q ![V j q, L k q] = (if j = k then (1 : ℝ) else 0) :=
    (hblocks q j k).1
  have hTT (j k : I) : omega q ![V j q, V k q] = 0 := (hblocks q j k).2
  have hdelta (f : I → ℝ) (j : I) :
      (∑ k, f k * (if j = k then (1 : ℝ) else 0)) = f j := by
    simpa only [mul_ite, mul_one, mul_zero] using
      Finset.sum_ite_eq_of_mem Finset.univ j f (Finset.mem_univ j)
  have hdelta' (f : I → ℝ) (j : I) :
      (∑ k, f k * (if k = j then (1 : ℝ) else 0)) = f j := by
    simpa only [mul_ite, mul_one, mul_zero] using
      Finset.sum_ite_eq_of_mem' Finset.univ j f (Finset.mem_univ j)
  have hnegdelta (f : I → ℝ) (j : I) :
      (∑ k, f k * (-(if k = j then (1 : ℝ) else 0))) = -(f j) := by
    simp only [mul_neg, Finset.sum_neg_distrib, hdelta']
  calc
    omega q ![v, w] =
        (∑ j, (DN v).1 j *
          ((∑ k, (DN w).1 k * omega q ![L j q, L k q]) +
            ∑ k, (DN w).2 k * omega q ![L j q, V k q])) +
        ∑ j, (DN v).2 j *
          ((∑ k, (DN w).1 k * omega q ![V j q, L k q]) +
            ∑ k, (DN w).2 k * omega q ![V j q, V k q]) :=
      sameOriginalFN_book_form_block_expansion
        R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left hCompat q v w
    _ = (∑ j, (DN v).1 j * (-(DN w).2 j)) + ∑ j, (DN v).2 j * (DN w).1 j := by
      simp only [hLL, hTT, hLT, hTL, mul_zero, Finset.sum_const_zero,
        zero_add, add_zero, hdelta, hnegdelta]
    _ = ∑ j, ((DN v).2 j * (DN w).1 j - (DN v).1 j * (DN w).2 j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

/-- The English corollary for each SAME actual cuff of the compatible
decomposition: its literal book length pullback contracts to minus d(bookTau).
No arbitrary new decomposition or reference is substituted here. -/
private theorem fixedLeft_length_contraction
    (hWPForm : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
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
    (hRebase : Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
      R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left)
    (hGeom : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
      R hg hgenus hA hAlt D₀ J hJ hJcuffs hJpants)
    (hWPReflection : Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
      R hp hg hgenus hΓ J hJ hsmooth)
    (hCartan :
      let freeR := closedUniformization_deckActsFreely R hp
      letI := canonicalComplexChartedSpace R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth
      letI : IsManifold 𝓘(ℝ, Fin (3 * g - 3) → ℂ) ω (TeichmullerSpace R) :=
        Topology.IsOpenEmbedding.isManifold_singleton
          («I» := 𝓘(ℝ, Fin (3 * g - 3) → ℂ)) (n := ω)
          (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
            (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth)
      ∀ (k : Fin (3 * g - 3))
        (Y Z : FormInterior.SmoothVectorField 𝓘(ℝ, Fin (3 * g - 3) → ℂ)
          (M := TeichmullerSpace R)),
        let data := sameOriginalFN_unitCurve_localFlowData
          R hp hg hgenus hΓ freeR hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)
        Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
          R hp hg hgenus hΓ freeR hsmooth hWPForm ⊤ 1 (by norm_num)
          (fun t a => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
            hU φ Θ hφ hΘ hRigid hRealize a k (left k) t)
          (sameOriginalFNSignedTwistField R hp hg hgenus hΓ freeR hsmooth
            hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)) Y Z
          data.1 data.2.1 data.2.2.1 data.2.2.2) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (q : T) (j : I) (z : TangentSpace RI q),
      omega q ![L j q, z] =
        -mfderiv RI 𝓘(ℝ) (fun a : T => (Nbook a).2 j) q z := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  have hWolpert := fixedLeft_Wolpert
    R hp hg hgenus hΓ hsmooth hA hAlt D₀ J hJ hJcuffs hJpants hU φ Θ hφ hΘ hRigid hRealize left
    hWPForm hFrickeBers hvariation hjets hCompat hRebase hGeom hWPReflection hCartan
  have hbook := sameOriginalFN_book_tangent_expansion
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat left
  let P (j : I) : F →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.snd ℝ (I → ℝ) (I → ℝ))
  have htauDeriv (q : T) (j : I) (z : TangentSpace RI q) :
      mfderiv RI 𝓘(ℝ) (fun a : T => (Nbook a).2 j) q z =
        (mvfderiv RI Nbook q z).2 j := by
    change mvfderiv RI ((P j : F → ℝ) ∘ Nbook) q z = P j (mvfderiv RI Nbook q z)
    have h := mvfderiv_comp q (P j).differentiableAt.mdifferentiableAt
      ((hbook.1 q).mdifferentiableAt (by simp))
    rw [mvfderiv_eq_fderiv, (P j).hasFDerivAt.fderiv] at h
    simpa only [mvfderiv, ContinuousLinearMap.comp_apply] using
      congrArg (fun A : TangentSpace RI q →L[ℝ] ℝ => A z) h
  have hunit (q : T) (j : I) : mvfderiv RI Nbook q (L j q) = b (Sum.inl j) := by
    change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook q))
      (mfderiv RI FI Nbook q ((mfderiv RI FI Nbook q).inverse
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook q)).symm (b (Sum.inl j))))) = _
    rw [(hbook.2.1 q).self_apply_inverse]
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook q)).apply_symm_apply _
  intro q j z
  have h := hWolpert q (L j q) z
  rw [hunit q j] at h
  change omega q ![L j q, z] = ∑ k,
    ((0 : ℝ) * (mvfderiv RI Nbook q z).1 k -
      (Pi.single (M := fun _ => ℝ) j (1 : ℝ)) k * (mvfderiv RI Nbook q z).2 k) at h
  have hsum : (∑ k, (Pi.single (M := fun _ => ℝ) j (1 : ℝ)) k * (mvfderiv RI Nbook q z).2 k) =
      (mvfderiv RI Nbook q z).2 j := by
    simpa only [Pi.single_apply, ite_mul, one_mul, zero_mul] using
      Finset.sum_ite_eq_of_mem' Finset.univ j
        (fun k : I => (mvfderiv RI Nbook q z).2 k) (Finset.mem_univ j)
  rw [htauDeriv]
  calc
    omega q ![L j q, z] = ∑ k,
        ((0 : ℝ) * (mvfderiv RI Nbook q z).1 k -
          (Pi.single (M := fun _ => ℝ) j (1 : ℝ)) k * (mvfderiv RI Nbook q z).2 k) := h
    _ = -(∑ k, (Pi.single (M := fun _ => ℝ) j (1 : ℝ)) k * (mvfderiv RI Nbook q z).2 k) := by
      simp only [zero_mul, zero_sub, Finset.sum_neg_distrib]
    _ = -(mvfderiv RI Nbook q z).2 j := congrArg Neg.neg hsum

/-- The original book-left geometric witness is supplied explicitly. The
same fixed labels and their actual reference/all-target germs are returned with
all three actual consequences. No choice comparison or new geometric gap is used. -/
theorem sameOriginalFN_book_core_for_left
    (hWPForm : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
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
    (hRebase : Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
      R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left)
    (hGeom : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
      R hg hgenus hA hAlt D₀ J hJ hJcuffs hJpants)
    (hWPReflection : Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
      R hp hg hgenus hΓ J hJ hsmooth)
    (hCartan :
      let freeR := closedUniformization_deckActsFreely R hp
      letI := canonicalComplexChartedSpace R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth
      letI : IsManifold 𝓘(ℝ, Fin (3 * g - 3) → ℂ) ω (TeichmullerSpace R) :=
        Topology.IsOpenEmbedding.isManifold_singleton
          («I» := 𝓘(ℝ, Fin (3 * g - 3) → ℂ)) (n := ω)
          (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
            (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth)
      ∀ (k : Fin (3 * g - 3))
        (Y Z : FormInterior.SmoothVectorField 𝓘(ℝ, Fin (3 * g - 3) → ℂ)
          (M := TeichmullerSpace R)),
        let data := sameOriginalFN_unitCurve_localFlowData
          R hp hg hgenus hΓ freeR hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)
        Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
          R hp hg hgenus hΓ freeR hsmooth hWPForm ⊤ 1 (by norm_num)
          (fun t a => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
            hU φ Θ hφ hΘ hRigid hRealize a k (left k) t)
          (sameOriginalFNSignedTwistField R hp hg hgenus hΓ freeR hsmooth
            hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)) Y Z
          data.1 data.2.1 data.2.2.1 data.2.2.2)
    (hLeft : (∀ j, OriginalFNCopyLeftGerm D₀ j (left j)) ∧
      ∀ (m : MarkedRiemannSurface.{0, 0} R)
        (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
        (D : OriginalFNRealization N inc),
        OriginalFNMarkedTransport D₀ m D → ∀ j, OriginalFNCopyLeftGerm D j (left j)) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    letI : IsManifold RI ω T := realManifold
    (∀ j, OriginalFNCopyLeftGerm D₀ j (left j)) ∧
    (∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc),
      OriginalFNMarkedTransport D₀ m D → ∀ j, OriginalFNCopyLeftGerm D j (left j)) ∧
    (∀ (q : T) (j k : I), omega q ![L j q, L k q] = 0) ∧
    (∀ (q : T) (v w : TangentSpace RI q),
      omega q ![v, w] = ∑ j,
        ((mvfderiv RI Nbook q v).2 j * (mvfderiv RI Nbook q w).1 j -
          (mvfderiv RI Nbook q v).1 j * (mvfderiv RI Nbook q w).2 j)) ∧
    ∀ (q : T) (j : I) (z : TangentSpace RI q),
      omega q ![L j q, z] = -mfderiv RI 𝓘(ℝ) (fun a : T => (Nbook a).2 j) q z := by
  let := R.toRiemannAtlas.toChartedSpace
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  exact ⟨hLeft.1, hLeft.2,
    fixedLeft_length_length_zero
      R hp hg hgenus hΓ hsmooth hA hAlt D₀ J hJ hJcuffs hJpants hU φ Θ hφ hΘ hRigid hRealize left
      hWPForm hFrickeBers hvariation hjets hCompat hRebase hGeom hWPReflection hCartan,
    fixedLeft_Wolpert
      R hp hg hgenus hΓ hsmooth hA hAlt D₀ J hJ hJcuffs hJpants hU φ Θ hφ hΘ hRigid hRealize left
      hWPForm hFrickeBers hvariation hjets hCompat hRebase hGeom hWPReflection hCartan,
    fixedLeft_length_contraction
      R hp hg hgenus hΓ hsmooth hA hAlt D₀ J hJ hJcuffs hJpants hU φ Θ hφ hΘ hRigid hRealize left
      hWPForm hFrickeBers hvariation hjets hCompat hRebase hGeom hWPReflection hCartan⟩

end ExplicitBookLeft

section ChosenBookLeft
variable (hBook : Unproved.Teichmuller.OriginalFNBookLeftCopyTransport D₀)
local notation "left" => Classical.choose hBook

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

local notation "omega" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "length" => (fun j : I =>
  markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus (OriginalClosedGeodesic.toLoop (D₀.cuff j)))

local notation "Rebase" => Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
  R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left
local notation "Lraw" => (fun (j : I) (q : T) => VectorField.mpullback RI FI Nraw
  (fun y : F => (ContinuousLinearEquiv.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) y)) (b (Sum.inl j))) q)


local notation "sigma" => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
  hU φ Θ hφ hΘ hRigid hRealize
local notation "W" => sameOriginalFNSignedTwistField R hp hg hgenus hΓ hfree hsmooth
  hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize


/-- The original canonical choice contract, specialized from the same
explicit-left core using the genuine witness supplied by hBook. -/
theorem sameOriginalFN_book_length_length_zero
    (hWPForm : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
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
    (hRebase : Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
      R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left)
    (hGeom : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
      R hg hgenus hA hAlt D₀ J hJ hJcuffs hJpants)
    (hWPReflection : Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
      R hp hg hgenus hΓ J hJ hsmooth)
    (hCartan :
      let freeR := closedUniformization_deckActsFreely R hp
      letI := canonicalComplexChartedSpace R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth
      letI : IsManifold 𝓘(ℝ, Fin (3 * g - 3) → ℂ) ω (TeichmullerSpace R) :=
        Topology.IsOpenEmbedding.isManifold_singleton
          («I» := 𝓘(ℝ, Fin (3 * g - 3) → ℂ)) (n := ω)
          (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
            (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth)
      ∀ (k : Fin (3 * g - 3))
        (Y Z : FormInterior.SmoothVectorField 𝓘(ℝ, Fin (3 * g - 3) → ℂ)
          (M := TeichmullerSpace R)),
        let data := sameOriginalFN_unitCurve_localFlowData
          R hp hg hgenus hΓ freeR hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)
        Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
          R hp hg hgenus hΓ freeR hsmooth hWPForm ⊤ 1 (by norm_num)
          (fun t a => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
            hU φ Θ hφ hΘ hRigid hRealize a k (left k) t)
          (sameOriginalFNSignedTwistField R hp hg hgenus hΓ freeR hsmooth
            hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)) Y Z
          data.1 data.2.1 data.2.2.1 data.2.2.2) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (q : T) (j k : I), omega q ![L j q, L k q] = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  have h := sameOriginalFN_book_core_for_left
    R hp hg hgenus hΓ hsmooth hA hAlt D₀ J hJ hJcuffs hJpants hU φ Θ hφ hΘ hRigid hRealize left
      hWPForm hFrickeBers hvariation hjets hCompat hRebase hGeom hWPReflection hCartan
    (Classical.choose_spec hBook)
  exact h.2.2.1

/-- The original canonical choice contract, specialized from the same
explicit-left core using the genuine witness supplied by hBook. -/
theorem sameOriginalFN_book_Wolpert_of_compatible_reflection
    (hWPForm : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
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
    (hRebase : Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
      R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left)
    (hGeom : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
      R hg hgenus hA hAlt D₀ J hJ hJcuffs hJpants)
    (hWPReflection : Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
      R hp hg hgenus hΓ J hJ hsmooth)
    (hCartan :
      let freeR := closedUniformization_deckActsFreely R hp
      letI := canonicalComplexChartedSpace R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth
      letI : IsManifold 𝓘(ℝ, Fin (3 * g - 3) → ℂ) ω (TeichmullerSpace R) :=
        Topology.IsOpenEmbedding.isManifold_singleton
          («I» := 𝓘(ℝ, Fin (3 * g - 3) → ℂ)) (n := ω)
          (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
            (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth)
      ∀ (k : Fin (3 * g - 3))
        (Y Z : FormInterior.SmoothVectorField 𝓘(ℝ, Fin (3 * g - 3) → ℂ)
          (M := TeichmullerSpace R)),
        let data := sameOriginalFN_unitCurve_localFlowData
          R hp hg hgenus hΓ freeR hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)
        Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
          R hp hg hgenus hΓ freeR hsmooth hWPForm ⊤ 1 (by norm_num)
          (fun t a => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
            hU φ Θ hφ hΘ hRigid hRealize a k (left k) t)
          (sameOriginalFNSignedTwistField R hp hg hgenus hΓ freeR hsmooth
            hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)) Y Z
          data.1 data.2.1 data.2.2.1 data.2.2.2) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (q : T) (v w : TangentSpace RI q),
      omega q ![v, w] = ∑ j,
        ((mvfderiv RI Nbook q v).2 j * (mvfderiv RI Nbook q w).1 j -
          (mvfderiv RI Nbook q v).1 j * (mvfderiv RI Nbook q w).2 j) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := C
  let : IsManifold RI ω T := realManifold
  have h := sameOriginalFN_book_core_for_left
    R hp hg hgenus hΓ hsmooth hA hAlt D₀ J hJ hJcuffs hJpants hU φ Θ hφ hΘ hRigid hRealize left
      hWPForm hFrickeBers hvariation hjets hCompat hRebase hGeom hWPReflection hCartan
    (Classical.choose_spec hBook)
  exact h.2.2.2.1

/-- The original canonical choice contract, specialized from the same
explicit-left core using the genuine witness supplied by hBook. -/
theorem sameOriginalFN_book_length_contraction_of_compatible_reflection
    (hWPForm : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
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
    (hRebase : Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
      R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left)
    (hGeom : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
      R hg hgenus hA hAlt D₀ J hJ hJcuffs hJpants)
    (hWPReflection : Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
      R hp hg hgenus hΓ J hJ hsmooth)
    (hCartan :
      let freeR := closedUniformization_deckActsFreely R hp
      letI := canonicalComplexChartedSpace R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth
      letI : IsManifold 𝓘(ℝ, Fin (3 * g - 3) → ℂ) ω (TeichmullerSpace R) :=
        Topology.IsOpenEmbedding.isManifold_singleton
          («I» := 𝓘(ℝ, Fin (3 * g - 3) → ℂ)) (n := ω)
          (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
            (canonicalHandleGroupPresentation g) hΓ freeR hp hsmooth)
      ∀ (k : Fin (3 * g - 3))
        (Y Z : FormInterior.SmoothVectorField 𝓘(ℝ, Fin (3 * g - 3) → ℂ)
          (M := TeichmullerSpace R)),
        let data := sameOriginalFN_unitCurve_localFlowData
          R hp hg hgenus hΓ freeR hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)
        Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
          R hp hg hgenus hΓ freeR hsmooth hWPForm ⊤ 1 (by norm_num)
          (fun t a => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
            hU φ Θ hφ hΘ hRigid hRealize a k (left k) t)
          (sameOriginalFNSignedTwistField R hp hg hgenus hΓ freeR hsmooth
            hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k (left k)) Y Z
          data.1 data.2.1 data.2.2.1 data.2.2.2) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (q : T) (j : I) (z : TangentSpace RI q),
      omega q ![L j q, z] =
        -mfderiv RI 𝓘(ℝ) (fun a : T => (Nbook a).2 j) q z := by
  let := R.toRiemannAtlas.toChartedSpace
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  have h := sameOriginalFN_book_core_for_left
    R hp hg hgenus hΓ hsmooth hA hAlt D₀ J hJ hJcuffs hJpants hU φ Θ hφ hΘ hRigid hRealize left
      hWPForm hFrickeBers hvariation hjets hCompat hRebase hGeom hWPReflection hCartan
    (Classical.choose_spec hBook)
  exact h.2.2.2.2

end ChosenBookLeft
end LowDimensionalTopology.Geometry.Teichmuller
