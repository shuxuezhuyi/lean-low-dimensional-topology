module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNUnitNativeTwist
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# The same inverse-FN unit curve in actual book coordinates

Only the fixed signs determined by the actual left seam copies change the
retained raw coordinates. The same original inverse-coordinate curve has
book twist speed +1. Its actual book coordinate vector is the signed raw
pullback vector, proved from the literal derivative and inverse, not assumed.
Identification with the actual physical QC surgery curve uses the separate
signed-marking witness and the owned reference-change geometry.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami

/-- The fixed diagonal correction of the actual two FN coordinate blocks. -/
def originalFNBookCoordinateSignEquiv {g : ℕ}
    (left : Fin (3 * g - 3) → Fin 2) :
    ((Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ)) ≃L[ℝ]
      ((Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ)) where
  toFun x := (x.1, fun j => originalFNBookSideSign (left j) * x.2 j)
  invFun x := (x.1, fun j => originalFNBookSideSign (left j) * x.2 j)
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext j
      change originalFNBookSideSign (left j) *
        (originalFNBookSideSign (left j) * x.2 j) = x.2 j
      rw [← mul_assoc, originalFNBookSideSign_sq, one_mul]
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext j
      change originalFNBookSideSign (left j) *
        (originalFNBookSideSign (left j) * x.2 j) = x.2 j
      rw [← mul_assoc, originalFNBookSideSign_sq, one_mul]
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext j
      change originalFNBookSideSign (left j) * (x.2 j + y.2 j) =
        originalFNBookSideSign (left j) * x.2 j +
          originalFNBookSideSign (left j) * y.2 j
      exact mul_add _ _ _
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · funext j
      change originalFNBookSideSign (left j) * (r * x.2 j) =
        r * (originalFNBookSideSign (left j) * x.2 j)
      ring
  continuous_toFun := continuous_fst.prodMk
    (continuous_pi fun j => continuous_const.mul ((continuous_apply j).comp continuous_snd))
  continuous_invFun := continuous_fst.prodMk
    (continuous_pi fun j => continuous_const.mul ((continuous_apply j).comp continuous_snd))

/-- The inverse correction is the same fixed geometric sign correction. -/
theorem originalFNBookCoordinateSignEquiv_symm_apply {g : ℕ}
    (left : Fin (3 * g - 3) → Fin 2)
    (x : (Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ)) :
    (originalFNBookCoordinateSignEquiv left).symm x =
      originalFNBookCoordinateSignEquiv left x := rfl

/-- A book unit twist pulls back under the correction to the actual signed
raw twist unit. Length directions are unchanged by the literal map. -/
theorem originalFNBookCoordinateSignEquiv_twist {g : ℕ}
    (left : Fin (3 * g - 3) → Fin 2) (j : Fin (3 * g - 3)) :
    (originalFNBookCoordinateSignEquiv left).symm
      ((0 : Fin (3 * g - 3) → ℝ), Pi.single j (1 : ℝ)) =
      originalFNBookSideSign (left j) •
        ((0 : Fin (3 * g - 3) → ℝ), Pi.single j (1 : ℝ)) := by
  classical
  rw [originalFNBookCoordinateSignEquiv_symm_apply]
  change ((0 : Fin (3 * g - 3) → ℝ), fun k =>
    originalFNBookSideSign (left k) * (Pi.single (M := fun _ => ℝ) j (1 : ℝ)) k) =
      originalFNBookSideSign (left j) •
        ((0 : Fin (3 * g - 3) → ℝ), Pi.single (M := fun _ => ℝ) j (1 : ℝ))
  apply Prod.ext
  · change (0 : Fin (3 * g - 3) → ℝ) =
      originalFNBookSideSign (left j) • (0 : Fin (3 * g - 3) → ℝ)
    exact (smul_zero _).symm
  · funext k
    change originalFNBookSideSign (left k) *
        (Pi.single (M := fun _ => ℝ) j (1 : ℝ)) k =
      originalFNBookSideSign (left j) *
        (Pi.single (M := fun _ => ℝ) j (1 : ℝ)) k
    by_cases hkj : k = j
    · subst k
      rfl
    · simp only [Pi.single_eq_of_ne hkj, mul_zero]

end LowDimensionalTopology.Geometry.Teichmuller

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

local notation "FN" => originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
local notation "Compat" => Unproved.Teichmuller.OriginalFNNativeSmoothInverse
  R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
local notation "sigma" => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
  hU φ Θ hφ hΘ hRigid hRealize
local notation "unitTwist" => (fun j : Fin (3 * g - 3) =>
  ((0 : Fin (3 * g - 3) → ℝ), Pi.single (M := fun _ => ℝ) j (1 : ℝ)))

/-- The actual native length and book-rescaled twist coordinates, obtained
from the same original FN formula and the actual book full real branch. -/
def originalFNBookNativeCoordinateMap (left : Fin (3 * g - 3) → Fin 2) : T → F :=
  originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀
    (originalFNBookAngle hA Θ left)

local notation "BookFN" => originalFNBookNativeCoordinateMap R hg hgenus hA hAlt D₀ Θ

/-- The book native map is exactly the fixed correction of the raw native map. -/
theorem originalFNBookNativeCoordinateMap_eq (left : Fin (3 * g - 3) → Fin 2) :
    BookFN left = originalFNBookCoordinateSignEquiv left ∘ FN := by
  funext q
  apply Prod.ext
  · rfl
  · funext j
    exact originalFNBookTwistCoordinate_eq R hg hgenus hA hAlt D₀ Θ left
      ⟨finiteFrickeCoordinates hA q, ⟨q, rfl⟩⟩ j

/-- The literal book coordinate pullback of a unit twist is the signed raw
pullback. The derivative and its inverse come from the SAME existing FN map. -/
theorem sameOriginalFN_book_twistVector_eq (hCompat : Compat)
    (left : Fin (3 * g - 3) → Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (j : Fin (3 * g - 3)) (a : T),
      VectorField.mpullback RI FI (BookFN left)
        (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)) a =
      originalFNBookSideSign (left j) • VectorField.mpullback RI FI FN
        (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)) a := by
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  intro j a
  let S := originalFNBookCoordinateSignEquiv left
  have heq := originalFNBookNativeCoordinateMap_eq R hg hgenus hA hAlt D₀ Θ left
  have hreg := sameOriginalFN_native_regular_and_isInvertible
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  have hS : MDifferentiableAt FI FI S (FN a) :=
    (S.toContinuousLinearMap.contMDiffAt (n := ∞)).mdifferentiableAt (by simp)
  have hchain : mfderiv RI FI (BookFN left) a =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (BookFN left a)).symm.toContinuousLinearMap.comp
        (S.toContinuousLinearMap.comp
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN a)).toContinuousLinearMap.comp
            (mfderiv RI FI FN a))) := by
    rw [heq]
    have h := mfderiv_comp a hS ((hreg.1 a).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv, S.fderiv] at h
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_assoc] using h
  change (mfderiv RI FI (BookFN left) a).inverse
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (BookFN left a)).symm (unitTwist j)) =
    originalFNBookSideSign (left j) • (mfderiv RI FI FN a).inverse
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (FN a)).symm (unitTwist j))
  rw [hchain]
  simp only [ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [show S.symm (unitTwist j) = originalFNBookSideSign (left j) • unitTwist j from
    originalFNBookCoordinateSignEquiv_twist left j]
  simp only [map_smul]

/-- The SAME inverse-FN unit curve has book twist speed +1 and actual
native velocity the literal book unit pullback, at every original marked point. -/
theorem sameOriginalFN_unitCurve_book_coordinates_and_twistDerivative (hCompat : Compat)
    (left : Fin (3 * g - 3) → Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (a : T) (j : Fin (3 * g - 3)),
      sigma a j (left j) 0 = a ∧
      (∀ t : ℝ, BookFN left (sigma a j (left j) t) =
        BookFN left a + t • unitTwist j) ∧
      ContMDiffAt 𝓘(ℝ) RI ∞ (sigma a j (left j)) 0 ∧
      HasDerivAt (fun t : ℝ => c (sigma a j (left j) t))
        (D a (VectorField.mpullback RI FI (BookFN left)
          (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)) a)) 0 := by
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  intro a j
  have hraw := sameOriginalFN_unitCurve_native_twistDerivative
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat a j (left j)
  refine ⟨hraw.1, ?_, hraw.2.2.1, ?_⟩
  · intro t
    have hunit : originalFNBookCoordinateSignEquiv left (unitTwist j) =
        originalFNBookSideSign (left j) • unitTwist j :=
      (originalFNBookCoordinateSignEquiv_symm_apply left (unitTwist j)).symm.trans
        (originalFNBookCoordinateSignEquiv_twist left j)
    rw [originalFNBookNativeCoordinateMap_eq, Function.comp_apply, hraw.2.1 t,
      map_add, map_smul, hunit]
    change _ + (originalFNBookSideSign (left j) * t) •
      (originalFNBookSideSign (left j) • unitTwist j) = _ + t • unitTwist j
    have hsign : (originalFNBookSideSign (left j) * t) *
        originalFNBookSideSign (left j) = t := by
      rw [mul_right_comm, originalFNBookSideSign_sq, one_mul]
    simp only [smul_smul, hsign, Function.comp_apply]
  · rw [sameOriginalFN_book_twistVector_eq
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat]
    simpa only [originalFNUnitSideSign, originalFNBookSideSign] using hraw.2.2.2

/-- The concrete left-germ transport input is consumed by actual book phases,
full branches, and the SAME original native inverse-FN curves and coordinate basis. -/
theorem exists_sameOriginalFN_book_coordinates_and_unit_curves
    (hBook : Unproved.Teichmuller.OriginalFNBookLeftCopyTransport D₀)
    (hCompat : Compat) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∃ left : Fin (3 * g - 3) → Fin 2,
      (∀ j, OriginalFNCopyLeftGerm D₀ j (left j)) ∧
      (∀ (m : MarkedRiemannSurface.{0, 0} R)
        (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
        (D₁ : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D₁)
        (j : Fin (3 * g - 3)),
        OriginalFNCopyLeftGerm D₁ j (left j) ∧
          Circle.exp (originalFNBookAngle hA Θ left
            ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
              ⟨TeichmullerSpace.mk m, rfl⟩⟩ j) = originalFNBookPhase D₁ left j) ∧
      ∀ (a : T) (j : Fin (3 * g - 3)),
        sigma a j (left j) 0 = a ∧
        (∀ t : ℝ, BookFN left (sigma a j (left j) t) =
          BookFN left a + t • unitTwist j) ∧
        ContMDiffAt 𝓘(ℝ) RI ∞ (sigma a j (left j)) 0 ∧
        HasDerivAt (fun t : ℝ => c (sigma a j (left j) t))
          (D a (VectorField.mpullback RI FI (BookFN left)
            (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)) a)) 0 := by
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  obtain ⟨left, href, htarget, _htwist⟩ := exists_originalFN_book_coordinates
    R hg hgenus hA hAlt D₀ hBook φ Θ hφ hΘ
  exact ⟨left, href, htarget,
    sameOriginalFN_unitCurve_book_coordinates_and_twistDerivative
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat left⟩

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
