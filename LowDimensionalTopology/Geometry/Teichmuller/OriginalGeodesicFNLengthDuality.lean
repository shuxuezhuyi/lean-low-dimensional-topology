module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNAllPointLengthDuality
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookUnitCurve
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNContinuousRealBranch
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNReferenceContainingGeodesic

/-!
# The WP metric and length duality of a prescribed original geodesic

One rich reference realization retains the original full oriented geodesic.
The geometric phase input produces an actual continuous real branch. The
intrinsic left-copy input fixes the same book order on every marked target.
The literal book twist pullback then has both the actual WP contraction
and the metric dual identity, with the English coefficient one.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Bundle Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3 * g - 3) → ℂ
local notation "V" => (Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ)
local notation "RI" => 𝓘(ℝ, E)
local notation "FI" => 𝓘(ℝ, V)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "r" => nativeRealComplexTangentEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "metric" => nativeWeilPeterssonRealBilinForm R hp hg hgenus hΓ hfree hsmooth
local notation "omega" => nativeWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hfree hsmooth
local notation "unitTwist" => (fun j : Fin (3 * g - 3) =>
  ((0 : Fin (3 * g - 3) → ℝ), Pi.single (M := fun _ => ℝ) j (1 : ℝ)))

/-- A prescribed original geodesic has an actual admissible real FN branch
and a coherent geometric book side. Its literal book unit-twist field has
the full original length covector as both its WP contraction and the metric
dual of its actual complex-structure rotation at every original point. -/
theorem originalGeodesic_exists_book_FN_length_duality
    (q : OriginalClosedGeodesic M)
    (hReference : Unproved.Teichmuller.OriginalFNReferenceContainingGeodesic R g M q) :
    ∃ (inc : OriginalFNCuffIncidence g) (D₀ : OriginalFNRealization M inc)
      (j : Fin (3 * g - 3)) (_hC : D₀.cuff j = q),
      ∀ (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
        (_hBook : Unproved.Teichmuller.OriginalFNBookLeftCopyTransport D₀),
        ∃ (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
          (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
          (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
            (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
            (D : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D)
            (k : Fin (3 * g - 3)),
            φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
              ⟨TeichmullerSpace.mk m, rfl⟩⟩ k = D.phase k)
          (hΘ : ∀ k, Circle.exp ∘ (fun x => Θ x k) = fun x => φ x k),
          (∀ k, Θ (nativeFrickeHomeomorph hA hAlt (basePoint R)) k =
            Complex.arg (φ (nativeFrickeHomeomorph hA hAlt (basePoint R)) k)) ∧
          ∃ left : Fin (3 * g - 3) → Fin 2,
            (∀ k, OriginalFNCopyLeftGerm D₀ k (left k)) ∧
            (∀ (m : MarkedRiemannSurface.{0, 0} R)
              (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
              (D : OriginalFNRealization N inc),
              OriginalFNMarkedTransport D₀ m D →
                ∀ k, OriginalFNCopyLeftGerm D k (left k)) ∧
            ∀ (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
                R hg hgenus hA hAlt D₀ φ Θ)
              (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
                R hg hgenus hA hAlt D₀ φ Θ)
              (_hCompat : Unproved.Teichmuller.OriginalFNNativeSmoothInverse
                R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize)
              (_hRebase : Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
                R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left),
              letI := C
              ∀ (a : T) (z : TangentSpace RI a),
                let v := VectorField.mpullback RI FI
                  (originalFNBookNativeCoordinateMap R hg hgenus hA hAlt D₀ Θ left)
                  (fun y : V => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)) a
                metric a (Complex.I • r a v) (r a z) =
                    mfderiv RI 𝓘(ℝ)
                      (markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus q.toLoop) a z ∧
                  omega a ![v, z] =
                    mfderiv RI 𝓘(ℝ)
                      (markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus q.toLoop) a z := by
  classical
  obtain ⟨inc, D₀, j, hC⟩ := hReference
  refine ⟨inc, D₀, j, hC, ?_⟩
  intro hU hBook
  obtain ⟨φ, Θ, hbase, hΘ, htarget⟩ := exists_originalFNContinuousRealBranch
    R hg hgenus hA hAlt D₀ hU (nativeFrickeHomeomorph hA hAlt (basePoint R))
  have hφ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (transport : OriginalFNMarkedTransport D₀ m D)
      (k : Fin (3 * g - 3)) :
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ k = D.phase k :=
    (congrFun (hΘ k)
      ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩).symm.trans (htarget m N D transport k)
  obtain ⟨left, hleft, hmarked⟩ := hBook
  refine ⟨φ, Θ, hφ, hΘ, hbase, left, hleft, hmarked, ?_⟩
  intro hRigid hRealize hCompat hRebase
  let := C
  let : IsManifold RI ω T :=
    (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth).isManifold_singleton
  dsimp only
  intro a z
  let v : TangentSpace RI a := VectorField.mpullback RI FI
    (originalFNBookNativeCoordinateMap R hg hgenus hA hAlt D₀ Θ left)
    (fun y : V => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)) a
  have hvector : v = originalFNUnitSideSign (left j) • VectorField.mpullback RI FI
      (originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ)
      (fun y : V => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist j)) a := by
    simpa only [v, originalFNBookSideSign, originalFNUnitSideSign] using
      sameOriginalFN_book_twistVector_eq R hp hg hgenus hΓ hfree hsmooth
        hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat left j a
  have hduality := sameOriginalFN_signed_twist_length_duality
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left
      hCompat hRebase a j
  have hOmega : omega a ![v, z] = mfderiv RI 𝓘(ℝ)
      (markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus q.toLoop) a z := by
    rw [hvector, ← hC]
    exact hduality z
  refine ⟨?_, hOmega⟩
  have hmetric : omega a ![v, z] = metric a (Complex.I • r a v) (r a z) := by
    rw [nativeWeilPeterssonRealFundamentalForm_apply]
    exact nativeWeilPeterssonFundamentalForm_eq_realBilinForm
      R hp hg hgenus hΓ hfree hsmooth a (r a v) (r a z)
  exact hmetric.symm.trans hOmega

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
