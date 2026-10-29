module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalGeodesicFNLengthDuality
public import LowDimensionalTopology.Geometry.Teichmuller.WolpertLengthReciprocity

/-!
# Cross-length reciprocity for two prescribed original geodesics

The two geodesics may use independent actual FN references and real branches.
Their literal book unit-twist fields lie in the same native tangent fibre.
The established full-length duality identities and alternation give their
cross-length reciprocity, with the physical unit-speed normalization.
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
local notation "unitTwist" => (fun j : Fin (3 * g - 3) =>
  ((0 : Fin (3 * g - 3) → ℝ), Pi.single (M := fun _ => ℝ) j (1 : ℝ)))
local notation "lengthOf" => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus

/-- Two prescribed original full geodesics have independent admissible FN
references and coherent book sides. The cross-length variations of their
actual physical unit-twist fields are opposite at every original point. -/
theorem originalGeodesics_exists_book_FN_cross_length_reciprocity
    (q : Fin 2 → OriginalClosedGeodesic M)
    (hReference : ∀ i, Unproved.Teichmuller.OriginalFNReferenceContainingGeodesic R g M (q i)) :
    ∃ (inc : Fin 2 → OriginalFNCuffIncidence g)
      (D₀ : ∀ i, OriginalFNRealization M (inc i))
      (j : Fin 2 → Fin (3 * g - 3)) (_hC : ∀ i, (D₀ i).cuff (j i) = q i),
      ∀ (hU : ∀ i, Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic
          R hg hgenus hA hAlt (D₀ i))
        (_hBook : ∀ i, Unproved.Teichmuller.OriginalFNBookLeftCopyTransport (D₀ i)),
        ∃ (φ : Fin 2 → C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
          (Θ : Fin 2 → C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
          (hφ : ∀ (i : Fin 2) (m : MarkedRiemannSurface.{0, 0} R)
            (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
            (D : OriginalFNRealization N (inc i))
            (_transport : OriginalFNMarkedTransport (D₀ i) m D) (k : Fin (3 * g - 3)),
            φ i ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
              ⟨TeichmullerSpace.mk m, rfl⟩⟩ k = D.phase k)
          (hΘ : ∀ i k, Circle.exp ∘ (fun x => Θ i x k) = fun x => φ i x k),
          (∀ i k, Θ i (nativeFrickeHomeomorph hA hAlt (basePoint R)) k =
            Complex.arg (φ i (nativeFrickeHomeomorph hA hAlt (basePoint R)) k)) ∧
          ∃ left : Fin 2 → Fin (3 * g - 3) → Fin 2,
            (∀ i k, OriginalFNCopyLeftGerm (D₀ i) k (left i k)) ∧
            (∀ (i : Fin 2) (m : MarkedRiemannSurface.{0, 0} R)
              (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
              (D : OriginalFNRealization N (inc i)),
              OriginalFNMarkedTransport (D₀ i) m D →
                ∀ k, OriginalFNCopyLeftGerm D k (left i k)) ∧
            ∀ (hRigid : ∀ i, Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
                R hg hgenus hA hAlt (D₀ i) (φ i) (Θ i))
              (hRealize : ∀ i, Unproved.Teichmuller.OriginalFNMarkedGluingRealization
                R hg hgenus hA hAlt (D₀ i) (φ i) (Θ i))
              (_hCompat : ∀ i, Unproved.Teichmuller.OriginalFNNativeSmoothInverse
                R hp hg hgenus hΓ hfree hsmooth hA hAlt (D₀ i) (hU i)
                  (φ i) (Θ i) (hφ i) (hΘ i) (hRigid i) (hRealize i))
              (_hRebase : ∀ i, Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
                R hp hg hgenus hΓ hfree hA hAlt (D₀ i) (hU i)
                  (φ i) (Θ i) (hφ i) (hΘ i) (hRigid i) (hRealize i) (left i)),
              letI := C
              ∀ a : T,
                let v := fun i : Fin 2 => VectorField.mpullback RI FI
                  (originalFNBookNativeCoordinateMap R hg hgenus hA hAlt (D₀ i) (Θ i) (left i))
                  (fun y : V => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist (j i))) a
                mfderiv RI 𝓘(ℝ) (lengthOf (q 1).toLoop) a (v 0) =
                  -mfderiv RI 𝓘(ℝ) (lengthOf (q 0).toLoop) a (v 1) := by
  classical
  choose inc D₀ j hC hdata using (fun i : Fin 2 =>
    originalGeodesic_exists_book_FN_length_duality
      R hp hg hgenus hΓ hfree hsmooth hA hAlt (q i) (hReference i))
  refine ⟨inc, D₀, j, hC, ?_⟩
  intro hU hBook
  choose φ Θ hφ hΘ hbase left hleft hmarked hduality using
    (fun i : Fin 2 => hdata i (hU i) (hBook i))
  refine ⟨φ, Θ, hφ, hΘ, hbase, left, hleft, hmarked, ?_⟩
  intro hRigid hRealize hCompat hRebase
  let := C
  dsimp only
  intro a
  let v : Fin 2 → TangentSpace RI a := fun i => VectorField.mpullback RI FI
    (originalFNBookNativeCoordinateMap R hg hgenus hA hAlt (D₀ i) (Θ i) (left i))
    (fun y : V => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (unitTwist (j i))) a
  have hdual (i : Fin 2) :
      Unproved.Teichmuller.WolpertLengthDualityAt
        R hp hg hgenus hΓ hfree hsmooth a (q i).toLoop (v i) := by
    intro z
    exact (hduality i (hRigid i) (hRealize i) (hCompat i) (hRebase i) a z).2
  exact nativeMarkedLengthReciprocity_of_wolpertDuality
    R hp hg hgenus hΓ hfree hsmooth a (q 0).toLoop (q 1).toLoop
      (v 0) (v 1) (hdual 0) (hdual 1)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
