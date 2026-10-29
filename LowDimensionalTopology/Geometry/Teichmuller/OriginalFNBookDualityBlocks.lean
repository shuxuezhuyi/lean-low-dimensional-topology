module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookTangentExpansion
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonSmoothForm
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# The actual book TL and TT blocks from the internal length-duality output

The internal input is the preceding theorem's actual all-point length duality
on the literal book twist fields. It must be supplied by the physical-curve
producer in the final assembly; no new Unproved input is installed. The same
marked length is the first component of the actual book map, whose genuine
native inverse supplies its unit length and twist pullbacks.
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
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
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
local notation "omega" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "length" => (fun j : I =>
  markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus (OriginalClosedGeodesic.toLoop (D₀.cuff j)))

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

local notation "Nbook" => originalFNBookNativeCoordinateMap R hg hgenus hA hAlt D₀ Θ left
local notation "Compat" => Unproved.Teichmuller.OriginalFNNativeSmoothInverse
  R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
local notation "unitLength" => (fun j : I => (Pi.single (M := fun _ => ℝ) j (1 : ℝ), (0 : I → ℝ)))
local notation "unitTwist" => (fun j : I => ((0 : I → ℝ), Pi.single (M := fun _ => ℝ) j (1 : ℝ)))
local notation "L" => (fun (j : I) (a : T) => VectorField.mpullback RI FI Nbook
  (fun y : F => (ContinuousLinearEquiv.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) y)) (unitLength j)) a)
local notation "V" => (fun (j : I) (a : T) => VectorField.mpullback RI FI Nbook
  (fun y : F => (ContinuousLinearEquiv.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) y)) (unitTwist j)) a)

include left in
/-- Internal length duality gives coefficient+1 on actual book twist/length
units and coefficient0 on actual book twist/twist units. -/
theorem sameOriginalFN_book_twist_blocks_of_length_duality (hCompat : Compat)
    (hDual : letI := C
      ∀ (a : T) (j : I) (z : TangentSpace RI a),
        omega a ![V j a, z] = mfderiv RI 𝓘(ℝ) (length j) a z) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (a : T) (j k : I),
      omega a ![V j a, L k a] = (if j = k then 1 else 0) ∧
        omega a ![V j a, V k a] = 0 := by
  classical
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only at hDual ⊢
  have hbook := sameOriginalFN_book_tangent_expansion
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat left
  let P (j : I) : F →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.fst ℝ (I → ℝ) (I → ℝ))
  have hlength (j : I) : length j = (P j : F → ℝ) ∘ Nbook := by
    funext a
    rfl
  have hlengthDeriv (a : T) (j : I) (z : TangentSpace RI a) :
      mfderiv RI 𝓘(ℝ) (length j) a z = (mvfderiv RI Nbook a z).1 j := by
    change mvfderiv RI (length j) a z = P j (mvfderiv RI Nbook a z)
    rw [hlength j]
    have h := mvfderiv_comp a (P j).differentiableAt.mdifferentiableAt
      ((hbook.1 a).mdifferentiableAt (by simp))
    rw [mvfderiv_eq_fderiv, (P j).hasFDerivAt.fderiv] at h
    simpa only [mvfderiv, ContinuousLinearMap.comp_apply] using
      congrArg (fun A : TangentSpace RI a →L[ℝ] ℝ => A z) h
  have hunit (a : T) (y : F) : mvfderiv RI Nbook a
      (VectorField.mpullback RI FI Nbook
        (fun t : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm y) a) = y := by
    change (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook a))
      (mfderiv RI FI Nbook a ((mfderiv RI FI Nbook a).inverse
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook a)).symm y))) = y
    rw [(hbook.2.1 a).self_apply_inverse]
    exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Nbook a)).apply_symm_apply y
  intro a j k
  constructor
  · rw [hDual a j, hlengthDeriv, hunit a (unitLength k)]
    change (Pi.single (M := fun _ => ℝ) k (1 : ℝ)) j = if j = k then 1 else 0
    by_cases h : j = k
    · subst j
      simp only [Pi.single_eq_same, ite_true]
    · simp only [Pi.single_eq_of_ne h, ite_eq_right h]
  · rw [hDual a j, hlengthDeriv, hunit a (unitTwist k)]
    rfl

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
