module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNReferenceRealBranch
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNNativeCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalLengthReferenceChange
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The actual original FN twist shear under its fixed deformed reference map

The same full oriented cuff is transported in its actual marking class.
Its all-point marked length equality and the already derived global integer
angular shift give the true length-rescaled real twist shear.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami TeichmullerSpace
open NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0}) (ν : Ball Γ)

local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "hY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "eν" => deformedTargetMarking R hgenus hΓ hp ν
local notation "Δ" => deformedGroup hΓ ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "Aν" => deformedReferenceChangeEquiv R hp hg hgenus hΓ ν
local notation "hP" => canonicalHandleGroupPresentation g
local notation "T" => TeichmullerSpace R
local notation "T₁" => TeichmullerSpace Y
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "C₁" => canonicalComplexChartedSpace Y hg hY hP hΔ hfY hpY hsmooth

variable
    (F : SmoothSurfaceEquiv R.toRiemannSurface
      (deformedNativeSurface R hgenus hΓ hp ν).toRiemannSurface)
    (hF : PreservesComplexOrientation R.toRiemannAtlas
      (deformedNativeSurface R hgenus hΓ hp ν).toRiemannAtlas F.toHomeomorph)
    (hmark : ContinuousMap.Homotopic (_root_.toContinuousMap F.toHomeomorph)
      (_root_.toContinuousMap (deformedTargetMarking R hgenus hΓ hp ν)))

local notation "mν" =>
  (MarkedRiemannSurface.mk (R := R)
    (carrier := LiZhongQC.ClosedRS.carrier (deformedTargetSource R hgenus hΓ hp ν))
    (topology := LiZhongQC.ClosedRS.topologicalSpace (deformedTargetSource R hgenus hΓ hp ν)) (surface := Y)
    (marking := F)
    (orientation_preserving := hF) : MarkedRiemannSurface R)

variable {e : X ≃ₜ PolygonQuotient g}
    {e₁ : (deformedTargetSource R hgenus hΓ hp ν).carrier ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (D₀ : OriginalFNRealization M inc)
    {N : HyperbolicSurfaceModel (deformedNativeSurface R hgenus hΓ hp ν).toRiemannSurface}
    (D₁ : OriginalFNRealization N inc)
    (t₀₁ : OriginalFNMarkedTransport (R := R) (M := M) (inc := inc) D₀
      (MarkedRiemannSurface.mk (R := R)
        (carrier := LiZhongQC.ClosedRS.carrier (deformedTargetSource R hgenus hΓ hp ν))
        (topology := LiZhongQC.ClosedRS.topologicalSpace (deformedTargetSource R hgenus hΓ hp ν))
        (surface := deformedNativeSurface R hgenus hΓ hp ν)
        (marking := F) (orientation_preserving := hF) : MarkedRiemannSurface R)
      (N := N) D₁)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hA₁ : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable
      (deformedNativeSurface R hgenus hΓ hp ν) hg e₁)
    (A₁ : OriginalFNGeometricFamily hA₁ D₁)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (φ₁ : C(nativeFrickeImage hA₁, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (Θ₁ : C(nativeFrickeImage hA₁, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (k : MarkedRiemannSurface.{0, 0} R)
      (P : HyperbolicSurfaceModel k.surface.toRiemannSurface)
      (D : OriginalFNRealization P inc) (_t : OriginalFNMarkedTransport D₀ k D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk k),
        ⟨TeichmullerSpace.mk k, rfl⟩⟩ j = D.phase j)
    (hφ₁ : ∀ (k : MarkedRiemannSurface.{0, 0} (deformedNativeSurface R hgenus hΓ hp ν))
      (P : HyperbolicSurfaceModel k.surface.toRiemannSurface)
      (D : OriginalFNRealization P inc) (_t : OriginalFNMarkedTransport D₁ k D)
      (j : Fin (3 * g - 3)),
      φ₁ ⟨finiteFrickeCoordinates hA₁ (TeichmullerSpace.mk k),
        ⟨TeichmullerSpace.mk k, rfl⟩⟩ j = D.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hΘ₁ : ∀ j, Circle.exp ∘ (fun t => Θ₁ t j) = fun t => φ₁ t j)

private theorem actualMarkedLength_freeClass_congr
    {Z : Type} [TopologicalSpace Z] (S : ClosedRiemannSurface Z)
    (hS : S.HasGenus g) {α β : LiZhongQC.Loop Z}
    (h : LiZhongQC.FreelyHomotopic α β) (q : TeichmullerSpace S) :
    markedGeodesicLength S (Nat.succ_le_of_lt hg) hS α q =
      markedGeodesicLength S (Nat.succ_le_of_lt hg) hS β q := by
  refine Quotient.inductionOn q ?_
  intro k
  exact congrArg ENNReal.toReal (LiZhongQC.s30b_fhl_congr _
    (LiZhongQC.s30b_fh_map k.markingMap.continuous h))

include hmark t₀₁ in
/-- The same complete oriented original cuff has equal actual marked length
at every point under the fixed actual deformed reference change. -/
theorem originalFN_deformed_reference_cuff_length (q : T) (j : Fin (3 * g - 3)) :
    markedGeodesicLength Y (Nat.succ_le_of_lt hg) hY (D₁.cuff j).toLoop (Aν q) =
      markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus (D₀.cuff j).toLoop q := by
  let α := (D₀.cuff j).toLoop
  let αY : LiZhongQC.Loop (deformedTargetSource R hgenus hΓ hp ν).carrier :=
    ⟨eν α.1, α.2.map (eν).continuous⟩
  have hclass : LiZhongQC.FreelyHomotopic αY (D₁.cuff j).toLoop :=
    LiZhongQC.s30b_fh_trans
      (LiZhongQC.s30b_fh_symm (LiZhongQC.s30b_fh_of_homotopic hmark α))
      (t₀₁.cuff_orientation j)
  calc
    markedGeodesicLength Y (Nat.succ_le_of_lt hg) hY (D₁.cuff j).toLoop (Aν q) =
        markedGeodesicLength Y (Nat.succ_le_of_lt hg) hY αY (Aν q) :=
      (actualMarkedLength_freeClass_congr hg Y hY hclass (Aν q)).symm
    _ = markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α q :=
      markedGeodesicLength_referenceChangeEquiv R Y hg hgenus hY eν
        (deformedTargetMarking_nativeQC R hp hgenus hΓ ν) α q

variable
    (hAlt : ∀ k : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA k))
    (hAlt₁ : ∀ k : MarkedRiemannSurface.{0, 0}
      (deformedNativeSurface R hgenus hΓ hp ν),
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA₁ k))

local notation "FN" => originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
local notation "FN₁" => originalFNNativeRescaledCoordinateMap Y hg hY hA₁ hAlt₁ D₁ Θ₁

include hfree hsmooth hmark t₀₁ A₁ hφ hφ₁ hΘ hΘ₁ in
/-- Actual length equality rescales the DERIVED global integer angle shift
to the same full real FN twist shear at every original native marked point. -/
theorem originalFN_deformed_reference_native_twist_shear :
    letI := C
    letI := C₁
    ∃ n : Fin (3 * g - 3) → ℤ, ∀ q : T,
      (FN₁ (Aν q)).1 = (FN q).1 ∧
      ∀ j, (FN₁ (Aν q)).2 j = (FN q).2 j + (n j : ℝ) * (FN q).1 j := by
  let := C
  let := C₁
  obtain ⟨n, hn⟩ := originalFN_deformed_reference_real_branch_shift
    R hp hg hgenus hΓ hfree hsmooth ν F hF hmark
      D₀ D₁ t₀₁ hA hA₁ A₁ φ φ₁ Θ Θ₁ hφ hφ₁ hΘ hΘ₁
  let t : T → nativeFrickeImage hA := fun q => ⟨finiteFrickeCoordinates hA q, ⟨q, rfl⟩⟩
  let t₁ : T₁ → nativeFrickeImage hA₁ := fun q =>
    ⟨finiteFrickeCoordinates hA₁ q, ⟨q, rfl⟩⟩
  have hlength (q : T) (j : Fin (3 * g - 3)) : (FN₁ (Aν q)).1 j = (FN q).1 j :=
    originalFN_deformed_reference_cuff_length
      R hp hg hgenus hΓ ν F hF hmark D₀ D₁ t₀₁ q j
  have htwist (q : T) (j : Fin (3 * g - 3)) :
      (FN q).2 j = (FN q).1 j / (2 * Real.pi) * Θ (t q) j := by
    have h := congrArg (fun z : (Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ) => z.1 j)
      (originalFNNativeRescaledCoordinateMap_eq_original R hg hgenus hA hAlt D₀ Θ q)
    change (((originalFNRealCoordinateMap R hg hgenus hA hAlt D₀ Θ (t q)).1 j : ℝ) /
      (2 * Real.pi)) * Θ (t q) j = (FN q).1 j / (2 * Real.pi) * Θ (t q) j
    exact congrArg (fun x : ℝ => x / (2 * Real.pi) * Θ (t q) j) h.symm
  have htwist₁ (q : T₁) (j : Fin (3 * g - 3)) :
      (FN₁ q).2 j = (FN₁ q).1 j / (2 * Real.pi) * Θ₁ (t₁ q) j := by
    have h := congrArg (fun z : (Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ) => z.1 j)
      (originalFNNativeRescaledCoordinateMap_eq_original Y hg hY hA₁ hAlt₁ D₁ Θ₁ q)
    change (((originalFNRealCoordinateMap Y hg hY hA₁ hAlt₁ D₁ Θ₁ (t₁ q)).1 j : ℝ) /
      (2 * Real.pi)) * Θ₁ (t₁ q) j = (FN₁ q).1 j / (2 * Real.pi) * Θ₁ (t₁ q) j
    exact congrArg (fun x : ℝ => x / (2 * Real.pi) * Θ₁ (t₁ q) j) h.symm
  refine ⟨n, fun q => ⟨funext (hlength q), fun j => ?_⟩⟩
  rw [htwist₁, htwist, hlength]
  have hangle : Θ₁ (t₁ (Aν q)) j = Θ (t q) j + (n j : ℝ) * (2 * Real.pi) := hn q j
  rw [hangle]
  field_simp [Real.pi_ne_zero]

end LowDimensionalTopology.Geometry.Teichmuller
