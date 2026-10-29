module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNReferenceChangePhase
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceChangeDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeCoordinateContinuityProof
public import LowDimensionalTopology.Geometry.Teichmuller.ComplexTopologicalProperties
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Tactic.Linarith

/-!
# One integer branch shift for the same actual deformed reference map

The already proved all-point circle-phase comparison and continuity of the
two prescribed real branches give one global integer for each original cuff.
The actual deformed reference equivalence is fixed throughout the whole
original native space, with the original topology and connectedness.
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


include hfree hsmooth hmark t₀₁ A₁ hφ hφ₁ hΘ hΘ₁ in
/-- For every admissible pair of continuous full real branches, the SAME
actual reference change has one global integer angular shift on each cuff. -/
theorem originalFN_deformed_reference_real_branch_shift :
    letI := C
    letI := C₁
    ∃ n : Fin (3 * g - 3) → ℤ, ∀ (q : T) (j : Fin (3 * g - 3)),
      Θ₁ ⟨finiteFrickeCoordinates hA₁ (Aν q), ⟨Aν q, rfl⟩⟩ j =
        Θ ⟨finiteFrickeCoordinates hA q, ⟨q, rfl⟩⟩ j + (n j : ℝ) * (2 * Real.pi) := by
  classical
  let := C
  let := C₁
  let : PathConnectedSpace T := canonical_pathConnected_of_smoothing
    R hg hgenus hP hΓ hfree hp hsmooth
  let t : T → nativeFrickeImage hA := fun q => ⟨finiteFrickeCoordinates hA q, ⟨q, rfl⟩⟩
  let t₁ : T₁ → nativeFrickeImage hA₁ := fun q =>
    ⟨finiteFrickeCoordinates hA₁ q, ⟨q, rfl⟩⟩
  have hc : Continuous (finiteFrickeCoordinates hA) := by
    change @Continuous T _ (beltramiTopology R) _ (finiteFrickeCoordinates hA)
    rw [beltramiTopology_eq_fromQC_of_smoothing R hg hgenus hP hsmooth]
    exact nativeFrickeCoordinateContinuity R hg hgenus e hA
  have hc₁ : Continuous (finiteFrickeCoordinates hA₁) := by
    change @Continuous T₁ _ (beltramiTopology Y) _ (finiteFrickeCoordinates hA₁)
    rw [beltramiTopology_eq_fromQC_of_smoothing Y hg hY hP hsmooth]
    exact nativeFrickeCoordinateContinuity Y hg hY e₁ hA₁
  have ht : Continuous t := hc.subtype_mk (fun q => mem_range_self q)
  have ht₁ : Continuous t₁ := hc₁.subtype_mk (fun q => mem_range_self q)
  have hAcont : Continuous Aν :=
    (deformedReferenceChangeEquiv_canonical_contMDiff
      R hp hg hgenus hΓ hfree ν hsmooth).continuous
  have hphase (q : T) (j : Fin (3 * g - 3)) : φ (t q) j = φ₁ (t₁ (Aν q)) j :=
    originalFN_circlePhase_referenceChange R hg hgenus mν hY eν
      (deformedTargetMarking_nativeQC R hp hgenus hΓ ν) hmark
      D₀ D₁ t₀₁ hA hA₁ A₁ φ φ₁ hφ hφ₁ q j
  have hshift (j : Fin (3 * g - 3)) :
      ∃ n : ℤ, ∀ q : T,
        Θ₁ (t₁ (Aν q)) j - Θ (t q) j = (n : ℝ) * (2 * Real.pi) := by
    let U : T → ℝ := fun q => Θ₁ (t₁ (Aν q)) j - Θ (t q) j
    have hUc : Continuous U :=
      ((continuous_apply j).comp (Θ₁.continuous.comp (ht₁.comp hAcont))).sub
        ((continuous_apply j).comp (Θ.continuous.comp ht))
    have hUexp (q : T) : Circle.exp (U q) = 1 := by
      change Circle.exp (Θ₁ (t₁ (Aν q)) j - Θ (t q) j) = 1
      have hΘtarget : Circle.exp (Θ₁ (t₁ (Aν q)) j) = φ₁ (t₁ (Aν q)) j :=
        congrFun (hΘ₁ j) (t₁ (Aν q))
      have hΘsource : Circle.exp (Θ (t q) j) = φ (t q) j :=
        congrFun (hΘ j) (t q)
      rw [Circle.exp_sub, hΘtarget, hΘsource, ← hphase q j, div_self']
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp (hUexp (basePoint R))
    refine ⟨n, fun q => ?_⟩
    exact (Circle.isCoveringMap_exp.const_of_comp hUc
      (fun a b => (hUexp a).trans (hUexp b).symm) q (basePoint R)).trans hn
  choose n hn using hshift
  refine ⟨n, fun q j => ?_⟩
  have h := hn j q
  change Θ₁ (t₁ (Aν q)) j = Θ (t q) j + (n j : ℝ) * (2 * Real.pi)
  linarith only [h]

end LowDimensionalTopology.Geometry.Teichmuller
