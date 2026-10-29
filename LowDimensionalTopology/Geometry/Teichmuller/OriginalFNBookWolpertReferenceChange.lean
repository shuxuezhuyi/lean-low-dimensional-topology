module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookWolpert
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceWPAllPoints
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookLeftReferenceTransport
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNReferenceCovectors
public import Mathlib.Tactic.Ring

/-!
# Wolpert's actual book formula across one matching original reference

The target theorem is produced by the compatible-reflection book proof on
its actual deformed reference. The actual ordered cuff transport retains
one fixed geometric left label. The fixed-reference WP law and actual FN
covector shear then return the complete English-normalized formula on the
original reference, with its actual native tangent vectors.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff BigOperators

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

variable
    (hAlt : ∀ k : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA k))
    (hAlt₁ : ∀ k : MarkedRiemannSurface.{0, 0}
      (deformedNativeSurface R hgenus hΓ hp ν),
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA₁ k))

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "FNModel" => (I → ℝ) × (I → ℝ)
local notation "RI" => 𝓘(ℝ, E)
local notation "FI" => 𝓘(ℝ, FNModel)

variable
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (hU₁ : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic
      (deformedNativeSurface R hgenus hΓ hp ν) hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) hA₁ hAlt₁ D₁)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRigid₁ : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      (deformedNativeSurface R hgenus hΓ hp ν) hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) hA₁ hAlt₁ D₁ φ₁ Θ₁)
    (hRealize₁ : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      (deformedNativeSurface R hgenus hΓ hp ν) hg
      (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) hA₁ hAlt₁ D₁ φ₁ Θ₁)
    (hBook : Unproved.Teichmuller.OriginalFNBookLeftCopyTransport D₀)

local notation "left" => Classical.choose hBook
local notation "Nbook" => originalFNBookNativeCoordinateMap R hg hgenus hA hAlt D₀ Θ left
local notation "Nbook₁" => originalFNBookNativeCoordinateMap Y hg hY hA₁ hAlt₁ D₁ Θ₁ left
local notation "Compat" => Unproved.Teichmuller.OriginalFNNativeSmoothInverse
  R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
local notation "Compat₁" => Unproved.Teichmuller.OriginalFNNativeSmoothInverse
  Y hpY hg hY hΔ hfY hsmooth hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁
local notation "omega" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "omega₁" => nativeWeilPeterssonRealFundamentalForm
  Y hpY hg hY hΔ hfY hsmooth
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "D₁t" => nativeWeilPeterssonRealTangentCoordinateEquiv
  Y hpY hg hY hΔ hfY hsmooth
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "f" => deformedReferenceWeilPeterssonCoordinateMap R hp hg hgenus hΓ ν
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  («I» := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth)
local notation "realManifold₁" => Topology.IsOpenEmbedding.isManifold_singleton
  («I» := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding Y hg hY hP hΔ hfY hpY hsmooth)


local notation "sigma₁" => sameOriginalFNUnitCurve Y hg hY hA₁ hAlt₁ D₁
  hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁
local notation "W₁" => sameOriginalFNSignedTwistField Y hpY hg hY hΔ hfY hsmooth
  hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁


include hmark t₀₁ in
/-- The actual compatible target's produced formula, actual WP reference
pullback and derived cuff shear give Wolpert on the original reference.
The target geometric family is extracted from its existing phase input. -/
theorem originalFN_book_Wolpert_via_matching_deformed_reference
    (hCompat : Unproved.Teichmuller.OriginalFNNativeSmoothInverse
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize)
    (hCompat₁ : Unproved.Teichmuller.OriginalFNNativeSmoothInverse
      Y hpY hg hY hΔ hfY hsmooth hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁)
    (hRebase₁ : Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
      Y hpY hg hY hΔ hfY hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ left)
    (J : (deformedTargetSource R hgenus hΓ hp ν).carrier ≃ₜ
      (deformedTargetSource R hgenus hΓ hp ν).carrier)
    (hJ : @LiZhongQC.IsAnticonformalInvolution
      (deformedTargetSource R hgenus hΓ hp ν).carrier inferInstance
      (Y).toRiemannAtlas.toChartedSpace J)
    (hJcuffs : ∀ j, J '' range (D₁.cuff j).curve = range (D₁.cuff j).curve)
    (hJpants : ∀ a, J '' (D₁.component a).val = (D₁.component a).val)
    (hGeom₁ : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
      Y hg hY hA₁ hAlt₁ D₁ J hJ hJcuffs hJpants)
    (hWPReflection₁ : Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
      Y hpY hg hY hΔ J hJ hsmooth)
    (hWPForm₁ : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      Y hpY hg hY hΔ hfY hsmooth)
    (hFrickeBers₁ : Unproved.Teichmuller.NativeFrickeBersRealAnalyticCompatibility
      Y hg hY hΔ hfY hpY hsmooth hA₁)
    (hvariation₁ : ∀ μ : Ball Δ,
      Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
        (deformedNativeSurface Y hY hΔ hpY μ)
        (deformedNativeSurface_uniformization Y hY hΔ hpY μ) hg
        (deformedNativeSurface_hasGenus Y hY hΔ hpY μ)
        (deformedGroup_spec hΔ μ).1
        (deformedNativeSurface_actsFreely Y hY hΔ hpY μ) hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})

    (hCartan₁ : letI := C₁
      letI : IsManifold RI ω T₁ := realManifold₁
      ∀ (k : I) (U V : FormInterior.SmoothVectorField RI (M := T₁)),
        let data := sameOriginalFN_unitCurve_localFlowData
          Y hpY hg hY hΔ hfY hsmooth hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁
            hCompat₁ k (left k)
        Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
          Y hpY hg hY hΔ hfY hsmooth hWPForm₁ ⊤ 1 (by norm_num)
          (fun t a => sameOriginalFNUnitCurve Y hg hY hA₁ hAlt₁ D₁
            hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ a k (left k) t)
          (sameOriginalFNSignedTwistField Y hpY hg hY hΔ hfY hsmooth
            hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ hCompat₁ k (left k)) U V
          data.1 data.2.1 data.2.2.1 data.2.2.2) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    letI := C₁
    letI : IsManifold RI ω T := realManifold
    letI : IsManifold RI ω T₁ := realManifold₁
    ∀ (q : T) (v w : TangentSpace RI q),
      omega q ![v, w] = ∑ j,
        ((mvfderiv RI Nbook q v).2 j * (mvfderiv RI Nbook q w).1 j -
          (mvfderiv RI Nbook q v).1 j * (mvfderiv RI Nbook q w).2 j) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := C
  let := C₁
  let : IsManifold RI ω T := realManifold
  let : IsManifold RI ω T₁ := realManifold₁
  have hLeft := originalFN_same_bookLeft_under_reference_transport D₀ mν D₁ t₀₁ hBook
  have hTarget := sameOriginalFN_book_core_for_left
    Y hpY hg hY hΔ hsmooth hA₁ hAlt₁ D₁ J hJ hJcuffs hJpants
    hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ left
    hWPForm₁ hFrickeBers₁ hvariation₁ hjets hCompat₁ hRebase₁ hGeom₁ hWPReflection₁ hCartan₁ hLeft
  obtain ⟨n, hn⟩ := exists_originalFN_deformed_reference_book_covector_shear
    R hp hg hgenus hΓ hfree hsmooth ν F hF hmark D₀ D₁ t₀₁ hA hA₁
    φ φ₁ Θ Θ₁ hφ hφ₁ hΘ hΘ₁ hAlt hAlt₁
    hU hU₁ hRigid hRigid₁ hRealize hRealize₁ hCompat hCompat₁ hBook
  intro q v w
  let P : TangentSpace RI q → TangentSpace RI (Aν q) :=
    fun z => (D₁t (Aν q)).symm (fderiv ℝ f (BC q) (D q z))
  calc
    omega q ![v, w] = omega₁ (Aν q) ![P v, P w] := by
      simpa only [P] using
        nativeWeilPeterssonRealForm_deformedReference_allPoints_coordinates
          R hp hg hgenus hΓ hfree hsmooth ν q v w
    _ = ∑ j,
        ((mvfderiv RI Nbook₁ (Aν q) (P v)).2 j *
            (mvfderiv RI Nbook₁ (Aν q) (P w)).1 j -
          (mvfderiv RI Nbook₁ (Aν q) (P v)).1 j *
            (mvfderiv RI Nbook₁ (Aν q) (P w)).2 j) :=
      hTarget.2.2.2.1 (Aν q) (P v) (P w)
    _ = ∑ j,
        ((mvfderiv RI Nbook q v).2 j * (mvfderiv RI Nbook q w).1 j -
          (mvfderiv RI Nbook q v).1 j * (mvfderiv RI Nbook q w).2 j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [P, (hn q v).1, (hn q w).1,
        (hn q v).2 j, (hn q w).2 j]
      ring

local notation "b" => (fun a : I ⊕ I => match a with
  | Sum.inl j => (Pi.single j (1 : ℝ), (0 : I → ℝ))
  | Sum.inr j => ((0 : I → ℝ), Pi.single j (1 : ℝ)))
local notation "L" => (fun (j : I) (q : T) => VectorField.mpullback RI FI Nbook
  (fun y : FNModel =>
    (ContinuousLinearEquiv.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) y)) (b (Sum.inl j))) q)

include hmark t₀₁ in
/-- The English corollary for each SAME actual cuff of the compatible
decomposition on the original reference: its actual book length pullback
contracts to minus the differential of its actual book twist coordinate. -/
theorem originalFN_book_length_contraction_via_matching_deformed_reference
    (hCompat : Unproved.Teichmuller.OriginalFNNativeSmoothInverse
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize)
    (hCompat₁ : Unproved.Teichmuller.OriginalFNNativeSmoothInverse
      Y hpY hg hY hΔ hfY hsmooth hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁)
    (hRebase₁ : Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
      Y hpY hg hY hΔ hfY hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ left)
    (J : (deformedTargetSource R hgenus hΓ hp ν).carrier ≃ₜ
      (deformedTargetSource R hgenus hΓ hp ν).carrier)
    (hJ : @LiZhongQC.IsAnticonformalInvolution
      (deformedTargetSource R hgenus hΓ hp ν).carrier inferInstance
      (Y).toRiemannAtlas.toChartedSpace J)
    (hJcuffs : ∀ j, J '' range (D₁.cuff j).curve = range (D₁.cuff j).curve)
    (hJpants : ∀ a, J '' (D₁.component a).val = (D₁.component a).val)
    (hGeom₁ : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
      Y hg hY hA₁ hAlt₁ D₁ J hJ hJcuffs hJpants)
    (hWPReflection₁ : Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
      Y hpY hg hY hΔ J hJ hsmooth)
    (hWPForm₁ : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      Y hpY hg hY hΔ hfY hsmooth)
    (hFrickeBers₁ : Unproved.Teichmuller.NativeFrickeBersRealAnalyticCompatibility
      Y hg hY hΔ hfY hpY hsmooth hA₁)
    (hvariation₁ : ∀ μ : Ball Δ,
      Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
        (deformedNativeSurface Y hY hΔ hpY μ)
        (deformedNativeSurface_uniformization Y hY hΔ hpY μ) hg
        (deformedNativeSurface_hasGenus Y hY hΔ hpY μ)
        (deformedGroup_spec hΔ μ).1
        (deformedNativeSurface_actsFreely Y hY hΔ hpY μ) hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})

    (hCartan₁ : letI := C₁
      letI : IsManifold RI ω T₁ := realManifold₁
      ∀ (k : I) (U V : FormInterior.SmoothVectorField RI (M := T₁)),
        let data := sameOriginalFN_unitCurve_localFlowData
          Y hpY hg hY hΔ hfY hsmooth hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁
            hCompat₁ k (left k)
        Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
          Y hpY hg hY hΔ hfY hsmooth hWPForm₁ ⊤ 1 (by norm_num)
          (fun t a => sameOriginalFNUnitCurve Y hg hY hA₁ hAlt₁ D₁
            hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ a k (left k) t)
          (sameOriginalFNSignedTwistField Y hpY hg hY hΔ hfY hsmooth
            hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ hCompat₁ k (left k)) U V
          data.1 data.2.1 data.2.2.1 data.2.2.2) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    letI := C₁
    letI : IsManifold RI ω T := realManifold
    letI : IsManifold RI ω T₁ := realManifold₁
    ∀ (q : T) (j : I) (z : TangentSpace RI q),
      omega q ![L j q, z] =
        -mfderiv RI 𝓘(ℝ) (fun a : T => (Nbook a).2 j) q z := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := C
  let := C₁
  let : IsManifold RI ω T := realManifold
  let : IsManifold RI ω T₁ := realManifold₁
  have hWolpert := originalFN_book_Wolpert_via_matching_deformed_reference
    R hp hg hgenus hΓ hfree hsmooth ν F hF hmark D₀ D₁ t₀₁ hA hA₁
    φ φ₁ Θ Θ₁ hφ hφ₁ hΘ hΘ₁ hAlt hAlt₁ hU hU₁ hRigid hRealize hRigid₁ hRealize₁ hBook
    hCompat hCompat₁ hRebase₁ J hJ hJcuffs hJpants hGeom₁ hWPReflection₁
    hWPForm₁ hFrickeBers₁ hvariation₁ hjets hCartan₁
  have hbook := sameOriginalFN_book_tangent_expansion
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat left
  let P (j : I) : FNModel →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.snd ℝ (I → ℝ) (I → ℝ))
  have htauDeriv (q : T) (j : I) (z : TangentSpace RI q) :
      mfderiv RI 𝓘(ℝ) (fun a : T => (Nbook a).2 j) q z =
        (mvfderiv RI Nbook q z).2 j := by
    change mvfderiv RI ((P j : FNModel → ℝ) ∘ Nbook) q z = P j (mvfderiv RI Nbook q z)
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

end LowDimensionalTopology.Geometry.Teichmuller
