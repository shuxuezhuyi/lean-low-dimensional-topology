module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookWolpertReferenceChange
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNCompatibleDeformedSymmetricReference

/-!
# The actual matching symmetric reference in the original book formula

The pictured-reference geometry selects one actual deformed target with
the same complete ordered pants transport. Each remaining analysis input
is the existing concrete predicate on that selected target. The actual
reference-change consumer then proves the original formula and contraction.
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
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (D₀ : OriginalFNRealization M inc)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc) (_t : OriginalFNMarkedTransport D₀ m D)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun x => Θ x j) = fun x => φ x j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)
    (hBook : Unproved.Teichmuller.OriginalFNBookLeftCopyTransport D₀)
    (hCompat : Unproved.Teichmuller.OriginalFNNativeSmoothInverse
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize)

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "V" => (I → ℝ) × (I → ℝ)
local notation "RI" => 𝓘(ℝ, E)
local notation "FI" => 𝓘(ℝ, V)
local notation "T" => TeichmullerSpace R
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  («I» := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth)
local notation "left" => Classical.choose hBook
local notation "Nbook" => originalFNBookNativeCoordinateMap R hg hgenus hA hAlt D₀ Θ left
local notation "omega" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "unitLength" => (fun j : I => (Pi.single (M := fun _ => ℝ) j (1 : ℝ), (0 : I → ℝ)))
local notation "L" => (fun (j : I) (q : T) => VectorField.mpullback RI FI Nbook
  (fun y : V => (ContinuousLinearEquiv.symm (NormedSpace.fromTangentSpace (𝕜 := ℝ) y)) (unitLength j)) q)

include hCompat in
/-- The geometric source selects the actual matching target before the
existing concrete target analysis predicates are supplied. The conclusions
are the original-reference English formula and its same-cuff contraction. -/
theorem exists_originalFN_book_formula_from_symmetric_reference
    (hSym : Unproved.Teichmuller.OriginalFNCompatibleDeformedSymmetricReference
      R hp hg hgenus hΓ D₀) :
    ∃ ν : Ball Γ,
      let Yν := deformedNativeSurface R hgenus hΓ hp ν
      let hYν := deformedNativeSurface_hasGenus R hgenus hΓ hp ν
      let eν := deformedTargetMarking R hgenus hΓ hp ν
      let hpYν := deformedNativeSurface_uniformization R hgenus hΓ hp ν
      let Δν := deformedGroup hΓ ν
      let hΔν := (deformedGroup_spec hΓ ν).1
      let hfYν := deformedNativeSurface_actsFreely R hgenus hΓ hp ν
      let Tν := TeichmullerSpace Yν
      let Cν := canonicalComplexChartedSpace Yν hg hYν hP hΔν hfYν hpYν hsmooth
      let realν := Topology.IsOpenEmbedding.isManifold_singleton («I» := RI) (n := ω)
        (canonicalBersCoordinates_isOpenEmbedding Yν hg hYν hP hΔν hfYν hpYν hsmooth)
      ∃ (F : SmoothSurfaceEquiv R.toRiemannSurface Yν.toRiemannSurface)
        (hF : PreservesComplexOrientation R.toRiemannAtlas Yν.toRiemannAtlas F.toHomeomorph)
        (_hmark : ContinuousMap.Homotopic (_root_.toContinuousMap F.toHomeomorph)
          (_root_.toContinuousMap eν)),
        let mν : MarkedRiemannSurface.{0, 0} R :=
          { carrier := (deformedTargetSource R hgenus hΓ hp ν).carrier
            topology := inferInstance
            surface := Yν
            marking := F
            orientation_preserving := hF }
        ∃ (N : HyperbolicSurfaceModel Yν.toRiemannSurface)
          (D₁ : OriginalFNRealization N inc)
          (_t₀₁ : OriginalFNMarkedTransport D₀ mν D₁)
          (J : (deformedTargetSource R hgenus hΓ hp ν).carrier ≃ₜ
            (deformedTargetSource R hgenus hΓ hp ν).carrier)
          (hJ : @LiZhongQC.IsAnticonformalInvolution
            (deformedTargetSource R hgenus hΓ hp ν).carrier inferInstance
            Yν.toRiemannAtlas.toChartedSpace J)
          (hJcuffs : ∀ j, J '' range (D₁.cuff j).curve = range (D₁.cuff j).curve)
          (hJpants : ∀ a, J '' (D₁.component a).val = (D₁.component a).val),
          ∀ {e₁ : (deformedTargetSource R hgenus hΓ hp ν).carrier ≃ₜ PolygonQuotient g}
            (hA₁ : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable Yν hg e₁)
            (hAlt₁ : ∀ m : MarkedRiemannSurface.{0, 0} Yν,
              Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA₁ m))
            (hU₁ : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic Yν hg hYν hA₁ hAlt₁ D₁)
            (φ₁ : C(nativeFrickeImage hA₁, I → Circle))
            (Θ₁ : C(nativeFrickeImage hA₁, I → ℝ))
            (hφ₁ : ∀ (m : MarkedRiemannSurface.{0, 0} Yν)
              (P : HyperbolicSurfaceModel m.surface.toRiemannSurface)
              (D : OriginalFNRealization P inc) (_t : OriginalFNMarkedTransport D₁ m D)
              (j : I),
              φ₁ ⟨finiteFrickeCoordinates hA₁ (TeichmullerSpace.mk m),
                ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
            (hΘ₁ : ∀ j, Circle.exp ∘ (fun x => Θ₁ x j) = fun x => φ₁ x j)
            (hRigid₁ : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
              Yν hg hYν hA₁ hAlt₁ D₁ φ₁ Θ₁)
            (hRealize₁ : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
              Yν hg hYν hA₁ hAlt₁ D₁ φ₁ Θ₁)
            (hCompat₁ : Unproved.Teichmuller.OriginalFNNativeSmoothInverse
              Yν hpYν hg hYν hΔν hfYν hsmooth hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁)
            (_hRebase₁ : Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
              Yν hpYν hg hYν hΔν hfYν hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ left)
            (_hGeom₁ : Unproved.Teichmuller.OriginalFNMarkedReflectionPhaseGeometry
              Yν hg hYν hA₁ hAlt₁ D₁ J hJ hJcuffs hJpants)
            (_hWPReflection₁ : Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
              Yν hpYν hg hYν hΔν J hJ hsmooth)
            (hWPForm₁ : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
              Yν hpYν hg hYν hΔν hfYν hsmooth)
            (_hFrickeBers₁ : Unproved.Teichmuller.NativeFrickeBersRealAnalyticCompatibility
              Yν hg hYν hΔν hfYν hpYν hsmooth hA₁)
            (_hvariation₁ : ∀ μ : Ball Δν,
              Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
                (deformedNativeSurface Yν hYν hΔν hpYν μ)
                (deformedNativeSurface_uniformization Yν hYν hΔν hpYν μ) hg
                (deformedNativeSurface_hasGenus Yν hYν hΔν hpYν μ)
                (deformedGroup_spec hΔν μ).1
                (deformedNativeSurface_actsFreely Yν hYν hΔν hpYν μ) hsmooth)
            (_hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
            (_hCartan₁ : letI := Cν
              letI : IsManifold RI ω Tν := realν
              ∀ (k : I) (U W : FormInterior.SmoothVectorField RI (M := Tν)),
                Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
                  Yν hpYν hg hYν hΔν hfYν hsmooth hWPForm₁ ⊤ 1 (by norm_num)
                  (fun t a => sameOriginalFNUnitCurve Yν hg hYν hA₁ hAlt₁ D₁
                    hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ a k (left k) t)
                  (sameOriginalFNSignedTwistField Yν hpYν hg hYν hΔν hfYν hsmooth
                    hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ hCompat₁ k (left k)) U W
                  (sameOriginalFN_unitCurve_localFlowData Yν hpYν hg hYν hΔν hfYν hsmooth
                    hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ hCompat₁ k (left k)).1
                  (sameOriginalFN_unitCurve_localFlowData Yν hpYν hg hYν hΔν hfYν hsmooth
                    hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ hCompat₁ k (left k)).2.1
                  (sameOriginalFN_unitCurve_localFlowData Yν hpYν hg hYν hΔν hfYν hsmooth
                    hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ hCompat₁ k (left k)).2.2.1
                  (sameOriginalFN_unitCurve_localFlowData Yν hpYν hg hYν hΔν hfYν hsmooth
                    hA₁ hAlt₁ D₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ hCompat₁ k (left k)).2.2.2),
            letI := R.toRiemannAtlas.toChartedSpace
            letI := C
            letI : IsManifold RI ω T := realManifold
            (∀ (q : T) (v w : TangentSpace RI q),
              omega q ![v, w] = ∑ j,
                ((mvfderiv RI Nbook q v).2 j * (mvfderiv RI Nbook q w).1 j -
                  (mvfderiv RI Nbook q v).1 j * (mvfderiv RI Nbook q w).2 j)) ∧
            ∀ (q : T) (j : I) (z : TangentSpace RI q),
              omega q ![L j q, z] =
                -mfderiv RI 𝓘(ℝ) (fun a : T => (Nbook a).2 j) q z := by
  classical
  obtain ⟨ν, F, hF, hmark, N, D₁, t₀₁, J, hJ, hJcuffs, hJpants⟩ := hSym
  refine ⟨ν, F, hF, hmark, N, D₁, t₀₁, J, hJ, hJcuffs, hJpants, ?_⟩
  intro e₁ hA₁ hAlt₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁ hCompat₁ hRebase₁
    hGeom₁ hWPReflection₁ hWPForm₁ hFrickeBers₁ hvariation₁ hjets hCartan₁
  let := R.toRiemannAtlas.toChartedSpace
  let := C
  let Yν := deformedNativeSurface R hgenus hΓ hp ν
  let hYν := deformedNativeSurface_hasGenus R hgenus hΓ hp ν
  let hpYν := deformedNativeSurface_uniformization R hgenus hΓ hp ν
  let hΔν := (deformedGroup_spec hΓ ν).1
  let hfYν := deformedNativeSurface_actsFreely R hgenus hΓ hp ν
  let := canonicalComplexChartedSpace Yν hg hYν hP hΔν hfYν hpYν hsmooth
  let : IsManifold RI ω T := realManifold
  let : IsManifold RI ω (TeichmullerSpace Yν) :=
    Topology.IsOpenEmbedding.isManifold_singleton («I» := RI) (n := ω)
      (canonicalBersCoordinates_isOpenEmbedding Yν hg hYν hP hΔν hfYν hpYν hsmooth)
  dsimp only
  constructor
  · exact originalFN_book_Wolpert_via_matching_deformed_reference
      R hp hg hgenus hΓ hfree hsmooth ν F hF hmark D₀ D₁ t₀₁ hA hA₁
      φ φ₁ Θ Θ₁ hφ hφ₁ hΘ hΘ₁ hAlt hAlt₁ hU hU₁ hRigid hRealize hRigid₁ hRealize₁ hBook
      hCompat hCompat₁ hRebase₁ J hJ hJcuffs hJpants hGeom₁ hWPReflection₁
      hWPForm₁ hFrickeBers₁ hvariation₁ hjets hCartan₁
  · exact originalFN_book_length_contraction_via_matching_deformed_reference
      R hp hg hgenus hΓ hfree hsmooth ν F hF hmark D₀ D₁ t₀₁ hA hA₁
      φ φ₁ Θ Θ₁ hφ hφ₁ hΘ hΘ₁ hAlt hAlt₁ hU hU₁ hRigid hRealize hRigid₁ hRealize₁ hBook
      hCompat hCompat₁ hRebase₁ J hJ hJcuffs hJpants hGeom₁ hWPReflection₁
      hWPForm₁ hFrickeBers₁ hvariation₁ hjets hCartan₁

end LowDimensionalTopology.Geometry.Teichmuller
