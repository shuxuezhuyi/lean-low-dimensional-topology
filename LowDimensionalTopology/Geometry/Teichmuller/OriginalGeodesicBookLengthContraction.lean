module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNBookSymmetricSelection
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNContinuousRealBranch
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNReferenceContainingGeodesic

/-!
# The book length contraction for a prescribed original geodesic

One actual rich reference retains the full original geodesic as a cuff.
The phase input produces an actual branch on both references. One matching
symmetric target, with its existing analysis inputs, gives the contraction
of the literal original book length vector with minus the book twist covector.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami
open NormalizedCoefficientTransport

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

local notation "I" => Fin (3 * g - 3)
local notation "E" => I → ℂ
local notation "V" => (I → ℝ) × (I → ℝ)
local notation "T" => TeichmullerSpace R
local notation "RI" => 𝓘(ℝ, E)
local notation "FI" => 𝓘(ℝ, V)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "nativeC" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  («I» := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth)
local notation "omega" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "unitLength" => (fun j : I => (Pi.single (M := fun _ => ℝ) j (1 : ℝ), (0 : I → ℝ)))

/-- A prescribed full original geodesic has a genuine book branch and an
actual matching target. The literal original book length pullback contracts
to minus its original book twist differential at every original point. -/
theorem originalGeodesic_exists_book_length_contraction
    (q : OriginalClosedGeodesic M)
    (hReference : Unproved.Teichmuller.OriginalFNReferenceContainingGeodesic R g M q) :
    ∃ (inc : OriginalFNCuffIncidence g) (D₀ : OriginalFNRealization M inc)
      (j : I) (_hC : D₀.cuff j = q),
      ∀ (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
        (hBook : Unproved.Teichmuller.OriginalFNBookLeftCopyTransport D₀),
        ∃ (φ : C(nativeFrickeImage hA, I → Circle))
          (Θ : C(nativeFrickeImage hA, I → ℝ))
          (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
            (P : HyperbolicSurfaceModel m.surface.toRiemannSurface)
            (D : OriginalFNRealization P inc) (_t : OriginalFNMarkedTransport D₀ m D)
            (k : I),
            φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
              ⟨TeichmullerSpace.mk m, rfl⟩⟩ k = D.phase k)
          (hΘ : ∀ k, Circle.exp ∘ (fun x => Θ x k) = fun x => φ x k),
          (∀ k, Θ (nativeFrickeHomeomorph hA hAlt (basePoint R)) k =
            Complex.arg (φ (nativeFrickeHomeomorph hA hAlt (basePoint R)) k)) ∧
          (∀ k, OriginalFNCopyLeftGerm D₀ k ((Classical.choose hBook) k)) ∧
          (∀ (m : MarkedRiemannSurface.{0, 0} R)
            (P : HyperbolicSurfaceModel m.surface.toRiemannSurface)
            (D : OriginalFNRealization P inc),
            OriginalFNMarkedTransport D₀ m D →
              ∀ k, OriginalFNCopyLeftGerm D k ((Classical.choose hBook) k)) ∧
          ∀ (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
              R hg hgenus hA hAlt D₀ φ Θ)
            (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
              R hg hgenus hA hAlt D₀ φ Θ)
            (_hCompat : Unproved.Teichmuller.OriginalFNNativeSmoothInverse
              R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize)
            (_hSym : Unproved.Teichmuller.OriginalFNCompatibleDeformedSymmetricReference
              R hp hg hgenus hΓ D₀),
            let left := Classical.choose hBook
            let sourceFN := originalFNBookNativeCoordinateMap R hg hgenus hA hAlt D₀ Θ left
            (∀ a : T, (sourceFN a).1 j =
              markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus q.toLoop a) ∧
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
                    let e₁ := F.toHomeomorph.symm.trans e
                    ∀ (hA₁ : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable Yν hg e₁)
                      (hAlt₁ : ∀ m : MarkedRiemannSurface.{0, 0} Yν,
                        Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA₁ m))
                      (hU₁ : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic Yν hg hYν hA₁ hAlt₁ D₁),
                      ∃ (φ₁ : C(nativeFrickeImage hA₁, I → Circle))
                        (Θ₁ : C(nativeFrickeImage hA₁, I → ℝ))
                        (hφ₁ : ∀ (m : MarkedRiemannSurface.{0, 0} Yν)
                          (P : HyperbolicSurfaceModel m.surface.toRiemannSurface)
                          (D : OriginalFNRealization P inc) (_t : OriginalFNMarkedTransport D₁ m D)
                          (j : I),
                          φ₁ ⟨finiteFrickeCoordinates hA₁ (TeichmullerSpace.mk m),
                            ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D.phase j)
                        (hΘ₁ : ∀ j, Circle.exp ∘ (fun x => Θ₁ x j) = fun x => φ₁ x j),
                        (∀ k, Θ₁ (nativeFrickeHomeomorph hA₁ hAlt₁ (basePoint Yν)) k =
                          Complex.arg (φ₁ (nativeFrickeHomeomorph hA₁ hAlt₁ (basePoint Yν)) k)) ∧
                        ∀ (hRigid₁ : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
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
                          letI := nativeC
                          letI : IsManifold RI ω T := realManifold
                          ∀ (a : T) (z : TangentSpace RI a),
                            omega a ![VectorField.mpullback RI FI sourceFN
                              (fun y : V => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm
                                (unitLength j)) a, z] =
                              -mfderiv RI 𝓘(ℝ) (fun x : T => (sourceFN x).2 j) a z := by
  classical
  obtain ⟨inc, D₀, j, hC⟩ := hReference
  refine ⟨inc, D₀, j, hC, ?_⟩
  intro hU hBook
  obtain ⟨φ, Θ, hbase, hΘ, htarget⟩ := exists_originalFNContinuousRealBranch
    R hg hgenus hA hAlt D₀ hU (nativeFrickeHomeomorph hA hAlt (basePoint R))
  have hφ (m : MarkedRiemannSurface.{0, 0} R)
      (P : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization P inc) (t : OriginalFNMarkedTransport D₀ m D) (k : I) :
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ k = D.phase k :=
    (congrFun (hΘ k) ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
      ⟨TeichmullerSpace.mk m, rfl⟩⟩).symm.trans (htarget m P D t k)
  refine ⟨φ, Θ, hφ, hΘ, hbase, (Classical.choose_spec hBook).1,
    (Classical.choose_spec hBook).2, ?_⟩
  intro hRigid hRealize hCompat hSym
  let left := Classical.choose hBook
  let sourceFN := originalFNBookNativeCoordinateMap R hg hgenus hA hAlt D₀ Θ left
  refine ⟨?_, ?_⟩
  · intro a
    change markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus (D₀.cuff j).toLoop a = _
    rw [hC]
  · obtain ⟨ν, F, hF, hmark, N, D₁, t₀₁, J, hJ, hJcuffs, hJpants, hAnalysis⟩ :=
      exists_originalFN_book_formula_from_symmetric_reference
        R hp hg hgenus hΓ hfree hsmooth D₀ hA hAlt hU φ Θ hφ hΘ
        hRigid hRealize hBook hCompat hSym
    refine ⟨ν, F, hF, hmark, N, D₁, t₀₁, J, hJ, hJcuffs, hJpants, ?_⟩
    let Yν := deformedNativeSurface R hgenus hΓ hp ν
    let hYν := deformedNativeSurface_hasGenus R hgenus hΓ hp ν
    let e₁ := F.toHomeomorph.symm.trans e
    refine fun hA₁ hAlt₁ hU₁ => ?_
    obtain ⟨φ₁, Θ₁, hbase₁, hΘ₁, htarget₁⟩ := exists_originalFNContinuousRealBranch
      Yν hg hYν hA₁ hAlt₁ D₁ hU₁ (nativeFrickeHomeomorph hA₁ hAlt₁ (basePoint Yν))
    have hφ₁ (m : MarkedRiemannSurface.{0, 0} Yν)
        (P : HyperbolicSurfaceModel m.surface.toRiemannSurface)
        (D : OriginalFNRealization P inc) (t : OriginalFNMarkedTransport D₁ m D) (k : I) :
        φ₁ ⟨finiteFrickeCoordinates hA₁ (TeichmullerSpace.mk m),
          ⟨TeichmullerSpace.mk m, rfl⟩⟩ k = D.phase k :=
      (congrFun (hΘ₁ k) ⟨finiteFrickeCoordinates hA₁ (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩).symm.trans (htarget₁ m P D t k)
    refine ⟨φ₁, Θ₁, hφ₁, hΘ₁, hbase₁, ?_⟩
    refine fun hRigid₁ hRealize₁ hCompat₁ hRebase₁ hGeom₁ hWPReflection₁
      hWPForm₁ hFrickeBers₁ hvariation₁ hjets hCartan₁ => ?_
    let := R.toRiemannAtlas.toChartedSpace
    let := nativeC
    let : IsManifold RI ω T := realManifold
    refine fun a z => ?_
    exact (hAnalysis (e₁ := e₁) hA₁ hAlt₁ hU₁ φ₁ Θ₁ hφ₁ hΘ₁ hRigid₁ hRealize₁
      hCompat₁ hRebase₁ hGeom₁ hWPReflection₁ hWPForm₁ hFrickeBers₁ hvariation₁ hjets hCartan₁).2 a j z

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
