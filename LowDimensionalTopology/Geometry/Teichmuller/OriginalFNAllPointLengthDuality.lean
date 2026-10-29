module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCuffPrescribedCoverNormalization
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNDeformedReferenceCurve
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCoefficientCurveTangent
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNPointwiseLengthDuality
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalLengthReferenceDifferential
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedReferenceHarmonicNaturalityProof

/-!
# Length duality for the same physical FN field at every original point

The actual marked cuff supplies its full oriented normalization on the
prescribed deformed cover. The same original unit curve, its actual rebased
coefficient direction, and the harmonic endpoint series identify the physical
velocity. The proved reference pullback and marked-length covector chain
transport the base-point numerical identity back to the fixed original space.
The intrinsic seam-side sign remains explicit throughout.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Bundle Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

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
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)
    (hU : Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic R hg hgenus hA hAlt D₀)
    (φ : C(nativeFrickeImage hA, Fin (3 * g - 3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3 * g - 3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D₁ : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D₁)
      (j : Fin (3 * g - 3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ j = D₁.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun x => Θ x j) = fun x => φ x j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)
    (left : Fin (3 * g - 3) → Fin 2)

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3 * g - 3) → ℂ
local notation "V" => (Fin (3 * g - 3) → ℝ) × (Fin (3 * g - 3) → ℝ)
local notation "TI" => 𝓘(ℂ, E)
local notation "RI" => 𝓘(ℝ, E)
local notation "FI" => 𝓘(ℝ, V)
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "c" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "N" => originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
local notation "sigma" => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
  hU φ Θ hφ hΘ hRigid hRealize
local notation "unitTwist" => (fun j : Fin (3 * g - 3) =>
  ((0 : Fin (3 * g - 3) → ℝ), Pi.single (M := fun _ => ℝ) j (1 : ℝ)))
local notation "Xj" => (fun (j : Fin (3 * g - 3)) (a : T) =>
  VectorField.mpullback RI FI N
    (fun y : V => ContinuousLinearEquiv.symm
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) y) (unitTwist j)) a)
local notation "Compat" => Unproved.Teichmuller.OriginalFNNativeSmoothInverse
  R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
local notation "Rebase" => Unproved.Teichmuller.OriginalFNSameCurveDeformedReferenceMarking
  R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left
local notation "omega" => nativeWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hfree hsmooth
local notation "Omega" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

variable (ν : Ball Γ)

local notation "Y" => deformedNativeSurface R hgenus hΓ hp ν
local notation "pY" => deformedTargetCover R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "hgY" => deformedNativeSurface_hasGenus R hgenus hΓ hp ν
local notation "Δ" => deformedGroup hΓ ν
local notation "hΔ" => And.left (deformedGroup_spec hΓ ν)
local notation "hfY" => deformedNativeSurface_actsFreely R hgenus hΓ hp ν
local notation "eY" => deformedTargetMarking R hgenus hΓ hp ν
local notation "CY" => canonicalComplexChartedSpace Y hg hgY hP hΔ hfY hpY hsmooth
local notation "BCY" => bersCoordinates Y hg hgY hP hΔ hfY hpY
local notation "cY" => nativeWeilPeterssonCoordinateChart Y hpY hg hgY hΔ hfY hsmooth (basePoint Y)
local notation "DY" => nativeWeilPeterssonRealTangentCoordinateEquiv Y hpY hg hgY hΔ hfY hsmooth
local notation "rY" => nativeRealComplexTangentEquiv Y hpY hg hgY hΔ hfY hsmooth
local notation "βY" => coefficientProjection Y hg hgY hP hΔ hfY hpY
local notation "omegaY" => nativeWeilPeterssonRealFundamentalForm Y hpY hg hgY hΔ hfY hsmooth
local notation "OmegaY" => nativeWeilPeterssonFundamentalRealCoordinateForm
  Y hpY hg hgY hΔ hfY hsmooth (basePoint Y)
local notation "a" => coefficientProjectionBall R hg hgenus hP hΓ hfree hp ν
local notation "Aν" => deformedReferenceChangeEquiv R hp hg hgenus hΓ ν
local notation "f" => deformedReferenceWeilPeterssonCoordinateMap R hp hg hgenus hΓ ν

/-- At an actual coefficient centre of the fixed original space, the physical
unit FN vector has the full marked-length contraction with the actual WP form. -/
theorem sameOriginalFN_signed_twist_length_duality_at_coefficient
    (hCompat : Compat) (hRebase : Rebase) (j : Fin (3 * g - 3)) :
    letI := C
    Unproved.Teichmuller.WolpertLengthDualityAt R hp hg hgenus hΓ hfree hsmooth
      a (D₀.cuff j).toLoop (originalFNUnitSideSign (left j) • Xj j a) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := (Y).toRiemannAtlas.toChartedSpace
  let := C
  let := CY
  let : IsManifold RI ω T :=
    (canonicalBersCoordinates_isOpenEmbedding R hg hgenus hP hΓ hfree hp hsmooth).isManifold_singleton
  let : IsManifold RI ω (TeichmullerSpace Y) :=
    (canonicalBersCoordinates_isOpenEmbedding Y hg hgY hP hΔ hfY hpY hsmooth).isManifold_singleton
  dsimp only
  let αY : LiZhongQC.Loop (deformedTargetSource R hgenus hΓ hp ν).carrier :=
    ⟨eY (D₀.cuff j).toLoop.1, (D₀.cuff j).toLoop.2.map (eY).continuous⟩
  obtain ⟨A, Q, s, hs, hA0, hTrace, hAΔ, hcov, hQA, hsep⟩ :=
    originalFN_deformedReference_exists_normalization R hp hg hgenus hΓ hsmooth
      hA hAlt D₀ hU ν j
  let := NormedSpace.restrictScalars ℝ ℂ (BersWeighted.Automorphic Δ)
  let := IsScalarTower.restrictScalars ℝ ℂ (BersWeighted.Automorphic Δ)
  obtain ⟨η, hcurve, hharmonic⟩ := sameOriginalFN_deformedReference_curve_harmonic
    R hp hg hgenus hΓ hfree hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left ν
      hRebase j A Q s hs hAΔ hcov hQA hA0 hTrace hsep
  let vR : TangentSpace RI a := originalFNUnitSideSign (left j) • Xj j a
  let vY : TangentSpace RI (basePoint Y) :=
    (rY (basePoint Y)).symm (mfderiv 𝓘(ℂ, Space Δ) TI βY 0 η)
  have hunit := sameOriginalFN_unitCurve_native_twistDerivative
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
      hCompat a j (left j)
  have hbase : Aν a = basePoint Y := by
    simpa only [coefficientProjection_ball] using
      deformedReferenceChangeEquiv_base R hp hg hgenus hΓ hfree ν
  have hzero : Aν (sigma a j (left j) 0) = basePoint Y := by
    rw [hunit.1]
    exact hbase
  have hcoefficient := (sameOriginalCoefficientCurve_native_base_tangent
    Y hpY hg hgY hΔ hfY hsmooth (fun t => Aν (sigma a j (left j) t))
      hzero η hcurve).2
  have hunitBC : HasDerivAt (fun t : ℝ => BC (sigma a j (left j) t)) (D a vR) 0 := by
    simpa only [vR, nativeWeilPeterssonCoordinateChart_coe] using hunit.2.2.2
  have hx : BC a ∈ (c).target := (c).map_source (mem_chart_source E a)
  have hana := deformedReferenceWeilPeterssonCoordinateMap_analytic
    R hp hg hgenus hΓ hfree hsmooth ν
  have hchain : HasDerivAt (fun t : ℝ => BCY (Aν (sigma a j (left j) t)))
      (fderiv ℝ f (BC a) (D a vR)) 0 := by
    have h := ((hana.1 (BC a) hx).differentiableAt.restrictScalars ℝ).hasFDerivAt
      |>.comp_hasDerivAt_of_eq (0 : ℝ) hunitBC (by rw [hunit.1])
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun t =>
      (deformedReferenceWeilPeterssonCoordinateMap_point
        R hp hg hgenus hΓ hfree ν (sigma a j (left j) t)).symm)
  have hvelocity : fderiv ℝ f (BC a) (D a vR) = DY (basePoint Y) vY :=
    hchain.unique hcoefficient
  have hframe := exists_same_originalFN_native_coordinate_frame
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat
  have hproj : DifferentiableAt ℝ (fun y : V => y.1 j) (N a) :=
    differentiableAt_pi.1 (differentiableAt_fst (𝕜 := ℝ) (p := N a)) j
  have hLength : MDifferentiableAt RI 𝓘(ℝ)
      (markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus (D₀.cuff j).toLoop) a := by
    have h := hproj.mdifferentiableAt.comp a ((hframe.1 a).mdifferentiableAt (by simp))
    exact h
  have hLengthTransport := marked_length_deformedReference_differential
    R hp hg hgenus hΓ hfree hsmooth ν (D₀.cuff j).toLoop hLength
  obtain ⟨P, F, hF⟩ := exists_deformedHalfPlaneFundamentalRegion R hgenus hΓ hp ν
  obtain ⟨Ψ, hΨ, hH⟩ := hharmonic P F hF
  have hDualY := originalCoefficientDirection_length_duality_at_basePoint
    Y hpY hg hgY hΔ hfY hsmooth αY A hAΔ hcov hA0 hTrace hLengthTransport.1
      P F hF η Ψ hΨ hH
  change ∀ z : TangentSpace RI (basePoint Y),
    omegaY (basePoint Y) ![vY, z] =
      mfderiv RI 𝓘(ℝ) (markedGeodesicLength Y (Nat.succ_le_of_lt hg) hgY αY)
        (basePoint Y) z at hDualY
  obtain ⟨S, _hSo, hν, _hSU, hWP⟩ :=
    nativeWeilPeterssonCoordinateForm_deformedReference_local_pullback
      R hp hg hgenus hΓ hfree hsmooth ν
        (deformedReferenceHarmonicNaturality R hp hg hgenus hΓ hfree hsmooth)
  have hνa : BC a ∈ S := by simpa only [coefficientProjection_ball] using hν
  have hcenter : f (BC a) = 0 := by
    simpa only [coefficientProjection_ball] using
      deformedReferenceWeilPeterssonCoordinateMap_center R hp hg hgenus hΓ hfree ν
  have hWPat := hWP (BC a) hνa
  rw [hcenter] at hWPat
  have hleft : (c).symm (BC a) = a := by
    simpa only [nativeWeilPeterssonCoordinateChart_coe] using
      (c).left_inv (mem_chart_source E a)
  have hleftY : (cY).symm (0 : E) = basePoint Y := by
    simpa only [nativeWeilPeterssonCoordinateChart_coe, bersCoordinates_basePoint] using
      (cY).left_inv (mem_chart_source E (basePoint Y))
  intro z
  change (omega a ![vR, z] : ℝ) =
    (mfderiv RI 𝓘(ℝ)
      (markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus (D₀.cuff j).toLoop) a z : ℝ)
  have hsourceWP : (omega a ![vR, z] : ℝ) = Omega (BC a) ![D a vR, D a z] := by
    rw [nativeWeilPeterssonFundamentalRealCoordinateForm_apply, hleft]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  have hpullbackWP : (Omega (BC a) ![D a vR, D a z] : ℝ) =
      OmegaY 0 ![fderiv ℝ f (BC a) (D a vR), fderiv ℝ f (BC a) (D a z)] := by
    rw [hWPat]
    rfl
  have htargetWP :
      (OmegaY 0 ![fderiv ℝ f (BC a) (D a vR), fderiv ℝ f (BC a) (D a z)] : ℝ) =
        omegaY (basePoint Y)
          ![vY, (DY (basePoint Y)).symm (fderiv ℝ f (BC a) (D a z))] := by
    rw [nativeWeilPeterssonFundamentalRealCoordinateForm_apply, hleftY, hvelocity]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  have hphysicalDual :
      (omegaY (basePoint Y)
        ![vY, (DY (basePoint Y)).symm (fderiv ℝ f (BC a) (D a z))] : ℝ) =
        (mfderiv RI 𝓘(ℝ)
          (markedGeodesicLength Y (Nat.succ_le_of_lt hg) hgY αY) (basePoint Y)
            ((DY (basePoint Y)).symm (fderiv ℝ f (BC a) (D a z))) : ℝ) := hDualY _
  have hlengthCovector :
      (mfderiv RI 𝓘(ℝ)
        (markedGeodesicLength Y (Nat.succ_le_of_lt hg) hgY αY) (basePoint Y)
          ((DY (basePoint Y)).symm (fderiv ℝ f (BC a) (D a z))) : ℝ) =
        (mfderiv RI 𝓘(ℝ)
          (markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus (D₀.cuff j).toLoop) a z : ℝ) :=
    hLengthTransport.2 z
  exact hsourceWP.trans (hpullbackWP.trans
    (htargetWP.trans (hphysicalDual.trans hlengthCovector)))

/-- Every point of the same fixed original Teichmuller space has physical
FN length duality, for its same actual native signed pullback field. -/
theorem sameOriginalFN_signed_twist_length_duality
    (hCompat : Compat) (hRebase : Rebase) :
    letI := C
    ∀ (q : T) (j : Fin (3 * g - 3)),
      Unproved.Teichmuller.WolpertLengthDualityAt R hp hg hgenus hΓ hfree hsmooth
        q (D₀.cuff j).toLoop (originalFNUnitSideSign (left j) • Xj j q) := by
  let := C
  dsimp only
  intro q j
  obtain ⟨μ, rfl⟩ := coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp q
  exact sameOriginalFN_signed_twist_length_duality_at_coefficient
    R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize left μ
      hCompat hRebase j

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
