module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalFNWPCoefficientInvariance
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Original WP coefficients along the actual signed FN curves

The scalar evaluation is smooth by the original WP coordinate form and the
actual smooth frame. Its derivative vanishes at every real time by the
actual FN generator and the existing coefficient derivative theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces Surfaces.HandlePresentation GammaMeasurableBeltrami NormalizedCoefficientTransport

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    {e : X ≃ₜ PolygonQuotient g}
    {M : HyperbolicSurfaceModel R.toRiemannSurface} {inc : OriginalFNCuffIncidence g}
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
    (hAlt : ∀ m : MarkedRiemannSurface.{0,0} R,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))
    (D₀ : OriginalFNRealization M inc)

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3*g-3) → ℂ
local notation "F" => (Fin (3*g-3) → ℝ) × (Fin (3*g-3) → ℝ)
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
    (φ : C(nativeFrickeImage hA, Fin (3*g-3) → Circle))
    (Θ : C(nativeFrickeImage hA, Fin (3*g-3) → ℝ))
    (hφ : ∀ (m : MarkedRiemannSurface.{0,0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D₁ : OriginalFNRealization N inc) (_transport : OriginalFNMarkedTransport D₀ m D₁)
      (j : Fin (3*g-3)),
      φ ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m,rfl⟩⟩ j = D₁.phase j)
    (hΘ : ∀ j, Circle.exp ∘ (fun t => Θ t j) = fun t => φ t j)
    (hRigid : Unproved.Teichmuller.OriginalFNMarkedCoordinateRigidity
      R hg hgenus hA hAlt D₀ φ Θ)
    (hRealize : Unproved.Teichmuller.OriginalFNMarkedGluingRealization
      R hg hgenus hA hAlt D₀ φ Θ)

local notation "FN" => originalFNNativeRescaledCoordinateMap R hg hgenus hA hAlt D₀ Θ
local notation "K" => FN ∘ OpenPartialHomeomorph.symm c
local notation "Compat" => Unproved.Teichmuller.OriginalFNNativeSmoothInverse
  R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize

local notation "J" => Fin (3*g-3) ⊕ Fin (3*g-3)
local notation "b" => (fun a : J => match a with
  | Sum.inl j => (Pi.single j (1 : ℝ), (0 : Fin (3*g-3) → ℝ))
  | Sum.inr j => ((0 : Fin (3*g-3) → ℝ), Pi.single j (1 : ℝ)))
local notation "sigma" => sameOriginalFNUnitCurve R hg hgenus hA hAlt D₀
  hU φ Θ hφ hΘ hRigid hRealize
local notation "W" => sameOriginalFNSignedTwistField R hp hg hgenus hΓ hfree hsmooth
  hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
local notation "omegaWP" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "lengthOf" => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus

local notation "Omega" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)

private theorem nativeWP_fieldPairing_contMDiff
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ Y Z : FormInterior.SmoothVectorField RI (M := T),
      ContMDiff RI 𝓘(ℝ) ∞ (fun q : T => omegaWP q ![Y q,Z q]) := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro Y Z
  let y : E → E := fun z => D ((c).symm z) (Y ((c).symm z))
  let z : E → E := fun w => D ((c).symm w) (Z ((c).symm w))
  have hY : ContMDiffOn RI RI ∞ y (c).target :=
    (nativeWP_vectorFieldCoordinates_contDiffOn
      R hp hg hgenus hΓ hfree hsmooth Y).contMDiffOn
  have hZ : ContMDiffOn RI RI ∞ z (c).target :=
    (nativeWP_vectorFieldCoordinates_contDiffOn
      R hp hg hgenus hΓ hfree hsmooth Z).contMDiffOn
  have hOmega :=
    (contDiffOn_nativeWeilPeterssonFundamentalRealCoordinateForm_of_localSmoothness
      R hp hg hgenus hΓ hfree hsmooth hWP (basePoint R)).contMDiffOn
  have hEval : ContMDiffOn RI 𝓘(ℝ) ∞
      (fun w : E => Omega w ![y w,z w]) (c).target := by
    apply hOmega.continuousAlternatingMap_apply (f := fun i w => ![y w,z w] i)
    intro i
    fin_cases i
    · exact hY
    · exact hZ
  intro q
  have ht : c q ∈ (c).target := (c).map_source (mem_chart_source E q)
  have hc : ContMDiffAt RI RI ∞ c q := by
    change ContMDiffAt RI RI ∞ (extChartAt RI (basePoint R)) q
    exact contMDiffAt_extChartAt' (mem_chart_source E q)
  apply ((hEval.contMDiffAt ((c).open_target.mem_nhds ht)).comp q hc).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x => by
    change omegaWP x ![Y x,Z x] = Omega (c x)
      ![D ((c).symm (c x)) (Y ((c).symm (c x))),
        D ((c).symm (c x)) (Z ((c).symm (c x)))]
    rw [nativeWeilPeterssonFundamentalRealCoordinateForm_apply,
      (c).left_inv (mem_chart_source E x)]
    simp only [ContinuousLinearEquiv.symm_apply_apply]

/-- Every original FN coordinate coefficient is constant for all real times
along the actual signed FN curve, under the same explicit length duality. -/
theorem sameOriginalFN_wpCoefficient_unitCurve_constant
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (hFrickeBers : Unproved.Teichmuller.NativeFrickeBersRealAnalyticCompatibility
      R hg hgenus hΓ hfree hp hsmooth hA)
    (hvariation : ∀ ν : Ball Γ,
      Unproved.Teichmuller.WeilPeterssonHarmonicIntegralFirstVariation
        (deformedNativeSurface R hgenus hΓ hp ν)
        (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hg
        (deformedNativeSurface_hasGenus R hgenus hΓ hp ν)
        (deformedGroup_spec hΓ ν).1
        (deformedNativeSurface_actsFreely R hgenus hΓ hp ν) hsmooth)
    (hjets : Unproved.Teichmuller.CanonicalHarmonicEichlerJets.{0})
    (hCompat : Compat) (k : Fin (3*g-3)) (side : Fin 2) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    let Phi : ℝ → T → T := fun t a => sigma a k side t
    let Wk := W hCompat k side
    let h := sameOriginalFN_unitCurve_localFlowData R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k side
    (∀ Y Z : FormInterior.SmoothVectorField RI (M := T),
      Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
        R hp hg hgenus hΓ hfree hsmooth hWP ⊤ 1 (by norm_num) Phi Wk Y Z
        h.1 h.2.1 h.2.2.1 h.2.2.2) →
    (∀ (q : T) (v : TangentSpace RI q),
      omegaWP q ![Wk q,v] = mfderiv RI 𝓘(ℝ) (lengthOf (D₀.cuff k).toLoop) q v) →
    ∃ frame : J → FormInterior.SmoothVectorField RI (M := T),
      (∀ a q, frame a q = VectorField.mpullback RI FI FN
        (fun y : F => (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm (b a)) q) ∧
      ∀ (a d : J) (r s : ℝ) (q : T) (t : ℝ),
        omegaWP (sigma q k side t)
          ![(r • frame a) (sigma q k side t),(s • frame d) (sigma q k side t)] =
        omegaWP q ![(r • frame a) q,(s • frame d) q] := by
  let := C
  let : IsManifold RI ω T := realManifold
  dsimp only
  intro hCartan hDual
  rcases (sameOriginalFN_wpCoefficient_twistDerivative_zero
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
      hWP hFrickeBers hvariation hjets hCompat k side hCartan hDual).2 with
    ⟨frame,hframe,hzero⟩
  refine ⟨frame,hframe,?_⟩
  intro a d r s q t
  let A : T → ℝ := fun x => omegaWP x ![(r • frame a) x,(s • frame d) x]
  let curve : ℝ → T := sigma q k side
  have hCoeff : ContMDiff RI 𝓘(ℝ) ∞ A :=
    nativeWP_fieldPairing_contMDiff R hp hg hgenus hΓ hfree hsmooth
      hWP (r • frame a) (s • frame d)
  have hcurve : ContMDiff 𝓘(ℝ) RI ∞ curve := by
    have hjoint := sameOriginalFN_unitCurve_jointSmooth R hp hg hgenus hΓ hfree hsmooth
      hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize hCompat k side
    simpa only [Function.comp_def] using
      (hjoint.comp (I := 𝓘(ℝ)) (I' := (𝓘(ℝ)).prod RI) (I'' := RI)
        (f := fun u : ℝ => (u, q))
        ((contMDiff_id (I := 𝓘(ℝ)) (M := ℝ) (n := ∞)).prodMk
          (show ContMDiff 𝓘(ℝ) RI ∞ (fun _ : ℝ => q) from
            contMDiff_const)))
  have hscalar : ContDiff ℝ ∞ (A ∘ curve) := (hCoeff.comp hcurve).contDiff
  have hderiv (u : ℝ) : deriv (A ∘ curve) u = 0 := by
    have h := mfderiv_comp_apply u
      ((hCoeff (curve u)).mdifferentiableAt (by simp))
      ((hcurve u).mdifferentiableAt (by simp))
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) u).symm 1)
    have hgen := sameOriginalFN_unitCurve_native_generator
      R hp hg hgenus hΓ hfree hsmooth hA hAlt D₀ hU φ Θ hφ hΘ hRigid hRealize
      hCompat k side u q
    change mfderiv 𝓘(ℝ) RI curve u
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) u).symm 1) =
        W hCompat k side (curve u) at hgen
    rw [hgen, hzero a d r s (curve u)] at h
    have hv := congrArg (NormedSpace.fromTangentSpace
      (𝕜 := ℝ) ((A ∘ curve) u)) h
    simpa only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      fderiv_apply_one_eq_deriv, map_zero] using hv
  have heq := is_const_of_deriv_eq_zero (hscalar.differentiable (by simp)) hderiv t 0
  have hstart : curve 0 = q :=
    (sameOriginalFN_unitCurve_native_coordinates R hg hgenus hA hAlt D₀
      hU φ Θ hφ hΘ hRigid hRealize q k side).1
  simpa only [Function.comp_def, hstart] using heq

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
