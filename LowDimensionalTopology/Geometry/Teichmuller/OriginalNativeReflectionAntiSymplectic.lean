module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalNativeMarkedReflection
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMarkedReflectionAntiSymplectic
public import LowDimensionalTopology.Geometry.Teichmuller.GammaNativeRealWPPullback
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The same original native reflection reverses the real WP two-form

The actual normalized-lift square identifies the two given-J maps. Its genuine
real chain rule and the already proved full native/group real-form pullback
transport the actual anti-symplectic identity to the original native quotient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
open Surfaces LiZhongQC TeichmullerSpace GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (hΓ : IsFuchsian Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    (J : X ≃ₜ X)
    (hJ : @IsAnticonformalInvolution X inferInstance R.toRiemannAtlas.toChartedSpace J)

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "T" => TeichmullerSpace R
local notation "TG" => TeichGamma Γ
local notation "hfree" => closedUniformization_deckActsFreely R hp
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ hfree hp
local notation "D" => canonicalGammaDiffeomorph R hp hg hgenus hΓ hfree hsmooth
local notation "rN" => originalNativeTeichmullerReflection R hg hgenus J hJ
local notation "nativeForm" => nativeWeilPeterssonRealFundamentalForm
  R hp hg hgenus hΓ hfree hsmooth
local notation "groupForm" => gammaWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hsmooth

/-- The same original native reflection has a genuine real derivative at every point. -/
theorem originalNativeTeichmullerReflection_real_mdifferentiable :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    MDifferentiable RI RI rN := by
  let := R.toRiemannAtlas.toChartedSpace
  let : TopologicalSpace (ClosedSpace R) :=
    distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface)
  let := C; let := mΓ; let := CG
  let HR := closedGammaHomeomorph R hg hgenus hΓ hp
  let rΓ : TG → TG := fun a => HR (originalTeichmullerReflection R J hJ (HR.symm a))
  have hconj : rN = (D).symm ∘ rΓ ∘ D := by
    funext q
    apply (D).injective
    change D (rN q) = D ((D).symm (rΓ (D q)))
    rw [(D).apply_symm_apply]
    exact originalNativeTeichmullerReflection_gamma_square R hg hgenus J hJ hΓ hp hsmooth q
  have hD := canonicalGammaDiffeomorph_real_contMDiff_bothDirections R hp hg hgenus hΓ hsmooth
  have hr (a : TG) : MDifferentiableAt RI RI rΓ a :=
    (originalTeichmullerReflection_real_derivative R hg hgenus hΓ hp J hJ a).1
  rw [hconj]
  intro q
  exact (hD.2.mdifferentiableAt (by decide)).comp q
    ((hr (D q)).comp q (hD.1.mdifferentiableAt (by decide)))

/-- The concrete original metric assertion reverses the full actual native real WP form. -/
theorem originalNativeTeichmullerReflection_antiSymplectic
    (hWP : Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
      R hp hg hgenus hΓ J hJ hsmooth) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := C
    ∀ q : T, (nativeForm (rN q)).compContinuousLinearMap (mfderiv RI RI rN q) =
      -nativeForm q := by
  let := R.toRiemannAtlas.toChartedSpace
  let : TopologicalSpace (ClosedSpace R) :=
    distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface)
  let := C; let := mΓ; let := CG
  let HR := closedGammaHomeomorph R hg hgenus hΓ hp
  let rΓ : TG → TG := fun a => HR (originalTeichmullerReflection R J hJ (HR.symm a))
  have hconj : rN = (D).symm ∘ rΓ ∘ D := by
    funext q
    apply (D).injective
    change D (rN q) = D ((D).symm (rΓ (D q)))
    rw [(D).apply_symm_apply]
    exact originalNativeTeichmullerReflection_gamma_square R hg hgenus J hJ hΓ hp hsmooth q
  have hD := canonicalGammaDiffeomorph_real_contMDiff_bothDirections R hp hg hgenus hΓ hsmooth
  have hr (a : TG) : MDifferentiableAt RI RI rΓ a :=
    (originalTeichmullerReflection_real_derivative R hg hgenus hΓ hp J hJ a).1
  intro q
  have hdf (v : TangentSpace RI q) :
      mfderiv RI RI rN q v = mfderiv RI RI (D).symm (rΓ (D q))
        (mfderiv RI RI rΓ (D q) (mfderiv RI RI D q v)) := by
    rw [hconj, mfderiv_comp_apply q (hD.2.mdifferentiableAt (by decide))
      ((hr (D q)).comp q (hD.1.mdifferentiableAt (by decide))),
      mfderiv_comp_apply q (hr (D q)) (hD.1.mdifferentiableAt (by decide))]
    simp only [Function.comp_apply]
  have hinverse (v : TangentSpace RI q) :
      mfderiv RI RI (D).symm (D q) (mfderiv RI RI D q v) = v := by
    have hid : (D).symm ∘ D = @id T := funext (D).symm_apply_apply
    have h := mfderiv_comp_apply q (hD.2.mdifferentiableAt (by decide))
      (hD.1.mdifferentiableAt (by decide)) v
    rw [hid, mfderiv_id] at h
    exact h.symm
  apply ContinuousAlternatingMap.ext
  intro v
  change nativeForm (rN q) (fun i => mfderiv RI RI rN q (v i)) = -(nativeForm q v)
  calc
    nativeForm (rN q) (fun i => mfderiv RI RI rN q (v i)) =
        nativeForm ((D).symm (rΓ (D q))) (fun i =>
          mfderiv RI RI (D).symm (rΓ (D q))
            (mfderiv RI RI rΓ (D q) (mfderiv RI RI D q (v i)))) := by
      rw [congrFun hconj q]
      exact congrArg (nativeForm ((D).symm (rΓ (D q)))) (funext fun i => hdf (v i))
    _ = groupForm (rΓ (D q)) (fun i =>
        mfderiv RI RI rΓ (D q) (mfderiv RI RI D q (v i))) :=
      congrArg (fun A : TangentSpace RI (rΓ (D q)) [⋀^Fin 2]→L[ℝ] ℝ =>
        A (fun i => mfderiv RI RI rΓ (D q) (mfderiv RI RI D q (v i))))
        (gammaWeilPeterssonRealFundamentalForm_eq_native_pullback
          R hp hg hgenus hΓ hsmooth (rΓ (D q)))
    _ = -(groupForm (D q) (fun i => mfderiv RI RI D q (v i))) :=
      congrArg (fun A : TangentSpace RI (D q) [⋀^Fin 2]→L[ℝ] ℝ =>
        A (fun i => mfderiv RI RI D q (v i)))
        (originalTeichmullerReflection_antiSymplectic
          R hg hgenus hΓ hp J hJ hsmooth hWP (D q))
    _ = -(nativeForm ((D).symm (D q)) (fun i =>
        mfderiv RI RI (D).symm (D q) (mfderiv RI RI D q (v i)))) :=
      congrArg Neg.neg (congrArg
        (fun A : TangentSpace RI (D q) [⋀^Fin 2]→L[ℝ] ℝ =>
          A (fun i => mfderiv RI RI D q (v i)))
        (gammaWeilPeterssonRealFundamentalForm_eq_native_pullback
          R hp hg hgenus hΓ hsmooth (D q))).symm
    _ = -(nativeForm q v) := by
      rw [(D).symm_apply_apply]
      exact congrArg Neg.neg (congrArg (nativeForm q) (funext fun i => hinverse (v i)))

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
