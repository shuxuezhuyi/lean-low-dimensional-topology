module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMarkedReflectionAnalytic
public import LowDimensionalTopology.Geometry.Teichmuller.GammaWeilPeterssonFundamentalForm
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# The same original marked reflection reverses the WP fundamental form

The actual original chart expression supplies its genuine real derivative
and the anti-i identity. The concrete original WP metric assertion then
reverses the full original real tangent two-form, retaining the source's
twice-real-part metric and minus-twice-imaginary-part fundamental form.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Topology
open scoped ComplexConjugate UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces LiZhongQC TeichmullerSpace GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : IsFuchsian Γ) {p : ℍ → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (J : X ≃ₜ X)
    (hJ : @IsAnticonformalInvolution X inferInstance R.toRiemannAtlas.toChartedSpace J)

local notation "Z" => Fin (3 * g - 3) → ℂ
local notation "RI" => 𝓘(ℝ, Z)
local notation "TG" => TeichGamma Γ
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ (s27g_actsFreely hp) hp
local notation "CG" => gammaBersChartedSpace R hg hgenus hΓ (s27g_actsFreely hp) hp
local notation "realify" => gammaRealComplexTangentEquiv R hp hg hgenus hΓ
local notation "realCoord" => gammaWeilPeterssonRealTangentCoordinateEquiv R hp hg hgenus hΓ

/-- The actual real derivative anticommutes with the original complex tangent operator. -/
theorem originalTeichmullerReflection_real_derivative :
    letI := R.toRiemannAtlas.toChartedSpace
    letI : TopologicalSpace (ClosedSpace R) :=
      distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface)
    letI := mΓ
    letI := CG
    let HR := closedGammaHomeomorph R hg hgenus hΓ hp
    let rΓ : TG → TG := fun a => HR (originalTeichmullerReflection R J hJ (HR.symm a))
    let Ireal := fun (a : TG) (v : TangentSpace RI a) =>
      (realify a).symm (I • realify a v)
    ∀ a : TG, MDifferentiableAt RI RI rΓ a ∧ ∀ v : TangentSpace RI a,
      mfderiv RI RI rΓ a (Ireal a v) = -Ireal (rΓ a) (mfderiv RI RI rΓ a v) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := mΓ
  let := CG
  let : Nonempty TG := ⟨TeichGamma.origin Γ⟩
  let : TopologicalSpace (ClosedSpace R) :=
    distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface)
  let HR := closedGammaHomeomorph R hg hgenus hΓ hp
  let rΓ : TG → TG := fun a => HR (originalTeichmullerReflection R J hJ (HR.symm a))
  let G := gammaBersCoordinates R hg hgenus hΓ (s27g_actsFreely hp) hp
  let hG := gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ (s27g_actsFreely hp) hp
  let : IsManifold RI ω TG := hG.isManifold_singleton
  let e := hG.toOpenPartialHomeomorph G
  let f : Z → Z := G ∘ rΓ ∘ e.symm
  have hc : Continuous rΓ := HR.continuous.comp
    ((originalTeichmullerReflection_continuous R J hJ).comp HR.symm.continuous)
  dsimp only
  intro a
  have hhol := originalTeichmullerReflection_antiholomorphic R hg hgenus hΓ hp J hJ a
  change DifferentiableOn ℂ (fun v : Z => star (f v))
    (e.target ∩ e.symm ⁻¹' (rΓ ⁻¹' e.source)) at hhol
  have hholOn : DifferentiableOn ℂ (fun v : Z => star (f v)) (range G) := by
    simpa only [e, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, preimage_univ, inter_univ]
      using hhol
  have hd := hholOn.differentiableAt (hG.isOpenMap.isOpen_range.mem_nhds (mem_range_self a))
  let D : Z →L[ℂ] Z := fderiv ℂ (fun v : Z => star (f v)) (G a)
  have hf : HasFDerivAt f
      ((starL' ℝ : Z ≃L[ℝ] Z).toContinuousLinearMap.comp (D.restrictScalars ℝ)) (G a) := by
    simpa only [star_star] using (hd.hasFDerivAt.restrictScalars ℝ).star
  let L : TangentSpace RI a →L[ℝ] TangentSpace RI (rΓ a) :=
    (realCoord (rΓ a)).symm.toContinuousLinearMap.comp
      (((starL' ℝ : Z ≃L[ℝ] Z).toContinuousLinearMap.comp (D.restrictScalars ℝ)).comp
        (realCoord a).toContinuousLinearMap)
  have hL : HasMFDerivAt RI RI rΓ a L := by
    refine ⟨hc.continuousAt, ?_⟩
    change HasFDerivWithinAt f
      ((starL' ℝ : Z ≃L[ℝ] Z).toContinuousLinearMap.comp (D.restrictScalars ℝ))
      (range RI) (G a)
    exact hf.hasFDerivWithinAt
  refine ⟨hL.mdifferentiableAt, ?_⟩
  intro v
  rw [hL.mfderiv]
  apply (realCoord (rΓ a)).injective
  change star (D (I • realCoord a v)) =
    -(I • star (D (realCoord a v)))
  rw [map_smul, star_smul]
  simp only [Complex.star_def, Complex.conj_I, neg_smul]

/-- The concrete real WP metric assertion reverses the full original tangent two-form. -/
theorem originalTeichmullerReflection_antiSymplectic
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    (hWP : Unproved.Teichmuller.OriginalTeichmullerReflectionWPIsometry
      R hp hg hgenus hΓ J hJ hsmooth) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI : TopologicalSpace (ClosedSpace R) :=
      distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface)
    letI := mΓ
    letI := CG
    let HR := closedGammaHomeomorph R hg hgenus hΓ hp
    let rΓ : TG → TG := fun a => HR (originalTeichmullerReflection R J hJ (HR.symm a))
    ∀ a : TG,
      (gammaWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hsmooth (rΓ a)).compContinuousLinearMap
        (mfderiv RI RI rΓ a) = -gammaWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hsmooth a := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := mΓ
  let := CG
  let : TopologicalSpace (ClosedSpace R) :=
    distanceTopology (Surface.ofRiemannSurface R.toRiemannSurface)
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ (s27g_actsFreely hp) hp hsmooth
  let HR := closedGammaHomeomorph R hg hgenus hΓ hp
  let rΓ : TG → TG := fun a => HR (originalTeichmullerReflection R J hJ (HR.symm a))
  let Ireal := fun (a : TG) (v : TangentSpace RI a) =>
    (realify a).symm (I • realify a v)
  let metric := gammaWeilPeterssonRealTangentForm R hp hg hgenus hΓ hsmooth
  let omega := gammaWeilPeterssonRealFundamentalForm R hp hg hgenus hΓ hsmooth
  let H := gammaWeilPeterssonCore R hp hg hgenus hΓ hsmooth
  have hmetric (a : TG) (v w : TangentSpace RI a) :
      metric (rΓ a) (mfderiv RI RI rΓ a v) (mfderiv RI RI rΓ a w) = metric a v w := hWP a v w
  have homega (a : TG) (v w : TangentSpace RI a) :
      omega a ![v, w] = metric a (Ireal a v) w := by
    rw [gammaWeilPeterssonRealFundamentalForm_apply, gammaWeilPeterssonRealTangentForm_apply]
    change -2 * ((H a).inner (realify a w) (realify a v)).im =
      2 * ((H a).inner (realify a w) (realify a ((realify a).symm (I • realify a v)))).re
    rw [(realify a).apply_symm_apply, InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ)]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub, mul_neg, neg_mul]
  dsimp only
  intro a
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  change omega (rΓ a) ![mfderiv RI RI rΓ a (v 0), mfderiv RI RI rΓ a (v 1)] =
    -(omega a ![v 0, v 1])
  have hanti : Ireal (rΓ a) (mfderiv RI RI rΓ a (v 0)) =
      -(mfderiv RI RI rΓ a (Ireal a (v 0))) := by
    have h := congrArg Neg.neg
      ((originalTeichmullerReflection_real_derivative R hg hgenus hΓ hp J hJ a).2 (v 0))
    simpa only [neg_neg] using h.symm
  calc
    omega (rΓ a) ![mfderiv RI RI rΓ a (v 0), mfderiv RI RI rΓ a (v 1)] =
        metric (rΓ a) (Ireal (rΓ a) (mfderiv RI RI rΓ a (v 0)))
          (mfderiv RI RI rΓ a (v 1)) := homega _ _ _
    _ = -(metric (rΓ a) (mfderiv RI RI rΓ a (Ireal a (v 0)))
        (mfderiv RI RI rΓ a (v 1))) := by rw [hanti, map_neg]; rfl
    _ = -(metric a (Ireal a (v 0)) (v 1)) := congrArg Neg.neg (hmetric a _ _)
    _ = -(omega a ![v 0, v 1]) := congrArg Neg.neg (homega a (v 0) (v 1)).symm

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
