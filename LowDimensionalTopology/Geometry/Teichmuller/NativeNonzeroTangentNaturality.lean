module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeNonzeroHarmonicTangent
public import LowDimensionalTopology.Geometry.Teichmuller.NativeDeformedHarmonicNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersDerivativeNaturality

/-!
# The induced original tangent-to-harmonic map is independent of its coefficient representative

The original point equality transports the actual tangent fibre by equality.
The actual Bers chart differential respects this equality transport. The
proved genuine coordinate-translation derivative naturality and the existing
harmonic integral inverse then identify the induced maps on that SAME tangent
fibre. The harmonic identification is already proved to be the identity on
actual coefficient classes and an isometry in their original infinity norms.

This statement concerns the induced original tangent map. It does not assert
equality of raw H L operators on coefficient spaces with different kernels.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces NormalizedCoefficientTransport

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)

local notation "E" => Fin (3 * g - 3) → ℂ

/-- Equality of the original projected points, for the original extended coefficient projection. -/
theorem coefficientProjection_eq_of_sameNativePoint (ν ν' : GammaMeasurableBeltrami.Ball Γ)
    (hpoint : coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp ν =
      coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν') :
    coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val =
      coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν'.val :=
  (coefficientProjection_ball R hg hgenus hΓ hfree hp ν).trans
    (hpoint.trans (coefficientProjection_ball R hg hgenus hΓ hfree hp ν').symm)

variable (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})

/-- The canonical identification of tangent fibres at equal original points is actual equality transport. -/
def canonicalTangentEquivOfPointEq {a b : TeichmullerSpace.{u, u} R} (_h : a = b) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    TangentSpace 𝓘(ℂ, E) a ≃L[ℂ] TangentSpace 𝓘(ℂ, E) b := by
  letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  exact tangentSpaceCast 𝓘(ℂ, E) a b

/-- At equal original points, the existing transport is Mathlib's actual tangent cast. -/
theorem canonicalTangentEquivOfPointEq_eq_tangentSpaceCast
    {a b : TeichmullerSpace.{u, u} R} (h : a = b) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth h =
      tangentSpaceCast 𝓘(ℂ, E) a b := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  subst b
  ext v
  rfl

/-- The actual chart differential respects equality transport of its actual point. -/
theorem canonicalBersTangentEquiv_pointEq {a b : TeichmullerSpace.{u, u} R} (h : a = b) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    ∀ v : TangentSpace 𝓘(ℂ, E) a,
      canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth b
        (canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth h v) =
      canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp hsmooth a v := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  subst b
  intro v
  rfl

/-- The derivative of the actual original coefficient projection reaches every tangent vector. -/
theorem coefficientProjection_mfderiv_surjective
    (ν : GammaMeasurableBeltrami.Ball Γ) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    Function.Surjective
      (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp) ν.val) := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  intro v
  obtain ⟨ξ, hξ⟩ :=
    (nonzeroDerivativeQuotientTangentEquiv R hp hg hgenus hΓ hfree ν hsmooth).surjective v
  obtain ⟨μ, rfl⟩ :=
    (Submodule.Quotient.mk_surjective (nonzeroInfinitesimalSubmodule R hp hg hgenus hΓ ν)) ξ
  exact ⟨μ, (nonzeroDerivativeQuotientTangentEquiv_apply_mk
    R hp hg hgenus hΓ hfree ν hsmooth μ).symm.trans hξ⟩

variable (ν ν' : GammaMeasurableBeltrami.Ball Γ)
    (hpoint : coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp ν =
      coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν')
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (P' : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν').map Hyperbolic.realSLMobius))
    (F' : Set ℍ) (hF' : Fuchsian.IsHalfPlaneFundamentalRegion P' F')

local notation "RY" => deformedNativeSurface R hgenus hΓ hp ν
local notation "pY" => deformedTargetCover R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "RY'" => deformedNativeSurface R hgenus hΓ hp ν'
local notation "pY'" => deformedTargetCover R hgenus hΓ hp ν'
local notation "hpY'" => deformedNativeSurface_uniformization R hgenus hΓ hp ν'

/-- The original tangent-to-harmonic equivalence has its literal single-base application formula. -/
theorem nonzeroTangentHarmonicEquiv_apply :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    ∀ v : TangentSpace 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val),
      nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth v =
        (NativePetersson.harmonicDerivativeEquiv RY P pY hpY F hF
          (deformedGroup_spec hΓ ν).1).symm
            ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm
              (canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g)
                hΓ hfree hp hsmooth
                (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g)
                  hΓ hfree hp ν.val) v)) := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  intro v
  rfl

/-- The one-base projection derivative has its proved weighted harmonic factorization. -/
theorem nonzeroTangentHarmonicEquiv_mfderiv_weighted
    (μ : GammaMeasurableBeltrami.Space Γ) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth
      (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp) ν.val μ) =
      (NativePetersson.harmonicDerivativeEquiv RY P pY hpY F hF
        (deformedGroup_spec hΓ ν).1).symm
          ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm
            (nonzeroBersDerivative R hp hg hgenus hΓ ν μ)) := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  have h := nonzeroTangentHarmonicEquiv_apply R hp hg hgenus hΓ hfree hsmooth ν P F hF
    (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, E)
      (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp) ν.val μ)
  exact h.trans (congrArg (fun φ : BersWeighted.Automorphic Γ =>
    (NativePetersson.harmonicDerivativeEquiv RY P pY hpY F hF
      (deformedGroup_spec hΓ ν).1).symm
        ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm φ))
    (canonicalBersTangentEquiv_mfderiv_coefficientProjection_nonzero
      R hg hgenus hΓ hfree hp hsmooth ν μ))

/-- The actual weighted derivative naturality also intertwines the existing harmonic inverses. -/
private theorem nativePointDeformedHarmonicEquiv_inverseBersDerivative_apply
    (φ : BersWeighted.Automorphic Γ) :
    nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint P F hF P' F' hF'
        ((NativePetersson.harmonicDerivativeEquiv RY P pY hpY F hF
          (deformedGroup_spec hΓ ν).1).symm
            ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm φ)) =
      (NativePetersson.harmonicDerivativeEquiv RY' P' pY' hpY' F' hF'
        (deformedGroup_spec hΓ ν').1).symm
          ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν').symm φ) := by
  have hc := congrArg (fun T : BersWeighted.Automorphic Γ →L[ℂ]
      BersWeighted.Automorphic (deformedGroup hΓ ν') => T φ)
    (nativePointDeformedBersEquiv_comp_inverseBersDerivativeEquiv_symm
      R hp hg hgenus hΓ hfree ν ν' hpoint)
  dsimp only [nativePointDeformedHarmonicEquiv, ContinuousLinearEquiv.trans_apply]
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact congrArg (NativePetersson.harmonicDerivativeEquiv RY' P' pY' hpY' F' hF'
    (deformedGroup_spec hΓ ν').1).symm hc

/-- Equal actual Bers derivatives give equal harmonic images of actual projection derivatives. -/
theorem nonzeroTangentHarmonicEquiv_coefficient_pair
    (μ μ' : GammaMeasurableBeltrami.Space Γ)
    (hderiv : nonzeroBersDerivative R hp hg hgenus hΓ ν μ =
      nonzeroBersDerivative R hp hg hgenus hΓ ν' μ') :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint P F hF P' F' hF'
      (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth
        (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, E)
          (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g)
            hΓ hfree hp) ν.val μ)) =
      nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν' P' F' hF' hsmooth
        (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, E)
          (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g)
            hΓ hfree hp) ν'.val μ') := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  have hν := nonzeroTangentHarmonicEquiv_mfderiv_weighted
    R hp hg hgenus hΓ hfree hsmooth ν P F hF μ
  have hν' := nonzeroTangentHarmonicEquiv_mfderiv_weighted
    R hp hg hgenus hΓ hfree hsmooth ν' P' F' hF' μ'
  exact (congrArg
    (nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint P F hF P' F' hF')
    hν).trans
      ((nativePointDeformedHarmonicEquiv_inverseBersDerivative_apply
        R hp hg hgenus hΓ hfree ν ν' hpoint P F hF P' F' hF'
        (nonzeroBersDerivative R hp hg hgenus hΓ ν μ)).trans
          ((congrArg (fun φ : BersWeighted.Automorphic Γ =>
            (NativePetersson.harmonicDerivativeEquiv RY' P' pY' hpY' F' hF'
              (deformedGroup_spec hΓ ν').1).symm
                ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν').symm φ)) hderiv).trans hν'.symm))

/-- The actual harmonic integral and inverse-coordinate derivative identify the
original deformed harmonic space with the original weighted Bers space. -/
def deformedHarmonicToOriginalBersEquiv :
    NativePetersson.Harmonic RY P pY hpY F hF ≃L[ℂ] BersWeighted.Automorphic Γ :=
  (NativePetersson.harmonicDerivativeEquiv RY P pY hpY F hF
    (deformedGroup_spec hΓ ν).1).trans
      (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν)

/-- The actual harmonic identification preserves the recovered original Bers vector. -/
theorem deformedHarmonicToOriginalBersEquiv_natural
    (η : NativePetersson.Harmonic RY P pY hpY F hF) :
    deformedHarmonicToOriginalBersEquiv R hp hg hgenus hΓ ν' P' F' hF'
      (nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
        P F hF P' F' hF' η) =
      deformedHarmonicToOriginalBersEquiv R hp hg hgenus hΓ ν P F hF η := by
  let K := deformedHarmonicToOriginalBersEquiv R hp hg hgenus hΓ ν P F hF
  let K' := deformedHarmonicToOriginalBersEquiv R hp hg hgenus hΓ ν' P' F' hF'
  apply K'.eq_symm_apply.mp
  have h := nativePointDeformedHarmonicEquiv_inverseBersDerivative_apply
    R hp hg hgenus hΓ hfree ν ν' hpoint P F hF P' F' hF' (K η)
  change nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
      P F hF P' F' hF' (K.symm (K η)) = K'.symm (K η) at h
  exact (congrArg
    (nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
      P F hF P' F' hF') (K.symm_apply_apply η)).symm.trans h

/-- Recovering the original weighted vector from the actual tangent harmonic
representative gives the actual canonical Bers chart differential. -/
theorem nonzeroTangentHarmonicEquiv_toOriginalBers :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    ∀ v : TangentSpace 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val),
      deformedHarmonicToOriginalBersEquiv R hp hg hgenus hΓ ν P F hF
        (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth v) =
      canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g)
        hΓ hfree hp hsmooth
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g)
          hΓ hfree hp ν.val) v := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  intro v
  apply (deformedHarmonicToOriginalBersEquiv R hp hg hgenus hΓ ν P F hF).eq_symm_apply.mp
  exact nonzeroTangentHarmonicEquiv_apply R hp hg hgenus hΓ hfree hsmooth ν P F hF v

/-- The induced map on the original tangent is independent of the coefficient representative,
under the true equality of its original point and the actual coefficient-identity harmonic isometry. -/
theorem nonzeroTangentHarmonicEquiv_natural :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    ∀ v : TangentSpace 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val),
      nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint P F hF P' F' hF'
        (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth v) =
      nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν' P' F' hF' hsmooth
        (canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth
          (coefficientProjection_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint) v) := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  intro v
  let J := canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth
    (coefficientProjection_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint)
  let f := canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
    (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val)
  let f' := canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
    (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν'.val)
  let φ : BersWeighted.Automorphic (deformedGroup hΓ ν) :=
    (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm (f v)
  let φ' : BersWeighted.Automorphic (deformedGroup hΓ ν') :=
    (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν').symm (f' (J v))
  have hφ : nativePointDeformedBersEquiv R hp hg hgenus hΓ hfree ν ν' hpoint φ = φ' := by
    have hc := congrArg (fun T : BersWeighted.Automorphic Γ →L[ℂ]
        BersWeighted.Automorphic (deformedGroup hΓ ν') => T (f v))
      (nativePointDeformedBersEquiv_comp_inverseBersDerivativeEquiv_symm
        R hp hg hgenus hΓ hfree ν ν' hpoint)
    have hf := canonicalBersTangentEquiv_pointEq R hp hg hgenus hΓ hfree hsmooth
      (coefficientProjection_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint) v
    exact hc.trans (congrArg (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν').symm hf.symm)
  have hν : (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth v).val =
      BersWeighted.ahlforsWeill φ :=
    (congrArg Subtype.val
      (nonzeroTangentHarmonicEquiv_apply R hp hg hgenus hΓ hfree hsmooth ν P F hF v)).trans
        (NativePetersson.harmonicDerivativeEquiv_symm_val_eq_ahlforsWeill
          RY P pY hpY F hF (deformedGroup_spec hΓ ν).1 φ)
  have hν' : (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree
      ν' P' F' hF' hsmooth (J v)).val = BersWeighted.ahlforsWeill φ' :=
    (congrArg Subtype.val
      (nonzeroTangentHarmonicEquiv_apply R hp hg hgenus hΓ hfree hsmooth
        ν' P' F' hF' (J v))).trans
          (NativePetersson.harmonicDerivativeEquiv_symm_val_eq_ahlforsWeill
            RY' P' pY' hpY' F' hF' (deformedGroup_spec hΓ ν').1 φ')
  apply Subtype.ext
  exact (nativePointDeformedHarmonicEquiv_val
    R hp hg hgenus hΓ hfree ν ν' hpoint P F hF P' F' hF'
    (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth v)).trans
      ((congrArg (nativePointDeformedCoefficientEquiv
        R hp hg hgenus hΓ hfree ν ν' hpoint) hν).trans
          ((nativePointDeformedCoefficientEquiv_ahlforsWeill
            R hp hg hgenus hΓ hfree ν ν' hpoint φ).trans
              ((congrArg (BersWeighted.ahlforsWeill (Γ := deformedGroup hΓ ν')) hφ).trans hν'.symm)))

/-- The original tangent harmonic maps have equal recovered vectors in the
original weighted Bers space under the actual equality transport of their point. -/
theorem nonzeroTangentHarmonicEquiv_recovered_natural :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    ∀ v : TangentSpace 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val),
      deformedHarmonicToOriginalBersEquiv R hp hg hgenus hΓ ν' P' F' hF'
        (nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint P F hF P' F' hF'
          (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth v)) =
      deformedHarmonicToOriginalBersEquiv R hp hg hgenus hΓ ν' P' F' hF'
        (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν' P' F' hF' hsmooth
          (canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth
            (coefficientProjection_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint) v)) := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  intro v
  exact congrArg
    (deformedHarmonicToOriginalBersEquiv R hp hg hgenus hΓ ν' P' F' hF')
    (nonzeroTangentHarmonicEquiv_natural
      R hp hg hgenus hΓ hfree hsmooth ν ν' hpoint P F hF P' F' hF' v)

/-- Naturality holds on every actual coefficient-projection derivative image. -/
theorem nonzeroTangentHarmonicEquiv_natural_projectionDerivative
    (μ : GammaMeasurableBeltrami.Space Γ) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint P F hF P' F' hF'
      (nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν P F hF hsmooth
        (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, E)
          (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g)
            hΓ hfree hp) ν.val μ)) =
      nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree ν' P' F' hF' hsmooth
        (canonicalTangentEquivOfPointEq R hp hg hgenus hΓ hfree hsmooth
          (coefficientProjection_eq_of_sameNativePoint R hp hg hgenus hΓ hfree ν ν' hpoint)
          (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, E)
            (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g)
              hΓ hfree hp) ν.val μ)) := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  exact nonzeroTangentHarmonicEquiv_natural
    R hp hg hgenus hΓ hfree hsmooth ν ν' hpoint P F hF P' F' hF'
      (mfderiv 𝓘(ℂ, GammaMeasurableBeltrami.Space Γ) 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g)
          hΓ hfree hp) ν.val μ)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
