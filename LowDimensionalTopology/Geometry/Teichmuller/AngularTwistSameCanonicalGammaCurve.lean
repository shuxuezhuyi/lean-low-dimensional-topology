module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistNativeInfinitesimal
public import LowDimensionalTopology.Geometry.Teichmuller.BersAutomorphicDerivative
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# The same given angular coefficient curve in the compatible Banach space

The given full-plane ball family retains its literal angular coefficients.
Encoding those same coefficients gives a compatible ball curve for every
real parameter. Its exact scalar identity gives its actual Banach derivative
and the genuine weighted Bers derivative, without choosing another family.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- Encode the SAME given plane family as a genuine compatible ball curve.
Its derivative is the SAME entire infinitesimal class, and its actual
weighted Bers derivative is the native Frechet derivative on that class. -/
theorem exists_same_canonical_gamma_curve
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) (hΓ : LiZhongQC.IsFuchsian Γ)
    (ν : GammaMeasurableBeltrami.Space Γ)
    (hν : (ν.val : ℍ → ℂ) =ᵐ[volume]
      (fun z : ℍ => rightCosetInfinitesimalSum θ Γ s (z : ℂ)))
    (μP : ℝ → MeasurableBeltramiBall)
    (hμP : ∀ t : ℝ, ((μP t).val : ℂ → ℂ) =ᵐ[volume]
      rightCosetCoefficientSum θ Γ s t) :
    let := NormedSpace.restrictScalars ℝ ℂ (GammaMeasurableBeltrami.Space Γ)
    let : SeminormedAddCommGroup (BersWeighted.Automorphic Γ) :=
      (BersWeighted.automorphicSubmodule Γ).normedAddCommGroup.toSeminormedAddCommGroup
    letI nR : NormedSpace ℝ (BersWeighted.Automorphic Γ) :=
      NormedSpace.restrictScalars ℝ ℂ (BersWeighted.Automorphic Γ)
    let := IsScalarTower.restrictScalars ℝ ℂ (GammaMeasurableBeltrami.Space Γ)
    let := IsScalarTower.restrictScalars ℝ ℂ (BersWeighted.Automorphic Γ)
    let : AddCommGroup (BersWeighted.Automorphic Γ) :=
      (BersWeighted.automorphicSubmodule Γ).normedAddCommGroup.toAddCommGroup
    let : Module ℝ (BersWeighted.Automorphic Γ) :=
      nR.toModule
    let : TopologicalSpace (BersWeighted.Automorphic Γ) :=
      (
        (inferInstance : NormedAddCommGroup (BersWeighted.Automorphic Γ)).toMetricSpace
      ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    let : ContinuousSMul ℝ (BersWeighted.Automorphic Γ) := IsScalarTower.continuousSMul ℂ
    ∃ μG : ℝ → GammaMeasurableBeltrami.Ball Γ,
      (∀ t : ℝ,
        GammaMeasurableBeltrami.planeRepresentative (μG t).val.val
          =ᵐ[volume.restrict LiZhongQC.upperHalf] ((μP t).val : ℂ → ℂ)) ∧
      (∀ t : ℝ, (μG t).val =
        ((t : ℂ) / (1 - (t : ℂ) * infinitesimalScale θ)) • ν) ∧
      (μG 0).val = 0 ∧
      HasDerivAt (fun t : ℝ => (μG t).val) ν 0 ∧
      HasDerivAt
        (fun t : ℝ => BersWeighted.automorphicProjection hΓ (μG t).val)
        (fderiv ℂ (BersWeighted.automorphicProjection hΓ) 0 ν) 0 := by
  let := NormedSpace.restrictScalars ℝ ℂ (GammaMeasurableBeltrami.Space Γ)
  let : SeminormedAddCommGroup (BersWeighted.Automorphic Γ) :=
    (BersWeighted.automorphicSubmodule Γ).normedAddCommGroup.toSeminormedAddCommGroup
  let nR : NormedSpace ℝ (BersWeighted.Automorphic Γ) :=
    NormedSpace.restrictScalars ℝ ℂ (BersWeighted.Automorphic Γ)
  let := IsScalarTower.restrictScalars ℝ ℂ (GammaMeasurableBeltrami.Space Γ)
  let := IsScalarTower.restrictScalars ℝ ℂ (BersWeighted.Automorphic Γ)
  let : AddCommGroup (BersWeighted.Automorphic Γ) :=
    (BersWeighted.automorphicSubmodule Γ).normedAddCommGroup.toAddCommGroup
  let : Module ℝ (BersWeighted.Automorphic Γ) :=
    nR.toModule
  let : TopologicalSpace (BersWeighted.Automorphic Γ) :=
    (
      (inferInstance : NormedAddCommGroup (BersWeighted.Automorphic Γ)).toMetricSpace
    ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : ContinuousSMul ℝ (BersWeighted.Automorphic Γ) := IsScalarTower.continuousSMul ℂ
  let lam : ℝ → ℂ := fun t => (t : ℂ) / (1 - (t : ℂ) * infinitesimalScale θ)
  have hraw (t : ℝ) : LiZhongQC.IsBeltramiCoeff (rightCosetCoefficientSum θ Γ s t)
      LiZhongQC.upperHalf ‖(μP t).val‖ := by
    have hp := (planar_isBeltramiCoeff_congr_ae (hμP t)).mp
      (MeasurableBeltramiSpace.isBeltramiCoeff (μP t).val)
    have hm : AEStronglyMeasurable (rightCosetCoefficientSum θ Γ s t) volume := by
      simpa only [Measure.restrict_univ] using hp.1
    have hb : ∀ᵐ z ∂volume, ‖rightCosetCoefficientSum θ Γ s t z‖ ≤ ‖(μP t).val‖ := by
      simpa only [Measure.restrict_univ] using hp.2
    exact ⟨hm.restrict, ae_restrict_of_ae hb⟩
  let μG : ℝ → GammaMeasurableBeltrami.Ball Γ := fun t =>
    GammaMeasurableBeltrami.ofCoefficientBall (norm_nonneg (μP t).val)
      (MeasurableBeltramiBall.norm_lt_one (μP t)) (hraw t)
      (isGammaCompatible_rightCosetCoefficientSum θ Γ s t)
  have hG (t : ℝ) : ((μG t).val.val : ℍ → ℂ) =ᵐ[volume]
      (fun z : ℍ => rightCosetCoefficientSum θ Γ s t (z : ℂ)) :=
    GammaMeasurableBeltrami.ofCoefficient_coe_ae (hraw t)
      (isGammaCompatible_rightCosetCoefficientSum θ Γ s t)
  have hsame (t : ℝ) : GammaMeasurableBeltrami.planeRepresentative (μG t).val.val
      =ᵐ[volume.restrict LiZhongQC.upperHalf] ((μP t).val : ℂ → ℂ) := by
    apply GammaMeasurableBeltrami.ae_plane_iff.mpr
    have hP := GammaMeasurableBeltrami.ae_plane_iff.mp (ae_restrict_of_ae (hμP t))
    filter_upwards [hG t, hP] with z hgz hpz
    rw [GammaMeasurableBeltrami.planeRepresentative_coe, hgz]
    exact hpz.symm
  have hclass (t : ℝ) : (μG t).val = lam t • ν := by
    apply Subtype.ext
    rw [SetLike.val_smul (GammaMeasurableBeltrami.compatibleClosedSubmodule Γ)]
    apply Lp.ext
    filter_upwards [hG t, Lp.coeFn_smul (lam t) ν.val, hν] with z hgz hsmul hnz
    have hscalar : rightCosetCoefficientSum θ Γ s t (z : ℂ) =
        lam t * rightCosetInfinitesimalSum θ Γ s (z : ℂ) :=
      rightCosetCoefficientSum_eq_scalar θ Γ s t (z : ℂ)
    rw [hgz, hscalar]
    simpa only [Pi.smul_apply, smul_eq_mul, hnz] using hsmul.symm
  have hzero : (μG 0).val = 0 := by
    rw [hclass 0]
    simp only [lam, Complex.ofReal_zero, zero_mul, sub_zero, zero_div, zero_smul]
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) 0 :=
    Complex.ofRealCLM.hasDerivAt
  have hden : HasDerivAt (fun t : ℝ => 1 - (t : ℂ) * infinitesimalScale θ)
      (-infinitesimalScale θ) 0 := by
    simpa only [one_mul] using HasDerivAt.const_sub (1 : ℂ)
      (hid.mul_const (infinitesimalScale θ))
  have hlam : HasDerivAt lam (1 : ℂ) (0 : ℝ) := by
    simpa [lam] using hid.fun_div hden (by simp)
  have hderiv : HasDerivAt (fun t : ℝ => (μG t).val) ν 0 := by
    have h := hlam.smul_const ν
    simpa only [← hclass, one_smul] using h
  have hB := (BersWeighted.hasFDerivAt_projection (Γ := Γ)).restrictScalars ℝ
  have hBcurve := hB.comp_hasDerivAt_of_eq (0 : ℝ) hderiv hzero.symm
  have hlim := hBcurve.tendsto_slope_zero
  simp only [ContinuousLinearMap.coe_restrictScalars'] at hlim
  refine ⟨μG, hsame, hclass, hzero, hderiv, ?_⟩
  rw [BersWeighted.fderiv_automorphicProjection]
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply tendsto_subtype_rng.mpr
  rw [BersWeighted.automorphicIntegralOperator_val]
  let incl : BersWeighted.Automorphic Γ →L[ℝ] BersWeighted.Target :=
    (BersWeighted.automorphicSubmodule Γ).subtypeL.restrictScalars ℝ
  refine Filter.Tendsto.congr (fun t : ℝ => ?_) hlim
  have hsmul := (incl.map_smul (t⁻¹)
    (BersWeighted.automorphicProjection hΓ (μG t).val -
      BersWeighted.automorphicProjection hΓ (μG 0).val)).symm
  simpa only [incl, ContinuousLinearMap.coe_restrictScalars', Submodule.subtypeL_apply,
    Submodule.coe_sub, BersWeighted.automorphicProjection_val, Function.comp_apply,
    zero_add] using hsmul

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
