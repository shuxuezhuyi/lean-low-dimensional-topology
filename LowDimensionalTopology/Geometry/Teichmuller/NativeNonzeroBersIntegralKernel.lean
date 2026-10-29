/-
The original normalized solution, Bers function and automorphy APIs reuse
Wu Xiaobin's Li-Zhong-QC-formalization, pinned commit
1c0d5473c020b66ed5106331a38a61536760b9b2, under Apache 2.0.
All normalized maps in the formula are the nonsymmetric zero-extension maps.
-/
module

public import LowDimensionalTopology.Geometry.Quasiconformal.NonsymmetricBersDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.NativeNonzeroBersDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersFiniteEvaluations
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric MeasureTheory Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

variable {Γ : Subgroup GammaMeasurableBeltrami.Deck}

/-- Actual point evaluation is continuous in the original weighted Bers norm. -/
def lowerEvaluation (z : Lower) : Automorphic Γ →L[ℂ] ℂ :=
  (lowerEvaluationLinear z).mkContinuous (z.val.im ^ 2)⁻¹ fun φ => by
    have hw : 0 < z.val.im ^ 2 := sq_pos_of_ne_zero (ne_of_lt z.property)
    have hb := decode_weightedBound φ.val z.val z.property
    change ‖lowerEvaluationLinear z φ‖ * z.val.im ^ 2 ≤ ‖φ‖ at hb
    calc
      ‖lowerEvaluationLinear z φ‖ ≤ ‖φ‖ / z.val.im ^ 2 := (le_div_iff₀ hw).mpr hb
      _ = (z.val.im ^ 2)⁻¹ * ‖φ‖ := by rw [div_eq_mul_inv, mul_comm]

@[simp] theorem lowerEvaluation_apply (z : Lower) (φ : Automorphic Γ) :
    lowerEvaluation z φ = (φ.toSource : ℂ → ℂ) z := rfl

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The literal raw affine representative retains the actual group equations. -/
private def sourceGammaOfAffine (μ : Ball Γ) (η : Space Γ) (t : ℂ)
    (ht : ‖μ.val.val‖ + ‖t‖ * ‖η.val‖ < 1) : LiZhongQC.BeltramiGamma Γ := by
  have hm := planeRepresentative_isBeltramiCoeff_univ μ.val.val
  have hη := planeRepresentative_isBeltramiCoeff_univ η.val
  refine ⟨⟨fun ζ => planeRepresentative μ.val.val ζ + t * planeRepresentative η.val ζ,
    ⟨⟨‖μ.val.val‖ + ‖t‖ * ‖η.val‖, by positivity, ht,
      hm.1.add (hη.1.const_mul t), ?_⟩, ?_⟩⟩, ?_⟩
  · filter_upwards [hm.2, hη.2] with ζ hμζ hηζ
    calc
      ‖planeRepresentative μ.val.val ζ + t * planeRepresentative η.val ζ‖ ≤
          ‖planeRepresentative μ.val.val ζ‖ + ‖t‖ * ‖planeRepresentative η.val ζ‖ := by
        rw [← norm_mul]
        exact norm_add_le _ _
      _ ≤ _ := add_le_add hμζ (mul_le_mul_of_nonneg_left hηζ (norm_nonneg t))
  · intro ζ hζ
    change planeRepresentative μ.val.val ζ + t * planeRepresentative η.val ζ = 0
    rw [planeRepresentative_off μ.val.val (not_lt.mpr hζ),
      planeRepresentative_off η.val (not_lt.mpr hζ), mul_zero, add_zero]
  · intro γ hγ
    filter_upwards [planeRepresentative_isGammaCompatible μ.val γ hγ,
      planeRepresentative_isGammaCompatible η γ hγ] with ζ hμζ hηζ
    change planeRepresentative μ.val.val ζ + t * planeRepresentative η.val ζ =
      (planeRepresentative μ.val.val
          (((γ 0 0 : ℂ) * ζ + γ 0 1) / ((γ 1 0 : ℂ) * ζ + γ 1 1)) +
        t * planeRepresentative η.val
          (((γ 0 0 : ℂ) * ζ + γ 0 1) / ((γ 1 0 : ℂ) * ζ + γ 1 1))) * _
    rw [hμζ, hηζ]
    ring

/-- The actual native affine family has the same Bers values as the literal
affine raw representatives, by genuine a.e. representative independence. -/
theorem automorphicProjection_affine_eventually (hΓ : LiZhongQC.IsFuchsian Γ)
    (μ : Ball Γ) (η : Space Γ) (z : BersWeighted.Lower) :
    ∀ᶠ t : ℂ in 𝓝 0,
      BersWeighted.lowerEvaluation z (BersWeighted.automorphicProjection hΓ (μ.val + t • η)) =
        LiZhongQC.bersFunction
          (fun ζ => planeRepresentative μ.val.val ζ + t * planeRepresentative η.val ζ) z := by
  have hμ : ‖μ.val.val‖ < 1 := by
    change ‖μ.val‖ < 1
    exact Ball.norm_lt_one μ
  have hnear : ∀ᶠ t : ℂ in 𝓝 0, ‖μ.val.val‖ + ‖t‖ * ‖η.val‖ < 1 :=
    (isOpen_lt (continuous_const.add (continuous_norm.mul continuous_const))
      continuous_const).mem_nhds (by
        change ‖μ.val.val‖ + ‖(0 : ℂ)‖ * ‖η.val‖ < 1
        simpa only [norm_zero, zero_mul, add_zero] using hμ)
  filter_upwards [hnear] with t ht
  have hu : ‖μ.val + t • η‖ < 1 := by
    calc
      ‖μ.val + t • η‖ ≤ ‖μ.val‖ + ‖t • η‖ := norm_add_le _ _
      _ = ‖μ.val.val‖ + ‖t‖ * ‖η.val‖ := by rw [norm_smul]; rfl
      _ < 1 := ht
  let u : Ball Γ := ⟨μ.val + t • η, mem_ball_zero_iff.mpr hu⟩
  let v := sourceGammaOfAffine μ η t ht
  have hae : planeRepresentative (μ.val + t • η).val =ᵐ[volume.restrict LiZhongQC.upperHalf]
      fun ζ => planeRepresentative μ.val.val ζ + t * planeRepresentative η.val ζ := by
    have hs : (t • η).val = t • η.val := SetLike.val_smul (compatibleClosedSubmodule Γ) t η
    filter_upwards [BersWeighted.planeRepresentative_add_ae μ.val (t • η),
      planeRepresentative_smul_ae t η.val] with ζ hadd hsmul
    rw [hs] at hadd
    exact hadd.trans (congrArg (fun w : ℂ => planeRepresentative μ.val.val ζ + w)
      (by simpa only [Pi.smul_apply, smul_eq_mul] using hsmul))
  change ((BersWeighted.automorphicProjection hΓ (μ.val + t • η)).toSource : ℂ → ℂ) z = _
  exact (BersWeighted.automorphicProjection_toSource hΓ (μ.val + t • η) hu z.property).trans
    (congrFun (sourceBers_congr_ae (toSourceGamma u) v hae) z)

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces
open Quasiconformal.CanonicalBersVariation

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)

/-- The already genuine full Frechet derivative has the literal original
nonsymmetric arbitrary-base kernel in every original compatible direction. -/
theorem nonzeroBersDerivative_integral (hΓ : LiZhongQC.IsFuchsian Γ)
    (μ : Ball Γ) (η : Space Γ) {z : ℂ} (hz : z ∈ LiZhongQC.lowerHalf) :
    ((nonzeroBersDerivative R hp hg hgenus hΓ μ η).toSource : ℂ → ℂ) z =
      (-(6 / Real.pi : ℂ) * ∫ ζ in LiZhongQC.upperHalf,
        planeRepresentative η.val ζ * LiZhongQC.dz (baseMap (toSourceGamma μ).val) ζ ^ 2 /
          (baseMap (toSourceGamma μ).val ζ - baseMap (toSourceGamma μ).val z) ^ 4) *
        deriv (baseMap (toSourceGamma μ).val) z ^ 2 := by
  let zz : BersWeighted.Lower := ⟨z, hz⟩
  have hline : HasDerivAt (fun t : ℂ => μ.val + t • η) η 0 := by
    change HasFDerivAtFilter (fun t : ℂ => μ.val + t • η)
      (ContinuousLinearMap.toSpanSingleton ℂ η) (𝓝 (0 : ℂ) ×ˢ pure (0 : ℂ))
    refine HasFDerivAtFilter.of_isLittleOTVS
      ((Asymptotics.IsLittleOTVS.zero _ _).congr_left ?_)
    intro q
    simp only [Pi.zero_apply, ContinuousLinearMap.toSpanSingleton_apply,
      add_sub_add_left_eq_sub, sub_smul, sub_self]
  have hpderiv := hasFDerivAt_automorphicProjection_nonzero R hp hg hgenus hΓ μ
  have he : HasFDerivAt
      (fun v : Space Γ => BersWeighted.lowerEvaluation zz (BersWeighted.automorphicProjection hΓ v))
      ((BersWeighted.lowerEvaluation zz).comp (nonzeroBersDerivative R hp hg hgenus hΓ μ)) μ.val :=
    (BersWeighted.lowerEvaluation zz).hasFDerivAt.comp μ.val hpderiv
  have hd := he.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
  have hs := hasDerivAt_bersFunction_affine (toSourceGamma μ).val
    (norm_nonneg η.val) (planeRepresentative_isBeltramiCoeff_univ η.val)
    (fun ζ hζ => planeRepresentative_off η.val (not_lt.mpr hζ)) hz
  have hs' := hs.congr_of_eventuallyEq (automorphicProjection_affine_eventually hΓ μ η zz)
  exact hd.unique hs'

/-- Full native Frechet differentiability and the actual integral formula are
both present, together with absolute integrability for every original direction. -/
theorem automorphicProjection_frechet_integral (hΓ : LiZhongQC.IsFuchsian Γ) (μ : Ball Γ) :
    HasFDerivAt (BersWeighted.automorphicProjection hΓ)
      (nonzeroBersDerivative R hp hg hgenus hΓ μ) μ.val ∧
      ∀ (η : Space Γ) (z : ℂ), z ∈ LiZhongQC.lowerHalf →
        IntegrableOn (fun ζ => planeRepresentative η.val ζ *
            LiZhongQC.dz (baseMap (toSourceGamma μ).val) ζ ^ 2 /
              (baseMap (toSourceGamma μ).val ζ - baseMap (toSourceGamma μ).val z) ^ 4)
          LiZhongQC.upperHalf ∧
        ((nonzeroBersDerivative R hp hg hgenus hΓ μ η).toSource : ℂ → ℂ) z =
          (-(6 / Real.pi : ℂ) * ∫ ζ in LiZhongQC.upperHalf,
            planeRepresentative η.val ζ * LiZhongQC.dz (baseMap (toSourceGamma μ).val) ζ ^ 2 /
              (baseMap (toSourceGamma μ).val ζ - baseMap (toSourceGamma μ).val z) ^ 4) *
            deriv (baseMap (toSourceGamma μ).val) z ^ 2 := by
  refine ⟨hasFDerivAt_automorphicProjection_nonzero R hp hg hgenus hΓ μ, ?_⟩
  intro η z hz
  exact ⟨(fourthKernel_change_of_variables (toSourceGamma μ).val (norm_nonneg η.val)
      (planeRepresentative_isBeltramiCoeff_univ η.val)
      (fun ζ hζ => planeRepresentative_off η.val (not_lt.mpr hζ)) hz).1,
    nonzeroBersDerivative_integral R hp hg hgenus hΓ μ η hz⟩

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
