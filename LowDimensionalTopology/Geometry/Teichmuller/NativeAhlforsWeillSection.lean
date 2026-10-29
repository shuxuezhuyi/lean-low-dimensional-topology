module

public import LowDimensionalTopology.Geometry.Teichmuller.BersAutomorphicDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.NativeGammaSourceRealization

/-!
# The literal Ahlfors-Weill section in the original coefficient norm

A bounded holomorphic automorphic function on the lower half plane gives the
actual coefficient `-2 y² φ(conj z)` on the upper half plane. Its genuine native
L-infinity class satisfies every deck equation and defines a bounded complex
linear map. On the actual weighted ball of radius one half, its Bers projection
is the original function. This section supplies the coefficient input for the
inverse Bers-coordinate germ at a nonzero point.

The actual extension and source compatibility theorem use Wu Xiaobin's
LiZhongQC development, Apache-2.0, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- The original explicit coefficient of the Ahlfors-Weill section. -/
def ahlforsWeillCoefficient (φ : Automorphic Γ) (z : ℍ) : ℂ :=
  -2 * (z.im : ℂ) ^ 2 * (φ.toSource : ℂ → ℂ) (conj (z : ℂ))

theorem ahlforsWeillCoefficient_continuous (φ : Automorphic Γ) :
    Continuous (ahlforsWeillCoefficient φ) := by
  have hφ : Continuous (fun z : ℍ => (φ.toSource : ℂ → ℂ) (conj (z : ℂ))) := by
    apply φ.toSource.property.1.continuousOn.comp_continuous
      (Complex.continuous_conj.comp UpperHalfPlane.continuous_coe)
    intro z
    change (conj (z : ℂ)).im < 0
    rw [Complex.conj_im]
    exact neg_lt_zero.mpr z.im_pos
  exact (continuous_const.mul
    ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow 2)).mul hφ

/-- The coefficient bound uses the actual lower weighted supremum norm. -/
theorem norm_ahlforsWeillCoefficient_le (φ : Automorphic Γ) (z : ℍ) :
    ‖ahlforsWeillCoefficient φ z‖ ≤ 2 * ‖φ‖ := by
  have hz : conj (z : ℂ) ∈ LiZhongQC.lowerHalf := by
    change (conj (z : ℂ)).im < 0
    rw [Complex.conj_im]
    exact neg_lt_zero.mpr z.im_pos
  have hb := decode_weightedBound φ.val (conj (z : ℂ)) hz
  change ‖(φ.toSource : ℂ → ℂ) (conj (z : ℂ))‖ *
    (conj (z : ℂ)).im ^ 2 ≤ ‖φ‖ at hb
  rw [Complex.conj_im, neg_sq] at hb
  calc
    ‖ahlforsWeillCoefficient φ z‖ =
        2 * (‖(φ.toSource : ℂ → ℂ) (conj (z : ℂ))‖ * z.im ^ 2) := by
      simp only [ahlforsWeillCoefficient, norm_mul, norm_neg, norm_pow,
        Complex.norm_ofNat, Complex.norm_of_nonneg z.im_pos.le]
      ring
    _ ≤ 2 * ‖φ‖ := mul_le_mul_of_nonneg_left hb (by norm_num)

theorem ahlforsWeillCoefficient_memLp (φ : Automorphic Γ) :
    MemLp (ahlforsWeillCoefficient φ) (⊤ : ℝ≥0∞) (volume : Measure ℍ) :=
  memLp_top_of_bound (ahlforsWeillCoefficient_continuous φ).aestronglyMeasurable
    (2 * ‖φ‖) (Eventually.of_forall (norm_ahlforsWeillCoefficient_le φ))

/-- The literal coefficient represented in the original ambient infinity space. -/
def ahlforsWeillValue (φ : Automorphic Γ) : Ambient :=
  (ahlforsWeillCoefficient_memLp φ).toLp (ahlforsWeillCoefficient φ)

theorem ahlforsWeillValue_coe_ae (φ : Automorphic Γ) :
    ahlforsWeillValue φ =ᵐ[volume] ahlforsWeillCoefficient φ :=
  (ahlforsWeillCoefficient_memLp φ).coeFn_toLp

/-- The source's explicitly compatible planar coefficient has the same literal upper values. -/
theorem ahlforsWeillCoefficient_eq_source (φ : Automorphic Γ) (z : ℍ) :
    LiZhongQC.l333_mu (φ.toSource : ℂ → ℂ) z = ahlforsWeillCoefficient φ z := by
  exact indicator_of_mem (show (z : ℂ) ∈ LiZhongQC.upperHalf from z.im_pos)
    (fun w : ℂ => -2 * (w.im : ℂ) ^ 2 * (φ.toSource : ℂ → ℂ) (conj w))

/-- All original deck equations hold on the genuine coefficient class. -/
theorem ahlforsWeillValue_mem_compatible (φ : Automorphic Γ) :
    ahlforsWeillValue φ ∈ compatibleSubmodule Γ := by
  apply (mem_compatibleSubmodule_iff _).mpr
  intro γ hγ
  have hs := ae_plane_iff.mp (LiZhongQC.l333_mu_compat φ.toSource.property γ hγ)
  filter_upwards [ahlforsWeillValue_coe_ae φ,
    (measurePreserving_deck γ).quasiMeasurePreserving.ae (ahlforsWeillValue_coe_ae φ),
    hs] with z hz hγz he
  rw [hz, hγz]
  have hm : LiZhongQC.l333_mu (φ.toSource : ℂ → ℂ) ((γ • z : ℍ) : ℂ) =
      LiZhongQC.l333_mu (φ.toSource : ℂ → ℂ)
        (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) := by
    rw [LiZhongQC.h23l_b_coe_smul]
  rw [← hm, ahlforsWeillCoefficient_eq_source,
    ahlforsWeillCoefficient_eq_source] at he
  simpa only [phase, denominator, mul_comm] using he

/-- The original essential norm is bounded by twice the actual Bers norm. -/
theorem norm_ahlforsWeillValue_le (φ : Automorphic Γ) :
    ‖ahlforsWeillValue φ‖ ≤ 2 * ‖φ‖ := by
  apply lpInfinity_norm_le_of_ae_bound _ (mul_nonneg (by norm_num) (norm_nonneg φ))
  filter_upwards [ahlforsWeillValue_coe_ae φ] with z hz
  rw [hz]
  exact norm_ahlforsWeillCoefficient_le φ z

theorem ahlforsWeillCoefficient_add (φ ψ : Automorphic Γ) (z : ℍ) :
    ahlforsWeillCoefficient (φ + ψ) z =
      ahlforsWeillCoefficient φ z + ahlforsWeillCoefficient ψ z := by
  have hd := congrFun (map_add decodeLinearMap φ.val ψ.val) (conj (z : ℂ))
  change decode (φ.val + ψ.val) (conj (z : ℂ)) =
    decode φ.val (conj (z : ℂ)) + decode ψ.val (conj (z : ℂ)) at hd
  change -2 * (z.im : ℂ) ^ 2 * decode (φ.val + ψ.val) (conj (z : ℂ)) =
    -2 * (z.im : ℂ) ^ 2 * decode φ.val (conj (z : ℂ)) +
      -2 * (z.im : ℂ) ^ 2 * decode ψ.val (conj (z : ℂ))
  rw [hd, mul_add]

theorem ahlforsWeillCoefficient_smul (c : ℂ) (φ : Automorphic Γ) (z : ℍ) :
    ahlforsWeillCoefficient (c • φ) z = c * ahlforsWeillCoefficient φ z := by
  have hd := congrFun (map_smul decodeLinearMap c φ.val) (conj (z : ℂ))
  change decode (c • φ.val) (conj (z : ℂ)) =
    c * decode φ.val (conj (z : ℂ)) at hd
  change -2 * (z.im : ℂ) ^ 2 * decode (c • φ.val) (conj (z : ℂ)) =
    c * (-2 * (z.im : ℂ) ^ 2 * decode φ.val (conj (z : ℂ)))
  rw [hd]
  ring

/-- Evaluation of the actual section coefficient is linear on the weighted function space. -/
def ahlforsWeillEvaluationLinear (z : ℍ) : Automorphic Γ →ₗ[ℂ] ℂ where
  toFun φ := ahlforsWeillCoefficient φ z
  map_add' φ ψ := ahlforsWeillCoefficient_add φ ψ z
  map_smul' c φ := by
    simpa only [RingHom.id_apply, smul_eq_mul] using ahlforsWeillCoefficient_smul c φ z

/-- Point evaluation is bounded on the actual weighted automorphic space.
This evaluates its literal function, not an arbitrary L-infinity representative. -/
def ahlforsWeillEvaluation (z : ℍ) : Automorphic Γ →L[ℂ] ℂ :=
  (ahlforsWeillEvaluationLinear z).mkContinuous 2
    (fun φ => norm_ahlforsWeillCoefficient_le φ z)

@[simp] theorem ahlforsWeillEvaluation_apply (z : ℍ) (φ : Automorphic Γ) :
    ahlforsWeillEvaluation z φ = ahlforsWeillCoefficient φ z := rfl

/-- The literal section is complex-linear on the full bounded automorphic space. -/
def ahlforsWeillLinearMap : Automorphic Γ →ₗ[ℂ] Space Γ where
  toFun φ := ⟨ahlforsWeillValue φ, ahlforsWeillValue_mem_compatible φ⟩
  map_add' φ ψ := by
    apply Subtype.ext
    change ahlforsWeillValue (φ + ψ) = ahlforsWeillValue φ + ahlforsWeillValue ψ
    apply Lp.ext
    filter_upwards [ahlforsWeillValue_coe_ae (φ + ψ), ahlforsWeillValue_coe_ae φ,
      ahlforsWeillValue_coe_ae ψ, Lp.coeFn_add (ahlforsWeillValue φ) (ahlforsWeillValue ψ)]
      with z hφψ hφ hψ hadd
    simp only [Pi.add_apply] at hadd
    rw [hφψ, hadd, hφ, hψ, ahlforsWeillCoefficient_add]
  map_smul' c φ := by
    apply Subtype.ext
    change ahlforsWeillValue (c • φ) = c • ahlforsWeillValue φ
    apply Lp.ext
    filter_upwards [ahlforsWeillValue_coe_ae (c • φ), ahlforsWeillValue_coe_ae φ,
      Lp.coeFn_smul c (ahlforsWeillValue φ)] with z hcφ hφ hsmul
    simp only [Pi.smul_apply, smul_eq_mul] at hsmul
    rw [hcφ, hsmul, hφ, ahlforsWeillCoefficient_smul]

/-- The actual Ahlfors-Weill continuous complex-linear section, in unchanged native norms. -/
def ahlforsWeill : Automorphic Γ →L[ℂ] Space Γ :=
  ahlforsWeillLinearMap.mkContinuous 2 (fun φ => norm_ahlforsWeillValue_le φ)

@[simp] theorem ahlforsWeill_val (φ : Automorphic Γ) :
    (ahlforsWeill φ).val = ahlforsWeillValue φ := rfl

theorem ahlforsWeill_coe_ae (φ : Automorphic Γ) :
    (ahlforsWeill φ).val =ᵐ[volume] ahlforsWeillCoefficient φ :=
  ahlforsWeillValue_coe_ae φ

theorem norm_ahlforsWeill_le (φ : Automorphic Γ) : ‖ahlforsWeill φ‖ ≤ 2 * ‖φ‖ :=
  norm_ahlforsWeillValue_le φ

/-- The actual raw Bers supremum is bounded by the identical native weighted norm. -/
theorem Automorphic.bersNormL_toSource_le (φ : Automorphic Γ) :
    LiZhongQC.bersNormL (φ.toSource : ℂ → ℂ) ≤ ENNReal.ofReal ‖φ‖ := by
  unfold LiZhongQC.bersNormL
  refine iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal ?_
  exact decode_weightedBound φ.val z hz

/-- The genuine Bers projection of the literal section is the original automorphic function. -/
theorem automorphicProjection_ahlforsWeill (hΓ : LiZhongQC.IsFuchsian Γ)
    (φ : Automorphic Γ) (hφ : ‖φ‖ < 1 / 2) :
    automorphicProjection hΓ (ahlforsWeill φ) = φ := by
  have hμ : ‖ahlforsWeill φ‖ < 1 :=
    (norm_ahlforsWeill_le φ).trans_lt (by linarith)
  have hφB : LiZhongQC.bersNormL (φ.toSource : ℂ → ℂ) <
      ENNReal.ofReal (1 / 2 : ℝ) :=
    (Automorphic.bersNormL_toSource_le φ).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : 0 < (1 / 2 : ℝ))).mpr hφ)
  obtain ⟨μ, hcoeff, hBers⟩ :=
    (LiZhongQC.bers_small_ball_section hΓ).2 (φ.toSource : ℂ → ℂ) φ.toSource.property hφB
  let μB : Ball Γ :=
    ⟨ahlforsWeill φ, by simpa only [Metric.mem_ball, dist_zero_right] using hμ⟩
  have he : planeRepresentative (ahlforsWeill φ).val =ᵐ[
      volume.restrict LiZhongQC.upperHalf] μ.val.val := by
    apply ae_plane_iff.mpr
    filter_upwards [ahlforsWeill_coe_ae φ] with z hz
    rw [planeRepresentative_coe, hz, hcoeff z z.im_pos]
    rfl
  have hb := sourceBers_congr_ae (toSourceGamma μB) μ he
  change LiZhongQC.bersFunction (planeRepresentative (ahlforsWeill φ).val) =
    LiZhongQC.bersFunction μ.val.val at hb
  have hvalue : LiZhongQC.bersFunction (planeRepresentative (ahlforsWeill φ).val) =
      (φ.toSource : ℂ → ℂ) :=
    hb.trans ((LiZhongQC.bg_bersMapGamma_eq (μ := μ) rfl).symm.trans hBers)
  apply Subtype.ext
  apply lp.ext
  funext z
  change projection (ahlforsWeill φ) z = φ.val z
  rw [projection_apply_source _ hμ z, hvalue, Automorphic.toSource_apply, decode_coe]
  exact div_mul_cancel₀ _ (weight_ne_zero z)

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
