module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaSourceCoefficient
public import LowDimensionalTopology.Geometry.Quasiconformal.BeltramiParameterDerivative
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S27_TeichmullerExistence

/-!
# Real first variation of the same symmetric normalized maps

The literal mirrored coefficient defines an actual full-plane L-infinity
direction with its original norm bound. The symmetric maps of the same
compatible scalar coefficients have the genuine real parameter derivative
and a locally uniform first-order limit throughout the plane.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- Mirroring the same compatible coefficient gives its actual plane
direction and the real first variation of the original symmetric maps.
The direction has arbitrary norm; subunit bounds are needed only near zero. -/
theorem exists_symmetric_native_real_parameter_variation
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (μ : GammaMeasurableBeltrami.Space Γ) :
    ∃ η : MeasurableBeltramiSpace,
      (η : ℂ → ℂ) =ᵐ[volume]
        LiZhongQC.s27u_symExt (GammaMeasurableBeltrami.planeRepresentative μ.val) ∧
      ‖η‖ ≤ ‖μ‖ ∧
      (∀ w : ℂ,
        HasDerivAt
          (fun t : ℝ => LiZhongQC.s27u_fSym
            (GammaMeasurableBeltrami.planeRepresentative ((t : ℂ) • μ).val) w)
          (Quasiconformal.firstVariation η w) 0) ∧
      TendstoLocallyUniformly
        (fun (t : ℝ) (w : ℂ) =>
          (LiZhongQC.s27u_fSym
            (GammaMeasurableBeltrami.planeRepresentative ((t : ℂ) • μ).val) w - w) /
              (t : ℂ))
        (Quasiconformal.firstVariation η) (𝓝[≠] (0 : ℝ)) := by
  classical
  let κ := GammaMeasurableBeltrami.planeRepresentative μ.val
  have hκ : LiZhongQC.IsBeltramiCoeff κ LiZhongQC.upperHalf ‖μ‖ :=
    GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val
  have hsym : LiZhongQC.IsBeltramiCoeff (LiZhongQC.s27u_symExt κ) univ ‖μ‖ :=
    LiZhongQC.s27u_b_s_beltrami hκ
  let η : MeasurableBeltramiSpace :=
    (MeasurableBeltramiBall.coefficientMemLp hsym).toLp (LiZhongQC.s27u_symExt κ)
  have hη : (η : ℂ → ℂ) =ᵐ[volume] LiZhongQC.s27u_symExt κ :=
    (MeasurableBeltramiBall.coefficientMemLp hsym).coeFn_toLp
  have hbound : ‖η‖ ≤ ‖μ‖ := by
    apply lpInfinity_norm_le_of_ae_bound η (norm_nonneg μ)
    have hb : ∀ᵐ z ∂volume, ‖LiZhongQC.s27u_symExt κ z‖ ≤ ‖μ‖ := by
      simpa only [Measure.restrict_univ] using hsym.2
    filter_upwards [hη, hb] with z hz hzb
    rw [hz]
    exact hzb
  have hmirror (t : ℝ) :
      LiZhongQC.s27u_symExt (fun z => (t : ℂ) * κ z) =
        fun z => (t : ℂ) * LiZhongQC.s27u_symExt κ z := by
    funext z
    by_cases hz : z.im < 0
    · simp only [LiZhongQC.s27u_symExt, ite_eq_left hz, map_mul, Complex.conj_ofReal]
    · simp only [LiZhongQC.s27u_symExt, ite_eq_right hz]
  have hscalar (t : ℝ) :
      GammaMeasurableBeltrami.planeRepresentative ((t : ℂ) • μ).val
        =ᵐ[volume.restrict LiZhongQC.upperHalf] (fun z => (t : ℂ) * κ z) := by
    change GammaMeasurableBeltrami.planeRepresentative ((t : ℂ) • μ.val)
      =ᵐ[volume.restrict LiZhongQC.upperHalf] (fun z => (t : ℂ) * κ z)
    filter_upwards [GammaMeasurableBeltrami.planeRepresentative_smul_ae (t : ℂ) μ.val] with z hz
    simpa only [κ, Pi.smul_apply, smul_eq_mul] using hz
  have hcoeff (t : ℝ) :
      LiZhongQC.IsBeltramiCoeff (fun z => (t : ℂ) * κ z) LiZhongQC.upperHalf
        (‖(t : ℂ)‖ * ‖μ‖) := by
    refine ⟨hκ.1.const_mul (t : ℂ), ?_⟩
    filter_upwards [hκ.2] with z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, ‖(t : ℂ)‖ * ‖μ‖ < 1 := by
    have ht : Tendsto (fun t : ℝ => ‖(t : ℂ)‖ * ‖μ‖) (𝓝 0) (𝓝 0) := by
      simpa only [Complex.ofReal_zero, norm_zero, zero_mul] using
        ((Complex.continuous_ofReal.norm.mul_const ‖μ‖).tendsto (0 : ℝ))
    exact ht.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))
  have hηsmall (t : ℝ) (ht : ‖(t : ℂ)‖ * ‖μ‖ < 1) : ‖(t : ℂ) • η‖ < 1 := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left hbound (norm_nonneg (t : ℂ))).trans_lt ht
  let B : ℝ → MeasurableBeltramiBall := fun t =>
    if ht : ‖(t : ℂ) • η‖ < 1 then
      ⟨(t : ℂ) • η, by simpa only [Metric.mem_ball, dist_zero_right] using ht⟩
    else ⟨0, by simp⟩
  have hBclass : ∀ᶠ t : ℝ in 𝓝 0, (B t).val = (t : ℂ) • η := by
    filter_upwards [hsmall] with t ht
    simp only [B, dite_eq_left (hηsmall t ht)]
  have hzero : (B 0).val = 0 := by
    simpa only [Complex.ofReal_zero, zero_smul] using hBclass.self_of_nhds
  have hε : Tendsto (fun _ : ℝ => (0 : MeasurableBeltramiSpace))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := tendsto_const_nhds
  have hdecomp : ∀ᶠ t : ℝ in 𝓝[≠] 0, (B t).val = (t : ℂ) • (η + 0) := by
    filter_upwards [hBclass.filter_mono nhdsWithin_le_nhds] with t ht
    simpa only [add_zero] using ht
  have hmaps : ∀ᶠ t : ℝ in 𝓝 0,
      (fun z => MeasurableBeltramiBall.normalizedSolution (B t) z) =
        LiZhongQC.s27u_fSym
          (GammaMeasurableBeltrami.planeRepresentative ((t : ℂ) • μ).val) := by
    filter_upwards [hsmall] with t ht
    have hBraw : ((B t).val : ℂ → ℂ) =ᵐ[volume]
        LiZhongQC.s27u_symExt (fun z => (t : ℂ) * κ z) := by
      have hclass : (B t).val = (t : ℂ) • η := by
        simp only [B, dite_eq_left (hηsmall t ht)]
      rw [hclass, hmirror t]
      filter_upwards [Lp.coeFn_smul (t : ℂ) η, hη] with z hsmul hz
      simpa only [Pi.smul_apply, smul_eq_mul, hz] using hsmul
    have hraw : (fun z => MeasurableBeltramiBall.normalizedSolution (B t) z) =
        LiZhongQC.s27u_fSym (fun z => (t : ℂ) * κ z) := by
      apply (LiZhongQC.s27u_sym_spec
        (mul_nonneg (norm_nonneg (t : ℂ)) (norm_nonneg μ)) ht (hcoeff t)).2.2.2
      exact MeasurableBeltramiBall.normalizedSolution_isNormalized_of_ae (B t) hBraw
    have hμt : ‖((t : ℂ) • μ).val‖ < 1 := by
      change ‖(t : ℂ) • μ‖ < 1
      simpa only [norm_smul] using ht
    have hsame := LiZhongQC.s27u_fSym_congr_ae
      (norm_nonneg ((t : ℂ) • μ).val) hμt
      (GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff ((t : ℂ) • μ).val)
      (mul_nonneg (norm_nonneg (t : ℂ)) (norm_nonneg μ)) ht (hcoeff t) (hscalar t)
    exact hraw.trans hsame.symm
  refine ⟨η, hη, hbound, ?_, ?_⟩
  · intro w
    have hd := Quasiconformal.normalizedSolution_real_parameter_hasDerivAt
      η hε B hdecomp hzero w
    apply hd.congr_of_eventuallyEq
    filter_upwards [hmaps] with t ht
    exact (congrFun ht w).symm
  · have hl := Quasiconformal.normalizedSolution_real_parameter_firstVariation
      η hε B hdecomp
    apply hl.congr_inseparable
    filter_upwards [hmaps.filter_mono nhdsWithin_le_nhds] with t ht
    intro w
    have hquot := congrArg (fun u : ℂ => (u - w) / (t : ℂ)) (congrFun ht w)
    exact Inseparable.of_eq hquot

end LowDimensionalTopology.Geometry.Teichmuller
