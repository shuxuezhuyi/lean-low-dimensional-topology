module

public import LowDimensionalTopology.Geometry.Teichmuller.MeasurableBeltrami
public import LowDimensionalTopology.External.LiZhongQC.Ch04.S16_Quasicircles

/-!
# Inversion conjugates of the actual canonical plane solution

Conjugation by reciprocal maps is genuinely quasiconformal across the
removable point zero. Its actual dilatation defines a coefficient class
with the same infinity bound, and normalized uniqueness identifies the
same reciprocal-conjugated map with that class's canonical solution.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Geometry.Teichmuller

/-- The literal reciprocal conjugate is another actual canonical solution,
with coefficient norm bounded by the same original coefficient norm. -/
theorem normalizedSolution_inversion_exists (μ : MeasurableBeltramiBall) :
    ∃ ν : MeasurableBeltramiBall, ‖ν.val‖ ≤ ‖μ.val‖ ∧
      ∀ z : ℂ, MeasurableBeltramiBall.normalizedSolution ν z =
        (MeasurableBeltramiBall.normalizedSolution μ z⁻¹)⁻¹ := by
  let F := MeasurableBeltramiBall.normalizedSolution μ
  let k : ℝ := ‖μ.val‖
  let K : ℝ := (1 + k) / (1 - k)
  let η : ℂ → ℂ := complexDilatation (nxInvConj F)
  have hk0 : 0 ≤ k := norm_nonneg _
  have hk1 : k < 1 := MeasurableBeltramiBall.norm_lt_one μ
  have hF := MeasurableBeltramiBall.normalizedSolution_spec μ
  obtain ⟨hH, hG0, hpunct⟩ := ahI_f2_homeo hF.2.1 hF.1.2.1 hF.1.2.2.1
  have hG : IsKQC (nxInvConj F) univ K := b4_isKQC_univ_of_punctured hH hpunct
  have hratio : (K - 1) / (K + 1) = k := by
    have hd : 1 - k ≠ 0 := (sub_pos.mpr hk1).ne'
    have hn : (1 + k) - (1 - k) = 2 * k := by ring
    have hm : (1 + k) + (1 - k) = 2 := by ring
    dsimp only [K]
    rw [div_sub_one hd, div_add_one hd, div_div_div_cancel_right₀ hd,
      hn, hm, mul_div_cancel_left₀ _ two_ne_zero]
  have hη : IsBeltramiCoeff η univ k := by
    have hcoeff : IsBeltramiCoeff
        (complexDilatation (nxInvConj F)) univ ((K - 1) / (K + 1)) :=
      (thm10_2_genHomeoSolution_of_isKQC hG).1
    rw [hratio] at hcoeff
    exact hcoeff
  let ν := MeasurableBeltramiBall.ofCoefficient hk0 hk1 hη
  have hν : (ν.val : ℂ → ℂ) =ᵐ[volume] η :=
    MeasurableBeltramiBall.ofCoefficient_coe_ae hk0 hk1 hη
  have hνnorm : ‖ν.val‖ ≤ k := by
    apply lpInfinity_norm_le_of_ae_bound ν.val hk0
    have hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖η z‖ ≤ k := by
      simpa only [Measure.restrict_univ] using hη.2
    filter_upwards [hν, hb] with z hz hbound
    rw [hz]
    exact hbound
  have hF1 : F 1 = 1 := hF.1.2.2.2.1
  have hG1 : nxInvConj F 1 = 1 := by
    simp only [nxInvConj, inv_one, hF1]
  have hGn : IsNormalizedSolution (nxInvConj F) η :=
    ⟨⟨K, hG⟩, hH.2.2.1, hG0, hG1, EventuallyEq.rfl⟩
  obtain ⟨E, hE⟩ := nxI1_exists_homeo F hF.1.2.2.1
  have hEn : IsNormalizedSolution E η := by simpa only [hE] using hGn
  have hcanonical := MeasurableBeltramiBall.normalizedSolution_eq_of_ae ν hν E hEn
  refine ⟨ν, hνnorm, ?_⟩
  intro z
  rw [hcanonical]
  exact congrFun hE z

end LowDimensionalTopology.Geometry.Quasiconformal
