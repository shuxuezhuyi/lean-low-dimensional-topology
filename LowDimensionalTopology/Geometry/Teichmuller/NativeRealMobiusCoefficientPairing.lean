module

public import LowDimensionalTopology.Geometry.Teichmuller.CoefficientRealMobiusIsometry
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Tactic.Ring

/-!
# The actual Beltrami–quadratic pairing under a real Möbius change

The native coefficient phase cancels the quadratic fourth denominator to
give the real Jacobian. The equality holds on each actual measurable region
of the upper half-plane, for every quadratic coefficient function, without
an integrability premise.

The coefficient and change-of-variable APIs reuse Wu Xiaobin's Li-Zhong-QC
formalization, Apache-2.0, pinned commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open GammaMeasurableBeltrami

/-- The same actual native coefficient and quadratic pullbacks preserve their
literal pairing on the corresponding measurable image region. -/
theorem coefficientQuadraticPairing_realMobius
    (Γ : Subgroup Deck) (Q : Deck) (μQ : Space (LiZhongQC.conjGroup Γ Q))
    {F : Set ℂ} (hFH : F ⊆ LiZhongQC.upperHalf) (hFm : MeasurableSet F)
    (φQ : ℂ → ℂ) :
    LiZhongQC.beltramiPairing F
      (planeRepresentative (coefficientRealMobiusIsometry Γ Q μQ).val)
      (fun z => φQ (LiZhongQC.h36p_m Q z) / ((Q 1 0 : ℂ) * z + Q 1 1) ^ 4) =
      LiZhongQC.beltramiPairing (LiZhongQC.h36p_m Q '' F)
        (planeRepresentative μQ.val) φQ := by
  have hκ : ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf),
      planeRepresentative (coefficientRealMobiusIsometry Γ Q μQ).val z =
        planeRepresentative μQ.val (LiZhongQC.h36p_m Q z) *
          (((Q 1 0 : ℂ) * z + Q 1 1) ^ 2 /
            conj (((Q 1 0 : ℂ) * z + Q 1 1) ^ 2)) := by
    apply ae_plane_iff.mpr
    filter_upwards [coefficientRealMobiusIsometry_coe_ae Γ Q μQ] with z hz
    rw [planeRepresentative_coe, LiZhongQC.h36p_m_coe, planeRepresentative_coe]
    change (coefficientRealMobiusIsometry Γ Q μQ).val z =
      μQ.val (Q • z) * phase Q z
    exact hz.trans (mul_comm _ _)
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hFm
    (fun z hz => ((LiZhongQC.h36p_m_hasDerivAt Q (hFH hz)).hasFDerivAt.restrictScalars
      ℝ).hasFDerivWithinAt)
    ((LiZhongQC.h36p_m_injOn Q).mono hFH)
    (fun z => planeRepresentative μQ.val z * φQ z)
  unfold LiZhongQC.beltramiPairing
  rw [hcv]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hFH hκ,
    ae_restrict_mem hFm] with z hκz hz
  have hden : (Q 1 0 : ℂ) * z + Q 1 1 ≠ 0 :=
    denominator_ne_zero Q ⟨z, hFH hz⟩
  have hcancel := LiZhongQC.h36p_b_compat_alg
    (a := φQ (LiZhongQC.h36p_m Q z)) hden hκz
  calc
    _ = (‖(Q 1 0 : ℂ) * z + Q 1 1‖⁻¹ ^ 4 : ℝ) •
        (planeRepresentative μQ.val (LiZhongQC.h36p_m Q z) *
          φQ (LiZhongQC.h36p_m Q z)) := hcancel
    _ = _ := by
      simp only [LiZhongQC.det_restrictScalars_toSpanSingleton]
      rw [abs_of_nonneg (sq_nonneg _), norm_div, norm_one, norm_pow]
      congr 1
      ring

end LowDimensionalTopology.Geometry.Teichmuller
