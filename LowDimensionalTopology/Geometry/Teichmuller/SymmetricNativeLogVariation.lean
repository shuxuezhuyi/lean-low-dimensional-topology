module

public import LowDimensionalTopology.Geometry.Teichmuller.SymmetricNativeBeltramiVariation
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Real logarithmic variation of the same symmetric maps

At the positive dilation parameter, the actual symmetric scalar family has
its ordinary real logarithmic derivative. The zero coefficient gives the
identity map, so the logarithmic base value at exp(2*s) is exactly 2*s.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- The same mirror direction gives the actual real logarithmic derivative
of the original symmetric maps at the full positive dilation, with its
kernel variation divided by that dilation. -/
theorem exists_symmetric_native_real_log_derivative
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (μ : GammaMeasurableBeltrami.Space Γ) (s : ℝ) (hs : 0 < s) :
    let lam := Real.exp (2 * s)
    ∃ η : MeasurableBeltramiSpace,
      (η : ℂ → ℂ) =ᵐ[volume]
        LiZhongQC.s27u_symExt (GammaMeasurableBeltrami.planeRepresentative μ.val) ∧
      ‖η‖ ≤ ‖μ‖ ∧
      1 < lam ∧
      Real.log ((LiZhongQC.s27u_fSym
        (GammaMeasurableBeltrami.planeRepresentative ((0 : ℂ) • μ).val)
          (lam : ℂ)).re) = 2 * s ∧
      HasDerivAt
        (fun t : ℝ => Real.log ((LiZhongQC.s27u_fSym
          (GammaMeasurableBeltrami.planeRepresentative ((t : ℂ) • μ).val)
            (lam : ℂ)).re))
        ((Quasiconformal.firstVariation η (lam : ℂ)).re / lam) 0 := by
  let lam := Real.exp (2 * s)
  let F : ℝ → ℂ → ℂ := fun t => LiZhongQC.s27u_fSym
    (GammaMeasurableBeltrami.planeRepresentative ((t : ℂ) • μ).val)
  obtain ⟨η, hη, hbound, hd, _⟩ := exists_symmetric_native_real_parameter_variation μ
  have hplaneZero : GammaMeasurableBeltrami.planeRepresentative
      (0 : GammaMeasurableBeltrami.Ambient)
        =ᵐ[volume.restrict LiZhongQC.upperHalf] (0 : ℂ → ℂ) := by
    apply GammaMeasurableBeltrami.ae_plane_iff.mpr
    filter_upwards [Lp.coeFn_zero ℂ (⊤ : ℝ≥0∞) (volume : Measure ℍ)] with z hz
    simpa only [GammaMeasurableBeltrami.planeRepresentative_coe, Pi.zero_apply] using hz
  have hzeroCoeff : LiZhongQC.IsBeltramiCoeff (0 : ℂ → ℂ) LiZhongQC.upperHalf 0 :=
    ⟨aestronglyMeasurable_const, Filter.Eventually.of_forall fun _ => by simp⟩
  have hplaneCoeff : LiZhongQC.IsBeltramiCoeff
      (GammaMeasurableBeltrami.planeRepresentative (0 : GammaMeasurableBeltrami.Ambient))
        LiZhongQC.upperHalf 0 := by
    simpa only [norm_zero] using
      GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff
        (0 : GammaMeasurableBeltrami.Ambient)
  have hmirrorZero : LiZhongQC.s27u_symExt (0 : ℂ → ℂ) = 0 := by
    funext z
    simp only [LiZhongQC.s27u_symExt, Pi.zero_apply, map_zero, ite_self]
  have hrawZero : LiZhongQC.s27u_fSym (0 : ℂ → ℂ) = id := by
    rw [LiZhongQC.s27u_fSym, hmirrorZero, LiZhongQC.bB_l_normalizedSolution_zero]
  have hsymZero : LiZhongQC.s27u_fSym
      (GammaMeasurableBeltrami.planeRepresentative (0 : GammaMeasurableBeltrami.Ambient))
        = id := by
    have h := LiZhongQC.s27u_fSym_congr_ae (le_refl (0 : ℝ)) zero_lt_one hplaneCoeff
      (le_refl (0 : ℝ)) zero_lt_one hzeroCoeff hplaneZero
    exact h.trans hrawZero
  have hFzero : F 0 = id := by
    simpa only [F, Complex.ofReal_zero, zero_smul, ZeroMemClass.coe_zero] using hsymZero
  have hvalue : (F 0 (lam : ℂ)).re = lam := by
    rw [hFzero]
    rfl
  have hlam : 1 < lam :=
    Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) hs)
  have hreal : HasDerivAt (fun t : ℝ => (F t (lam : ℂ)).re)
      (Quasiconformal.firstVariation η (lam : ℂ)).re 0 := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have h := (Complex.continuous_re.tendsto _).comp
      (hd (lam : ℂ)).tendsto_slope_zero
    refine Filter.Tendsto.congr (fun t : ℝ => ?_) h
    change (t⁻¹ • (F (0 + t) (lam : ℂ) - F 0 (lam : ℂ))).re =
      t⁻¹ • ((F (0 + t) (lam : ℂ)).re - (F 0 (lam : ℂ)).re)
    rw [Complex.smul_re, Complex.sub_re]
  have hnonzero : (F 0 (lam : ℂ)).re ≠ 0 := by
    rw [hvalue]
    exact ne_of_gt (zero_lt_one.trans hlam)
  have hbase : Real.log ((F 0 (lam : ℂ)).re) = 2 * s := by
    rw [hvalue]
    exact Real.log_exp (2 * s)
  refine ⟨η, hη, hbound, hlam, hbase, ?_⟩
  have hlog := hreal.log hnonzero
  rw [hvalue] at hlog
  exact hlog

end LowDimensionalTopology.Geometry.Teichmuller
