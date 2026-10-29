/-
Released under Apache 2.0 license as described in the file LICENSE.
The analytic Cauchy-transform and Hilbert-transform results used below are due to
Wu Xiaobin, from Li-Zhong-QC-formalization commit
1c0d5473c020b66ed5106331a38a61536760b9b2. The fixed external source retains
its author and license records. This module proves the normalization bridges
using those public results and Mathlib's public derivative and integration APIs.
-/
module
public import LowDimensionalTopology.External.LiZhongQC.Ch02.S11_IntegralOperators
public import Mathlib.Tactic.Ring

/-!
# A normalized Cauchy potential for smooth compactly supported input

The difference of the two Cauchy kernels occurs inside the actual integral.
For continuous compactly supported input the integrand is integrable, and the
potential equals the ordinary Cauchy transform minus its value at zero.
For smooth compactly supported input its actual Wirtinger derivatives are the
input and the Hilbert transform, with the exact L2 norm identity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The normalization is imposed inside the actual Cauchy integral. -/
def normalizedCauchyPotential (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(1 / (Real.pi : ℂ)) * ∫ ζ, h ζ * (1 / (ζ - z) - 1 / ζ)

private theorem normalizedCauchyPotential_integrand_eq (h : ℂ → ℂ) (z : ℂ) :
    (fun ζ => h ζ * (1 / (ζ - z) - 1 / ζ)) =
      fun ζ => h ζ / (ζ - z) - h ζ / (ζ - (0 : ℂ)) := by
  funext ζ
  simp only [mul_sub, mul_one_div, sub_zero]

/-- Each singular Cauchy kernel is integrable against continuous compact input,
so their difference inside the normalized integral is genuinely integrable. -/
theorem normalizedCauchyPotential_integrand_integrable {h : ℂ → ℂ}
    (hh : Continuous h) (hc : HasCompactSupport h) (z : ℂ) :
    Integrable (fun ζ => h ζ * (1 / (ζ - z) - 1 / ζ)) volume := by
  rw [normalizedCauchyPotential_integrand_eq]
  exact (LiZhongQC.integrable_div_sub_of_hasCompactSupport hh hc z).sub
    (LiZhongQC.integrable_div_sub_of_hasCompactSupport hh hc 0)

/-- The normalized integral is exactly the Cauchy transform with its value at zero
subtracted; both ordinary kernel integrals are integrable. -/
theorem normalizedCauchyPotential_eq_cauchyT_sub {h : ℂ → ℂ}
    (hh : Continuous h) (hc : HasCompactSupport h) (z : ℂ) :
    normalizedCauchyPotential h z = LiZhongQC.cauchyT h z - LiZhongQC.cauchyT h 0 := by
  have hz := LiZhongQC.integrable_div_sub_of_hasCompactSupport hh hc z
  have hzero := LiZhongQC.integrable_div_sub_of_hasCompactSupport hh hc 0
  unfold normalizedCauchyPotential LiZhongQC.cauchyT
  rw [normalizedCauchyPotential_integrand_eq, integral_sub hz hzero]
  ring

/-- The normalized potential vanishes at zero, for every input function. -/
@[simp] theorem normalizedCauchyPotential_zero (h : ℂ → ℂ) :
    normalizedCauchyPotential h 0 = 0 := by
  simp [normalizedCauchyPotential]

/-- Subtracting the value at zero leaves the actual real Fréchet derivative unchanged. -/
theorem normalizedCauchyPotential_fderiv {h : ℂ → ℂ}
    (hh : Continuous h) (hc : HasCompactSupport h) (z : ℂ) :
    fderiv ℝ (normalizedCauchyPotential h) z = fderiv ℝ (LiZhongQC.cauchyT h) z := by
  have heq : normalizedCauchyPotential h =
      fun w => LiZhongQC.cauchyT h w - LiZhongQC.cauchyT h 0 :=
    funext (normalizedCauchyPotential_eq_cauchyT_sub hh hc)
  rw [heq, fderiv_sub_const]

/-- A C1 compactly supported input gives an actual C1 normalized potential. -/
theorem normalizedCauchyPotential_contDiff {h : ℂ → ℂ}
    (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) :
    ContDiff ℝ 1 (normalizedCauchyPotential h) := by
  have heq : normalizedCauchyPotential h =
      fun w => LiZhongQC.cauchyT h w - LiZhongQC.cauchyT h 0 :=
    funext (normalizedCauchyPotential_eq_cauchyT_sub hh.continuous hc)
  rw [heq]
  exact (LiZhongQC.contDiff_cauchyT hh hc).sub contDiff_const

/-- The actual antiholomorphic derivative of the smooth normalized potential is its input. -/
theorem normalizedCauchyPotential_dzbar {h : ℂ → ℂ}
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (z : ℂ) :
    LiZhongQC.dzbar (normalizedCauchyPotential h) z = h z := by
  have hd := ((LiZhongQC.eq11_17 hh hc).2 z).1
  simpa only [LiZhongQC.dzbar, normalizedCauchyPotential_fderiv hh.continuous hc z] using hd

/-- The actual holomorphic derivative is the pointwise smooth Hilbert transform. -/
theorem normalizedCauchyPotential_dz {h : ℂ → ℂ}
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (z : ℂ) :
    LiZhongQC.dz (normalizedCauchyPotential h) z = LiZhongQC.hilbertHSmooth h z := by
  have hd := ((LiZhongQC.eq11_17 hh hc).2 z).2
  simpa only [LiZhongQC.dz, normalizedCauchyPotential_fderiv hh.continuous hc z] using hd

/-- The derivative agrees almost everywhere with the actual L2 Hilbert-transform representative. -/
theorem normalizedCauchyPotential_dz_ae {h : ℂ → ℂ}
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    LiZhongQC.dz (normalizedCauchyPotential h) =ᵐ[volume] LiZhongQC.hilbertH h := by
  filter_upwards [LiZhongQC.hilbertH_eq_ae_smooth hh hc] with z hz
  exact (normalizedCauchyPotential_dz hh hc z).trans hz.symm

/-- The holomorphic derivative has exactly the input's L2 norm, by the actual Hilbert isometry. -/
theorem normalizedCauchyPotential_dz_eLpNorm_two {h : ℂ → ℂ}
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    eLpNorm (LiZhongQC.dz (normalizedCauchyPotential h)) 2 volume = eLpNorm h 2 volume := by
  have hmem : MemLp h 2 volume := hh.continuous.memLp_of_hasCompactSupport (μ := volume) hc
  calc
    eLpNorm (LiZhongQC.dz (normalizedCauchyPotential h)) 2 volume =
        eLpNorm (LiZhongQC.hilbertH h) 2 volume :=
      eLpNorm_congr_ae (normalizedCauchyPotential_dz_ae hh hc)
    _ = eLpNorm h 2 volume := LiZhongQC.thm11_3_isometry hmem

end LowDimensionalTopology.Geometry.Quasiconformal
