module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertRadialProfile
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Scaling the finite inverse-norm disc potential

Rotation invariance and real dilation reduce the two-pole disc potential
to one fixed radial profile. Both changes of variables use the original
Lebesgue measure on the complex plane.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped Pointwise

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- The finite disc potential with a second pole at `a`. -/
def inverseNormDiscPotential (R : ℝ) (a : ℂ) : ℂ :=
  ∫ t in Metric.ball (0 : ℂ) R, inverseNormKernel t * inverseNormKernel (a - t)

theorem integrableOn_inverseNormDiscPotential {R : ℝ} (hR : 0 < R)
    {a : ℂ} (ha : a ≠ 0) :
    IntegrableOn (fun t : ℂ => inverseNormKernel t * inverseNormKernel (a - t))
      (Metric.ball (0 : ℂ) R) := by
  have h := integrableOn_inverseNormKernel_mul_ball hR ha.symm
  convert h using 1
  funext t
  simp only [sub_zero]
  rw [show inverseNormKernel (a - t) = inverseNormKernel (t - a) by
    simp only [inverseNormKernel, norm_sub_rev]]

/-- Simultaneously rotating the second pole and the integration variable
preserves the disc potential. -/
theorem inverseNormDiscPotential_rotation (u : Circle) (R : ℝ) (a : ℂ) :
    inverseNormDiscPotential R ((u : ℂ) * a) = inverseNormDiscPotential R a := by
  let e : ℂ ≃ₗᵢ[ℝ] ℂ := rotation u
  have hp : e ⁻¹' Metric.ball (0 : ℂ) R = Metric.ball (0 : ℂ) R := by
    simpa only [map_zero] using e.preimage_ball (0 : ℂ) R
  have hc := e.measurePreserving.setIntegral_preimage_emb
    e.toHomeomorph.isClosedEmbedding.measurableEmbedding
    (fun t : ℂ => inverseNormKernel t * inverseNormKernel ((u : ℂ) * a - t))
    (Metric.ball (0 : ℂ) R)
  rw [hp] at hc
  have hcomp : (fun t : ℂ => inverseNormKernel (e t) *
      inverseNormKernel ((u : ℂ) * a - e t)) =
        fun t : ℂ => inverseNormKernel t * inverseNormKernel (a - t) := by
    funext t
    change (‖(u : ℂ) * t‖ : ℂ)⁻¹ * (‖(u : ℂ) * a - (u : ℂ) * t‖ : ℂ)⁻¹ = _
    rw [← mul_sub]
    simp only [norm_mul, Circle.norm_coe, one_mul]
    rfl
  rw [hcomp] at hc
  exact hc.symm

/-- Dilation cancels its two-dimensional Jacobian against the two inverse
distances. -/
theorem inverseNormDiscPotential_ofReal {ρ : ℝ} (hρ : 0 < ρ) (R : ℝ) :
    inverseNormDiscPotential R (ρ : ℂ) = inverseNormUnitPoleDiscPotential (R / ρ) := by
  have hset : ρ • Metric.ball (0 : ℂ) (R / ρ) = Metric.ball (0 : ℂ) R := by
    rw [_root_.smul_ball hρ.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hρ]
    congr 1
    field_simp
  have hchange := Measure.setIntegral_comp_smul_of_pos (volume : Measure ℂ)
    (fun t : ℂ => inverseNormKernel t * inverseNormKernel ((ρ : ℂ) - t))
    (Metric.ball (0 : ℂ) (R / ρ)) hρ
  rw [hset, Complex.finrank_real_complex] at hchange
  have hpoint : (fun t : ℂ => inverseNormKernel (ρ • t) *
      inverseNormKernel ((ρ : ℂ) - ρ • t)) =
        fun t : ℂ => (ρ ^ 2)⁻¹ • inverseNormUnitPoleProduct t := by
    have hscale (v : ℂ) : inverseNormKernel (ρ • v) =
        (ρ : ℂ)⁻¹ * inverseNormKernel v := by
      unfold inverseNormKernel
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, Complex.ofReal_mul, mul_inv_rev]
      exact mul_comm _ _
    funext t
    have hshift : (ρ : ℂ) - ρ • t = ρ • ((1 : ℂ) - t) := by
      simp only [Complex.real_smul]
      ring
    rw [hshift, hscale t, hscale (1 - t), Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_pow, ← inv_pow, inverseNormUnitPoleProduct]
    ring
  rw [hpoint, integral_smul] at hchange
  have hnonzero : (((ρ ^ 2)⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hρ.ne'))
  apply Eq.symm
  apply mul_left_cancel₀ hnonzero
  simpa only [inverseNormUnitPoleDiscPotential, inverseNormDiscPotential,
    Complex.real_smul] using hchange

/-- The actual finite disc integral reduces to the fixed unit-pole
profile at the scaled radius. -/
theorem inverseNormDiscPotential_eq_profile {a : ℂ} (ha : a ≠ 0) (R : ℝ) :
    inverseNormDiscPotential R a = inverseNormUnitPoleDiscPotential (R / ‖a‖) := by
  have hρ : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let u : Circle := ⟨a / (‖a‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ, div_self hρ.ne']⟩
  have hua : (u : ℂ) * (‖a‖ : ℂ) = a := by
    dsimp [u]
    exact div_mul_cancel₀ a (Complex.ofReal_ne_zero.mpr hρ.ne')
  calc
    inverseNormDiscPotential R a = inverseNormDiscPotential R (‖a‖ : ℂ) := by
      calc
        inverseNormDiscPotential R a =
            inverseNormDiscPotential R ((u : ℂ) * (‖a‖ : ℂ)) :=
          congrArg (inverseNormDiscPotential R) hua.symm
        _ = inverseNormDiscPotential R (‖a‖ : ℂ) :=
          inverseNormDiscPotential_rotation u R (‖a‖ : ℂ)
    _ = inverseNormUnitPoleDiscPotential (R / ‖a‖) := inverseNormDiscPotential_ofReal hρ R

end LowDimensionalTopology.Geometry.Quasiconformal
