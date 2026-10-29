module

public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HyperbolicExamples
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.PoincareLineElement
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The half-plane Poincaré line element

The native upper half-plane carries the real coordinate tensor `|dz|² / (Im z)²`.
We reuse the existing hyperbolic length density, prove real smoothness and positive
definiteness, and identify this tensor with the actual Cayley pullback of the disk
tensor. This is the standard-model calculation in Imayoshi–Taniguchi, Chapter III,
printed page 53; LearningMath, printed page 675, gives the same Cayley calculation.
-/

@[expose] public section
noncomputable section

open scoped Manifold ContDiff InnerProductSpace UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The half-plane metric uses the square of the existing hyperbolic length density. -/
def halfPlanePoincareTensor (z : ℍ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  hyperbolicDensity z ^ 2 • innerSL ℝ

/-- The literal tensor coefficient is the reciprocal square of the imaginary part. -/
theorem halfPlanePoincareTensor_eq_inv_sq (z : ℍ) :
    halfPlanePoincareTensor z = (z.im ^ 2)⁻¹ • innerSL ℝ := by
  simp [halfPlanePoincareTensor, hyperbolicDensity, one_div, inv_pow]

theorem halfPlanePoincareTensor_apply (z : ℍ) (v w : ℂ) :
    halfPlanePoincareTensor z v w = hyperbolicDensity z ^ 2 * ⟪v, w⟫_ℝ := rfl

/-- Symmetry holds on the real tangent coordinate space. -/
theorem halfPlanePoincareTensor_symmetric (z : ℍ) (v w : ℂ) :
    halfPlanePoincareTensor z v w = halfPlanePoincareTensor z w v := by
  rw [halfPlanePoincareTensor_apply, halfPlanePoincareTensor_apply, real_inner_comm v w]

/-- The diagonal value is exactly `|v|² / (Im z)²`. -/
theorem halfPlanePoincareTensor_self (z : ℍ) (v : ℂ) :
    halfPlanePoincareTensor z v v = ‖v‖ ^ 2 / z.im ^ 2 := by
  rw [halfPlanePoincareTensor_apply, real_inner_self_eq_norm_sq]
  simp only [hyperbolicDensity, div_pow, one_pow]
  ring

/-- Positive definiteness follows from the prescribed density. -/
theorem halfPlanePoincareTensor_pos (z : ℍ) {v : ℂ} (hv : v ≠ 0) :
    0 < halfPlanePoincareTensor z v v := by
  rw [halfPlanePoincareTensor_apply]
  exact mul_pos (sq_pos_of_pos (hyperbolicDensity_pos z)) (real_inner_self_pos.mpr hv)

/-- Real smoothness is taken in the existing global inclusion chart of the half-plane. -/
theorem contMDiff_halfPlanePoincareTensor :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞ halfPlanePoincareTensor := by
  let : IsManifold 𝓘(ℝ, ℂ) ∞ ℍ :=
    UpperHalfPlane.isOpenEmbedding_coe.isManifold_singleton
  have hc : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ((↑) : ℍ → ℂ) :=
    fun _ => contMDiffAt_extChartAt
  have hi : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun z : ℍ => z.im) :=
    Complex.imCLM.contMDiff.comp hc
  let k : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := innerSL ℝ
  have hk : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
      (fun _ : ℍ => k) := contMDiff_const
  change ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
    (fun z : ℍ => hyperbolicDensity z ^ 2 • k)
  simpa only [hyperbolicDensity, one_div, Pi.smul_def'] using
    ((hi.inv₀ fun z => z.im_ne_zero).pow 2).smul hk

/-- Squaring the actual Cayley differential's length identity gives the diagonal pullback. -/
theorem cayley_discPoincareTensor_self (z : ℍ) (v : ℂ) :
    discPoincareTensor (cayleyFormula z)
      (((2 * Complex.I) / ((z : ℂ) + Complex.I) ^ 2) * v)
      (((2 * Complex.I) / ((z : ℂ) + Complex.I) ^ 2) * v) =
        halfPlanePoincareTensor z v v := by
  rw [discPoincareTensor_self, halfPlanePoincareTensor_self]
  have h := congrArg (fun t : ℝ => t ^ 2) (cayley_weighted_tangent_norm z v)
  simpa only [div_pow, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using h

/-- The actual Cayley derivative pulls back both slots of the disk tensor to the half-plane
tensor; the identity is proved rather than supplied as an isometry assumption. -/
theorem cayley_discPoincareTensor_pullback (z : ℍ) (v w : ℂ) :
    discPoincareTensor (cayleyFormula z)
      (((2 * Complex.I) / ((z : ℂ) + Complex.I) ^ 2) * v)
      (((2 * Complex.I) / ((z : ℂ) + Complex.I) ^ 2) * w) =
        halfPlanePoincareTensor z v w := by
  have h := cayley_discPoincareTensor_self z (v + w)
  simp only [mul_add, map_add, add_apply] at h
  rw [discPoincareTensor_symmetric (cayleyFormula z)
    (((2 * Complex.I) / ((z : ℂ) + Complex.I) ^ 2) * w)
    (((2 * Complex.I) / ((z : ℂ) + Complex.I) ^ 2) * v),
    halfPlanePoincareTensor_symmetric z w v] at h
  linarith [cayley_discPoincareTensor_self z v, cayley_discPoincareTensor_self z w]

/-- The same pullback identity, expressed using the derivative of the specified Cayley map. -/
theorem cayley_deriv_discPoincareTensor_pullback (z : ℍ) (v w : ℂ) :
    discPoincareTensor (cayleyFormula z)
      (deriv cayleyFormula (z : ℂ) * v) (deriv cayleyFormula (z : ℂ) * w) =
        halfPlanePoincareTensor z v w := by
  rw [(hasDerivAt_cayleyFormula z).deriv]
  exact cayley_discPoincareTensor_pullback z v w

end LowDimensionalTopology.Geometry.Hyperbolic
