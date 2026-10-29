module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeBergmanProjection

/-!
# Bounds and projection identities for the original Bergman integral

The estimate keeps the original weighted essential norm. The integral is
linear on every original measurable automorphic input and fixes every
holomorphic automorphic coefficient on the original compact surface.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter MeasureTheory
open scoped ENNReal UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadratic

open Surfaces QuadraticBergman GammaMeasurableBeltrami

section RawInputs

variable {Γ : Subgroup Deck} (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict LiZhongQC.upperHalf))
    (ha : ∀ A ∈ Γ, ∀ z ∈ LiZhongQC.upperHalf,
      f (LiZhongQC.h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = f z)
    (hb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf),
      ‖f z‖ * z.im ^ 2 ≤ M)

include hf ha hb

/-- Every original input has a uniform output bound in its exact weighted essential norm. -/
theorem bergman_weighted_bound {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    ‖bergman f z‖ * z.im ^ 2 ≤
      (2 * BersWeighted.kernelConstant) * weightedEssNorm (fun z : ℍ => f z) := by
  have hz' : conj z ∈ LiZhongQC.lowerHalf := by
    change (conj z).im < 0
    rw [Complex.conj_im]
    exact neg_lt_zero.mpr hz
  have h := BersWeighted.bersDerivative_weighted_bound
    (planeRepresentative_isBeltramiCoeff (bergmanInput f hf ha hb).val).2 hz'
  rw [Complex.conj_im, neg_sq, ClosedSubmodule.norm_coe,
    norm_bergmanInput f hf ha hb] at h
  have htwo : ‖(-2 : ℂ)‖ = (2 : ℝ) := by norm_num
  calc
    _ = 2 * (‖LiZhongQC.bersDerivative
        (planeRepresentative (bergmanInput f hf ha hb).val) (conj z)‖ * z.im ^ 2) := by
      rw [bergman_eq_bers f hf ha hb z, norm_mul, htwo, Complex.norm_conj]
      ring
    _ ≤ 2 * (BersWeighted.kernelConstant * weightedEssNorm (fun z : ℍ => f z)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

/-- Additivity uses the genuine absolute convergence of both original summands. -/
theorem bergman_add (g : ℂ → ℂ)
    (hg : AEStronglyMeasurable g (volume.restrict LiZhongQC.upperHalf))
    (hga : ∀ A ∈ Γ, ∀ z ∈ LiZhongQC.upperHalf,
      g (LiZhongQC.h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = g z)
    (hgb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf),
      ‖g z‖ * z.im ^ 2 ≤ M) {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    bergman (f + g) z = bergman f z + bergman g z := by
  unfold bergman
  simp_rw [Pi.add_apply, mul_add, add_mul]
  exact integral_add (bergman_integrable f hf ha hb hz)
    (bergman_integrable g hg hga hgb hz)

end RawInputs

/-- Scalar linearity retains the literal integral, even without convergence assumptions. -/
theorem bergman_smul (a : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    bergman (a • f) z = a * bergman f z := by
  unfold bergman
  calc
    _ = ∫ ζ in LiZhongQC.upperHalf,
        a * ((ζ.im : ℂ) ^ 2 * f ζ * conj (halfPlaneQuadraticKernel z ζ)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ζ => by
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
    _ = _ := integral_const_mul _ _

section OriginalSurface

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

include hp

/-- Every original holomorphic automorphic coefficient is fixed, with no extra bound premise. -/
theorem bergman_eq_self_of_differentiable (φ : ℂ → ℂ)
    (hφ : DifferentiableOn ℂ φ LiZhongQC.upperHalf)
    (hφΓ : ∀ A ∈ Γ, ∀ z ∈ LiZhongQC.upperHalf,
      φ (LiZhongQC.h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = φ z) :
    EqOn (bergman φ) φ LiZhongQC.upperHalf := by
  intro z hz
  exact (automorphicQuadratic_reproducing_kernel R p hp φ hφ hφΓ z hz).2.symm

/-- The same integral fixes the actual lift of every original global quadratic differential. -/
theorem bergman_uniformizedQuadratic
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    EqOn (bergman (uniformizedQuadratic R p q))
      (uniformizedQuadratic R p q) LiZhongQC.upperHalf := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  apply bergman_eq_self_of_differentiable R p hp
  · exact LiZhongQC.utm_liftQD_differentiableOn q.property hp
  · exact uniformizedQuadratic_automorphic R p hp q

end OriginalSurface

end LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadratic
