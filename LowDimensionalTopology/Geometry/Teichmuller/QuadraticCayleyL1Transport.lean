module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanCayleyEquivalence
public import LowDimensionalTopology.Geometry.Teichmuller.PoincareKernelSeries

/-!
# Unweighted L¹ transport of quadratic Cayley pullbacks

The original coefficient functions, multiplied by the square of the actual
Cayley derivative, preserve their unweighted absolute planar integrals. The
proof uses the established conformal Jacobian change of variables, not a
weighted L² norm. Every integrable holomorphic disc seed consequently supplies
the existing half-plane Poincare series with absolute and compact-uniform
convergence on its entire actual transformation group.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller.QuadraticCayleyL1

open LiZhongQC Hyperbolic Mobius WeightedQuadraticBergman

/-- The original unweighted absolute area is preserved by inverse quadratic pullback. -/
theorem inverseCayleyPullback_phiArea (ψ : ℂ → ℂ) :
    phiArea (inverseCayleyPullback ψ) (Metric.ball (0 : ℂ) 1) =
      phiArea ψ upperHalf := by
  have hS : IsConformalOnto inverseCayleyFormula (Metric.ball (0 : ℂ) 1)
      (inverseCayleyFormula '' Metric.ball (0 : ℂ) 1) := by
    refine ⟨?_, inverseCayley_injOn_disk, rfl⟩
    intro z hz
    exact (hasDerivAt_inverseCayleyFormula
      (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz))).differentiableAt.differentiableWithinAt
  have hpull : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      inverseCayleyPullback ψ z =
        ψ (inverseCayleyFormula z) * deriv inverseCayleyFormula z ^ 2 := by
    intro z hz
    exact congrArg (fun d : ℂ => ψ (inverseCayleyFormula z) * d ^ 2)
      (hasDerivAt_inverseCayleyFormula
        (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz))).deriv.symm
  simpa only [inverseCayley_image_disk, upperHalf] using
    (phiArea_conformal_invariant (φ := inverseCayleyPullback ψ) (ψ := ψ)
      (h := inverseCayleyFormula) Metric.isOpen_ball hS hpull)

/-- Forward quadratic pullback preserves the same unweighted absolute area. -/
theorem cayleyPullback_phiArea (φ : ℂ → ℂ) :
    phiArea (cayleyPullback φ) upperHalf = phiArea φ (Metric.ball (0 : ℂ) 1) := by
  calc
    phiArea (cayleyPullback φ) upperHalf =
        phiArea (inverseCayleyPullback (cayleyPullback φ)) (Metric.ball (0 : ℂ) 1) :=
      (inverseCayleyPullback_phiArea (cayleyPullback φ)).symm
    _ = phiArea φ (Metric.ball (0 : ℂ) 1) := by
      unfold phiArea
      exact setLIntegral_congr_fun measurableSet_ball fun z hz =>
        congrArg (fun a : ℂ => ENNReal.ofReal ‖a‖)
          (inverseCayleyPullback_cayleyPullback φ hz)

/-- Every original integrable holomorphic disc seed gives a normally convergent
half-plane Poincare series on the whole actual projective group. -/
theorem halfPlane_convergence_of_disk_seed
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (hΓ : IsFuchsian Γ)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hfA : phiArea f (Metric.ball (0 : ℂ) 1) < ⊤) :
    (∀ z ∈ upperHalf, Summable (fun g : Γ.map realSLMobius =>
      ‖ProjectivePoincare.term Γ (cayleyPullback f) g z‖)) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ upperHalf →
      TendstoUniformlyOn
        (fun s : Finset (Γ.map realSLMobius) => fun z =>
          ∑ g ∈ s, ProjectivePoincare.term Γ (cayleyPullback f) g z)
        (ProjectivePoincare.series Γ (cayleyPullback f)) atTop K) := by
  have hU : DifferentiableOn ℂ (cayleyPullback f) upperHalf :=
    cayleyPullback_holomorphic hf
  have hUA : phiArea (cayleyPullback f) upperHalf < ⊤ := by
    rw [cayleyPullback_phiArea]
    exact hfA
  exact ⟨fun z hz => ProjectivePoincare.summable_norm Γ hΓ hU hUA hz,
    fun K hK hKH => ProjectivePoincare.tendstoUniformlyOn Γ hΓ hU hUA hK hKH⟩

end LowDimensionalTopology.Geometry.Teichmuller.QuadraticCayleyL1
