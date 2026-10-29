module

public import LowDimensionalTopology.Geometry.Quasiconformal.RealHilbertPrincipalValue
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Real and imaginary components of the literal real-line Hilbert transform

The complex Hilbert estimate reduces tests to their real components. These identities
concern the actual original principal-value transform, with its positive
`1/pi` normalization. They are derived from the absolutely integrable paired
kernel, without an Lp estimate, an assumed operator extension, or any
orthogonality claim about arbitrary complex-valued summands.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Complex

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem realHilbertTransform_comp_realLinear {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (L : ℂ →L[ℝ] ℂ) (ξ : ℝ) :
    realHilbertTransform (fun x => L (φ x)) ξ = L (realHilbertTransform φ ξ) := by
  have hL : ContDiff ℝ 1 (fun x => L (φ x)) := L.contDiff.comp hφ
  have hcL : HasCompactSupport (fun x => L (φ x)) :=
    hc.comp_left (g := fun z : ℂ => L z) L.map_zero
  have hQ : IntegrableOn (realHilbertPairedKernel φ ξ) (Ioi (0 : ℝ)) :=
    (integrable_realHilbertPairedKernel hφ hc ξ).integrableOn
  have hpair : (∫ x in Ioi (0 : ℝ), realHilbertPairedKernel (fun t => L (φ t)) ξ x) =
      L (∫ x in Ioi (0 : ℝ), realHilbertPairedKernel φ ξ x) := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), L (realHilbertPairedKernel φ ξ x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        change realHilbertPairedKernel (fun t => L (φ t)) ξ x =
          L (realHilbertPairedKernel φ ξ x)
        rw [realHilbertPairedKernel_of_ne (fun t => L (φ t)) ξ (ne_of_gt hx),
          realHilbertPairedKernel_of_ne φ ξ (ne_of_gt hx)]
        simp only [map_smul, map_sub]
      _ = _ := L.integral_comp_comm hQ
  rw [(realHilbert_principalValue_and_eq_paired hL hcL ξ).2,
    (realHilbert_principalValue_and_eq_paired hφ hc ξ).2]
  have hscale (w : ℂ) : (1 / (Real.pi : ℂ)) * w = (1 / Real.pi : ℝ) • w := by
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
  simp only [hscale, map_smul]
  exact congrArg (fun w : ℂ => (1 / Real.pi : ℝ) • w) hpair

/-- The real component is the transform of the actual real-part test.
The equality embeds both real values into the same complex codomain. -/
theorem realHilbertTransform_realPart {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (ξ : ℝ) :
    realHilbertTransform (fun x => ((φ x).re : ℂ)) ξ =
      ((realHilbertTransform φ ξ).re : ℂ) := by
  simpa only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    Complex.reCLM_apply] using
    realHilbertTransform_comp_realLinear hφ hc
      (Complex.ofRealCLM.comp Complex.reCLM) ξ

/-- The imaginary component is the transform of the actual imaginary-part
test; no complex-valued orthogonality assumption is used. -/
theorem realHilbertTransform_imaginaryPart {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (ξ : ℝ) :
    realHilbertTransform (fun x => ((φ x).im : ℂ)) ξ =
      ((realHilbertTransform φ ξ).im : ℂ) := by
  simpa only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    Complex.imCLM_apply] using
    realHilbertTransform_comp_realLinear hφ hc
      (Complex.ofRealCLM.comp Complex.imCLM) ξ

/-- A genuine real compact C1 test has a real principal-value transform.
This follows from the literal transform itself, before any Riesz estimate. -/
theorem realHilbertTransform_ofReal_im_eq_zero {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (ξ : ℝ) :
    (realHilbertTransform (fun x => (φ x : ℂ)) ξ).im = 0 := by
  have hcast : ContDiff ℝ 1 (fun x => (φ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hφ
  have hcompact : HasCompactSupport (fun x => (φ x : ℂ)) :=
    hc.comp_left (g := fun x : ℝ => (x : ℂ)) rfl
  have heq := realHilbertTransform_realPart hcast hcompact ξ
  have him := congrArg Complex.im heq
  simpa only [Complex.ofReal_re, Complex.ofReal_im] using him

end LowDimensionalTopology.Geometry.Quasiconformal
