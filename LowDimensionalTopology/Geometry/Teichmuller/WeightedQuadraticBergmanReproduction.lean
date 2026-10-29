module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanSpaces
public import LowDimensionalTopology.Geometry.Teichmuller.HalfPlaneQuadraticReproduction
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Reproduction in the full weighted holomorphic half-plane space

Every original half-plane point determines a holomorphic kernel section with a
genuine finite weighted L² norm. The native L² pairing therefore supplies actual
absolute integrability, and the general analytic reproducing formula recovers
every coefficient value. The pairing is linear in its first argument.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ComplexConjugate ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman

open LiZhongQC QuadraticBergman

/-- The literal kernel section is holomorphic on the original upper half-plane. -/
theorem halfPlaneKernel_holomorphic {z : ℂ} (hz : z ∈ upperHalf) :
    DifferentiableOn ℂ (halfPlaneQuadraticKernel z) upperHalf := by
  unfold halfPlaneQuadraticKernel
  exact (differentiableOn_const _).div (by fun_prop)
    (fun ζ hζ => pow_ne_zero 4 (h36p_c_conj_sub_ne hz hζ))

private theorem halfPlaneKernel_norm (z ζ : ℂ) :
    ‖halfPlaneQuadraticKernel z ζ‖ =
      ‖(12 / Real.pi : ℂ)‖ * ‖ζ - conj z‖⁻¹ ^ 4 := by
  unfold halfPlaneQuadraticKernel
  rw [norm_div, norm_pow, norm_sub_rev, div_eq_mul_inv, inv_pow]

private theorem halfPlaneKernel_profile_integrable {z : ℂ} (hz : z ∈ upperHalf) :
    IntegrableOn (fun ζ : ℂ => ‖ζ - conj z‖⁻¹ ^ 4) upperHalf := by
  have hm : Measurable (fun ζ : ℂ => ‖ζ - conj z‖⁻¹ ^ 4) := by fun_prop
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (f := fun ζ : ℂ => ‖ζ - conj z‖⁻¹ ^ 4)
    (Eventually.of_forall fun ζ => by positivity)).2
  rw [h36p_c_kernel_area (h36p_c_conj_mem hz)]
  exact ENNReal.mul_lt_top measure_ball_lt_top ENNReal.ofReal_lt_top

private theorem halfPlaneKernel_weighted_sq_le {z ζ : ℂ}
    (hz : z ∈ upperHalf) (hζ : ζ ∈ upperHalf) :
    ζ.im ^ 2 * ‖halfPlaneQuadraticKernel z ζ‖ ^ 2 ≤
      (‖(12 / Real.pi : ℂ)‖ ^ 2 / (16 * z.im ^ 2)) * ‖ζ - conj z‖⁻¹ ^ 4 := by
  have hn : ‖z - conj ζ‖ = ‖ζ - conj z‖ := by
    rw [← Complex.norm_conj (z - conj ζ), map_sub, Complex.conj_conj, norm_sub_rev]
  have hb : ζ.im ^ 2 * ‖ζ - conj z‖⁻¹ ^ 4 ≤ 1 / (16 * z.im ^ 2) := by
    simpa only [h36p_c_K_norm, hn, norm_one, mul_one] using
      h36p_c_K_le (fun _ : ℂ => (1 : ℂ)) hζ hz
  rw [halfPlaneKernel_norm]
  calc
    ζ.im ^ 2 * (‖(12 / Real.pi : ℂ)‖ * ‖ζ - conj z‖⁻¹ ^ 4) ^ 2 =
        (ζ.im ^ 2 * ‖ζ - conj z‖⁻¹ ^ 4) *
          (‖(12 / Real.pi : ℂ)‖ ^ 2 * ‖ζ - conj z‖⁻¹ ^ 4) := by ring
    _ ≤ (1 / (16 * z.im ^ 2)) *
        (‖(12 / Real.pi : ℂ)‖ ^ 2 * ‖ζ - conj z‖⁻¹ ^ 4) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by ring

private theorem halfPlaneKernel_weighted_sq_integrable {z : ℂ} (hz : z ∈ upperHalf) :
    IntegrableOn (fun ζ : ℂ => ζ.im ^ 2 * ‖halfPlaneQuadraticKernel z ζ‖ ^ 2)
      upperHalf := by
  have hc : ContinuousOn
      (fun ζ : ℂ => ζ.im ^ 2 * ‖halfPlaneQuadraticKernel z ζ‖ ^ 2) upperHalf :=
    (Complex.continuous_im.continuousOn.pow 2).mul
      ((halfPlaneKernel_holomorphic hz).continuousOn.norm.pow 2)
  refine ((halfPlaneKernel_profile_integrable hz).const_mul
    (‖(12 / Real.pi : ℂ)‖ ^ 2 / (16 * z.im ^ 2))).mono'
      (hc.aestronglyMeasurable isOpen_upperHalf.measurableSet) ?_
  refine ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet fun ζ hζ => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact halfPlaneKernel_weighted_sq_le hz hζ

/-- Membership is proved from the actual weighted integral, with no extra premise. -/
theorem halfPlaneKernel_memLp {z : ℂ} (hz : z ∈ upperHalf) :
    MemLp (halfPlaneQuadraticKernel z) 2 halfPlaneMeasure := by
  have hm : Measurable (halfPlaneQuadraticKernel z) := by
    unfold halfPlaneQuadraticKernel
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
  change Integrable (fun ζ => ‖halfPlaneQuadraticKernel z ζ‖ ^ 2)
    ((volume.restrict upperHalf).withDensity (fun ζ => (halfPlaneWeight ζ : ℝ≥0∞)))
  apply (integrable_withDensity_iff_integrable_coe_smul halfPlaneWeight_measurable).2
  change Integrable (fun ζ : ℂ => ζ.im ^ 2 * ‖halfPlaneQuadraticKernel z ζ‖ ^ 2)
    (volume.restrict upperHalf)
  exact halfPlaneKernel_weighted_sq_integrable hz

/-- The actual kernel section as an element of the full original weighted space. -/
def halfPlaneKernelElement {z : ℂ} (hz : z ∈ upperHalf) : HalfPlane :=
  ofFunction (halfPlaneQuadraticKernel z) (halfPlaneKernel_holomorphic hz)
    (halfPlaneKernel_memLp hz)

/-- Every original domain value of the kernel section is retained. -/
theorem halfPlaneKernelElement_coefficient {z : ℂ} (hz : z ∈ upperHalf) :
    EqOn (coefficient (halfPlaneKernelElement hz)) (halfPlaneQuadraticKernel z) upperHalf :=
  halfPlane_coefficient_ofFunction (halfPlaneQuadraticKernel z)
    (halfPlaneKernel_holomorphic hz) (halfPlaneKernel_memLp hz)

private theorem weighted_kernel_integrand_eq (φ : ℂ → ℂ) (z ζ : ℂ) :
    (halfPlaneWeight ζ : ℂ) * φ ζ * conj (halfPlaneQuadraticKernel z ζ) =
      (12 / Real.pi : ℂ) * h36p_c_K φ ζ z := by
  have hw : (halfPlaneWeight ζ : ℂ) = (ζ.im : ℂ) ^ 2 := by
    change ((ζ.im ^ 2 : ℝ) : ℂ) = (ζ.im : ℂ) ^ 2
    exact Complex.ofReal_pow _ _
  have hpow : (z - conj ζ) ^ 4 = (conj ζ - z) ^ 4 := by ring
  rw [hw]
  simp only [halfPlaneQuadraticKernel, h36p_c_K, map_div₀, map_ofNat,
    Complex.conj_ofReal, map_pow, map_sub, Complex.conj_conj]
  rw [hpow]
  ring

/-- Hölder in the actual weighted L² space gives absolute convergence for every element. -/
theorem halfPlane_kernel_integrable (q : HalfPlane) {z : ℂ} (hz : z ∈ upperHalf) :
    IntegrableOn (fun ζ => (halfPlaneWeight ζ : ℂ) * coefficient q ζ *
      conj (halfPlaneQuadraticKernel z ζ)) upperHalf := by
  have hi := halfPlane_pairing_integrable q (halfPlaneKernelElement hz)
  exact hi.congr_fun (fun ζ hζ => by
    dsimp only
    rw [halfPlaneKernelElement_coefficient hz hζ]) isOpen_upperHalf.measurableSet

private theorem halfPlane_h36_integrable (q : HalfPlane) {z : ℂ} (hz : z ∈ upperHalf) :
    IntegrableOn (fun ζ => h36p_c_K (coefficient q) ζ z) upperHalf := by
  have hi := halfPlane_kernel_integrable q hz
  have hc : (12 / Real.pi : ℂ) ≠ 0 :=
    div_ne_zero (by norm_num) (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have hdiv : IntegrableOn (fun ζ => ((halfPlaneWeight ζ : ℂ) * coefficient q ζ *
      conj (halfPlaneQuadraticKernel z ζ)) / (12 / Real.pi : ℂ)) upperHalf :=
    hi.div_const (12 / Real.pi : ℂ)
  exact hdiv.congr_fun (fun ζ _ => by
    dsimp only
    rw [weighted_kernel_integrand_eq]
    exact mul_div_cancel_left₀ _ hc) isOpen_upperHalf.measurableSet

/-- The general reproducing formula, for every element and every original half-plane point. -/
theorem halfPlane_reproducing (q : HalfPlane) {z : ℂ} (hz : z ∈ upperHalf) :
    coefficient q z = ∫ ζ in upperHalf,
      (halfPlaneWeight ζ : ℂ) * coefficient q ζ * conj (halfPlaneQuadraticKernel z ζ) := by
  have hr : coefficient q z = (12 / Real.pi : ℂ) *
      ∫ ζ in upperHalf, h36p_c_K (coefficient q) ζ z := by
    rw [h36p_c_rp_upper (coefficient_holomorphic q) hz (halfPlane_h36_integrable q hz)]
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    field_simp
  calc
    coefficient q z = (12 / Real.pi : ℂ) *
        ∫ ζ in upperHalf, h36p_c_K (coefficient q) ζ z := hr
    _ = _ := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun isOpen_upperHalf.measurableSet fun ζ _ =>
        (weighted_kernel_integrand_eq (coefficient q) z ζ).symm

/-- Evaluation is the first-linear pairing with the genuine kernel element. -/
theorem halfPlane_reproducing_pairing (q : HalfPlane) {z : ℂ} (hz : z ∈ upperHalf) :
    coefficient q z = pairing q (halfPlaneKernelElement hz) := by
  calc
    coefficient q z = ∫ ζ in upperHalf,
        (halfPlaneWeight ζ : ℂ) * coefficient q ζ *
          conj (halfPlaneQuadraticKernel z ζ) := halfPlane_reproducing q hz
    _ = ∫ ζ in upperHalf, (halfPlaneWeight ζ : ℂ) * coefficient q ζ *
        conj (coefficient (halfPlaneKernelElement hz) ζ) := by
      exact setIntegral_congr_fun isOpen_upperHalf.measurableSet fun ζ hζ => by
        rw [halfPlaneKernelElement_coefficient hz hζ]
    _ = pairing q (halfPlaneKernelElement hz) :=
      (halfPlane_pairing_eq_integral q (halfPlaneKernelElement hz)).symm

/-- The native inner product retains its conjugate-first slot convention. -/
theorem halfPlane_reproducing_inner (q : HalfPlane) {z : ℂ} (hz : z ∈ upperHalf) :
    coefficient q z = inner ℂ (halfPlaneKernelElement hz) q := by
  simpa only [pairing] using halfPlane_reproducing_pairing q hz

end LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman
