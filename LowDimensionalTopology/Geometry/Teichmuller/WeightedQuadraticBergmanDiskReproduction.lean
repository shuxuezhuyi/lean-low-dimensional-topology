module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanCayleyEquivalence
public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanReproduction
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# The literal kernel of the full original weighted disc space

Quadratic Cayley covariance gives genuine weighted L² membership of every disc
kernel section. The original complex linear isometry then transports the
half-plane reproducing formula, with the same first-linear pairing and actual
absolute convergence on the full original disc.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ComplexConjugate ENNReal NNReal UpperHalfPlane Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman

open LowDimensionalTopology.Geometry.Hyperbolic LiZhongQC QuadraticBergman

/-- The conjugate-first literal kernel for the original inverse-density-square weight. -/
def diskQuadraticKernel (z ζ : ℂ) : ℂ :=
  (12 / Real.pi : ℂ) / (1 - conj z * ζ) ^ 4

theorem diskKernel_denom_ne_zero {z ζ : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) (hζ : ζ ∈ Metric.ball (0 : ℂ) 1) :
    1 - conj z * ζ ≠ 0 := by
  have hn : ‖conj z * ζ‖ < 1 := by
    calc
      ‖conj z * ζ‖ = ‖z‖ * ‖ζ‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hζ).le (norm_nonneg _)
      _ = ‖z‖ := mul_one _
      _ < 1 := mem_ball_zero_iff.mp hz
  intro h
  rw [(sub_eq_zero.mp h).symm, norm_one] at hn
  exact (lt_irrefl (1 : ℝ)) hn

/-- The kernel section is holomorphic at every original disc point. -/
theorem diskKernel_holomorphic {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (diskQuadraticKernel z) (Metric.ball (0 : ℂ) 1) := by
  unfold diskQuadraticKernel
  exact (differentiableOn_const _).div (by fun_prop)
    (fun ζ hζ => pow_ne_zero 4 (diskKernel_denom_ne_zero hz hζ))

private theorem inverseCayley_kernel_denominator {z ζ : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) (hζ : ζ ∈ Metric.ball (0 : ℂ) 1) :
    conj (inverseCayleyFormula z) - inverseCayleyFormula ζ =
      -(2 * Complex.I) * (1 - conj z * ζ) / ((1 - conj z) * (1 - ζ)) := by
  have hzc : 1 - conj z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hn : (1 : ℝ) = ‖z‖ := by
      simpa only [norm_one, Complex.norm_conj] using congrArg norm h
    exact (ne_of_lt (mem_ball_zero_iff.mp hz)) hn.symm
  have hζ0 : 1 - ζ ≠ 0 := inverseCayley_denom_ne_zero
    (Complex.UnitDisc.mk ζ (mem_ball_zero_iff.mp hζ))
  simp only [inverseCayleyFormula, map_mul, map_div₀, map_add, map_sub,
    map_one, Complex.conj_I]
  field_simp [hzc, hζ0]
  ring

/-- Both squared derivative factors occur in the true inverse Cayley covariance. -/
theorem inverseCayley_kernel_covariance {z ζ : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) (hζ : ζ ∈ Metric.ball (0 : ℂ) 1) :
    diskQuadraticKernel z ζ = conj (inverseCayleyDerivative z ^ 2) *
      halfPlaneQuadraticKernel (inverseCayleyFormula z) (inverseCayleyFormula ζ) *
        inverseCayleyDerivative ζ ^ 2 := by
  have hzc : 1 - conj z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hn : (1 : ℝ) = ‖z‖ := by
      simpa only [norm_one, Complex.norm_conj] using congrArg norm h
    exact (ne_of_lt (mem_ball_zero_iff.mp hz)) hn.symm
  have hζ0 : 1 - ζ ≠ 0 := inverseCayley_denom_ne_zero
    (Complex.UnitDisc.mk ζ (mem_ball_zero_iff.mp hζ))
  have hd := diskKernel_denom_ne_zero hz hζ
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  unfold diskQuadraticKernel halfPlaneQuadraticKernel
  rw [inverseCayley_kernel_denominator hz hζ]
  simp only [inverseCayleyDerivative, map_pow, map_div₀, map_mul, map_ofNat,
    map_sub, map_one, Complex.conj_I]
  field_simp [hzc, hζ0, hd, hπ, Complex.I_ne_zero]

/-- The original forward Cayley formula retains the conjugated first derivative slot. -/
theorem cayley_kernel_covariance {z ζ : ℂ} (hz : 0 < z.im) (hζ : 0 < ζ.im) :
    halfPlaneQuadraticKernel z ζ =
      diskQuadraticKernel (cayleyFormula z) (cayleyFormula ζ) *
        conj (cayleyDerivative z ^ 2) * cayleyDerivative ζ ^ 2 := by
  have hi := inverseCayley_kernel_covariance (cayley_mapsTo hz) (cayley_mapsTo hζ)
  rw [inverseCayley_cayley hz, inverseCayley_cayley hζ] at hi
  rw [hi]
  calc
    halfPlaneQuadraticKernel z ζ = halfPlaneQuadraticKernel z ζ *
        conj ((inverseCayleyDerivative (cayleyFormula z) * cayleyDerivative z) ^ 2) *
          (inverseCayleyDerivative (cayleyFormula ζ) * cayleyDerivative ζ) ^ 2 := by
      simp only [inverseCayleyDerivative_cayley hz, inverseCayleyDerivative_cayley hζ,
        one_pow, map_one, mul_one]
    _ = _ := by simp only [map_pow, map_mul]; ring

private theorem disk_ae_eq_of_eqOn {φ ψ : ℂ → ℂ}
    (h : EqOn φ ψ (Metric.ball (0 : ℂ) 1)) : φ =ᵐ[diskMeasure] ψ :=
  (withDensity_absolutelyContinuous (volume.restrict (Metric.ball (0 : ℂ) 1))
    (fun z => (diskWeight z : ℝ≥0∞))).ae_eq (h.aeEq_restrict measurableSet_ball)

/-- Actual weighted L² membership precedes the kernel constructor and reproducing theorem. -/
theorem diskKernel_memLp {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    MemLp (diskQuadraticKernel z) 2 diskMeasure := by
  have hzH := inverseCayley_mapsTo hz
  have hm := ((inverseCayleyPullback_memLp_iff (halfPlaneKernel_holomorphic hzH)).mp
    (halfPlaneKernel_memLp hzH)).const_mul (conj (inverseCayleyDerivative z ^ 2))
  have he : (fun ζ => conj (inverseCayleyDerivative z ^ 2) *
      inverseCayleyPullback (halfPlaneQuadraticKernel (inverseCayleyFormula z)) ζ) =ᵐ[diskMeasure]
        diskQuadraticKernel z := by
    apply disk_ae_eq_of_eqOn
    intro ζ hζ
    change conj (inverseCayleyDerivative z ^ 2) *
      (halfPlaneQuadraticKernel (inverseCayleyFormula z) (inverseCayleyFormula ζ) *
        inverseCayleyDerivative ζ ^ 2) = diskQuadraticKernel z ζ
    simpa only [mul_assoc] using (inverseCayley_kernel_covariance hz hζ).symm
  exact MemLp.ae_eq he hm

/-- The literal kernel as a genuine element of the full original disc space. -/
def diskKernelElement {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) : Disk :=
  ofFunction (diskQuadraticKernel z) (diskKernel_holomorphic hz) (diskKernel_memLp hz)

/-- The kernel constructor retains its literal value at every original disc point. -/
theorem diskKernelElement_coefficient {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    EqOn (coefficient (diskKernelElement hz)) (diskQuadraticKernel z) (Metric.ball (0 : ℂ) 1) :=
  disk_coefficient_ofFunction _ _ _

/-- The original weighted L² class is the correctly scaled inverse quadratic pullback. -/
theorem diskKernelElement_eq_scaled_inverseCayley {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    diskKernelElement hz = conj (inverseCayleyDerivative z ^ 2) •
      inverseCayleyPullbackElement (halfPlaneKernelElement (inverseCayley_mapsTo hz)) := by
  let k : HalfPlane := halfPlaneKernelElement (inverseCayley_mapsTo hz)
  let v : Disk := inverseCayleyPullbackElement k
  let c : ℂ := conj (inverseCayleyDerivative z ^ 2)
  change diskKernelElement hz = c • v
  have he : coefficient (diskKernelElement hz) =ᵐ[diskMeasure]
      (fun ζ => c * coefficient v ζ) := by
    apply disk_ae_eq_of_eqOn
    intro ζ hζ
    change coefficient (diskKernelElement hz) ζ = c * coefficient (inverseCayleyPullbackElement k) ζ
    rw [diskKernelElement_coefficient hz hζ,
      inverseCayleyPullbackElement_coefficient k hζ]
    change diskQuadraticKernel z ζ = conj (inverseCayleyDerivative z ^ 2) *
      (coefficient k (inverseCayleyFormula ζ) * inverseCayleyDerivative ζ ^ 2)
    rw [halfPlaneKernelElement_coefficient (inverseCayley_mapsTo hz) (inverseCayley_mapsTo hζ)]
    simpa only [mul_assoc] using inverseCayley_kernel_covariance hz hζ
  apply Subtype.ext
  apply Lp.ext
  change ((diskKernelElement hz).val : ℂ → ℂ) =ᵐ[diskMeasure]
    ((c • v.val : Lp ℂ 2 diskMeasure) : ℂ → ℂ)
  filter_upwards [coefficient_ae (diskKernelElement hz), he,
    coefficient_ae v, Lp.coeFn_smul c v.val] with ζ hL hE hV hS
  calc
    (diskKernelElement hz).val ζ = coefficient (diskKernelElement hz) ζ := hL
    _ = c * coefficient v ζ := hE
    _ = (c • v.val : Lp ℂ 2 diskMeasure) ζ := by
      simpa only [Pi.smul_apply, smul_eq_mul, hV] using hS.symm

/-- Every original coefficient value is its first-linear pairing with the actual kernel. -/
theorem disk_reproducing_pairing (q : Disk) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    coefficient q z = pairing q (diskKernelElement hz) := by
  let k : HalfPlane := halfPlaneKernelElement (inverseCayley_mapsTo hz)
  let c : ℂ := conj (inverseCayleyDerivative z ^ 2)
  have hpair : pairing q (inverseCayleyPullbackElement k) =
      pairing (cayleyLinearIsometryEquiv q) k := by
    have h := cayleyLinearIsometryEquiv_pairing q (inverseCayleyPullbackElement k)
    change pairing (cayleyLinearIsometryEquiv q)
      (cayleyPullbackElement (inverseCayleyPullbackElement k)) = _ at h
    rw [cayleyPullbackElement_inverseCayleyPullbackElement] at h
    exact h.symm
  symm
  calc
    pairing q (diskKernelElement hz) = conj c * pairing q (inverseCayleyPullbackElement k) := by
      rw [diskKernelElement_eq_scaled_inverseCayley]
      exact inner_smul_left (inverseCayleyPullbackElement k) q c
    _ = conj c * coefficient (cayleyLinearIsometryEquiv q) (inverseCayleyFormula z) := by
      rw [hpair, ← halfPlane_reproducing_pairing (cayleyLinearIsometryEquiv q)
        (inverseCayley_mapsTo hz)]
    _ = coefficient q z := by
      rw [cayleyLinearIsometryEquiv_coefficient q (inverseCayley_mapsTo hz),
        cayley_inverseCayley hz]
      dsimp only [c]
      rw [Complex.conj_conj]
      calc
        inverseCayleyDerivative z ^ 2 *
            (coefficient q z * cayleyDerivative (inverseCayleyFormula z) ^ 2) =
          coefficient q z *
            (cayleyDerivative (inverseCayleyFormula z) * inverseCayleyDerivative z) ^ 2 := by ring
        _ = coefficient q z := by
          rw [cayleyDerivative_inverseCayley hz, one_pow, mul_one]

theorem disk_reproducing_inner (q : Disk) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    coefficient q z = inner ℂ (diskKernelElement hz) q := by
  simpa only [pairing] using disk_reproducing_pairing q hz

/-- Hölder in the unchanged weighted L² carrier supplies actual absolute convergence. -/
theorem disk_kernel_integrable (q : Disk) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    IntegrableOn (fun ζ => (diskWeight ζ : ℂ) * coefficient q ζ *
      conj (diskQuadraticKernel z ζ)) (Metric.ball (0 : ℂ) 1) := by
  exact (disk_pairing_integrable q (diskKernelElement hz)).congr_fun
    (fun ζ hζ => by
      dsimp only
      rw [diskKernelElement_coefficient hz hζ]) measurableSet_ball

/-- Literal absolutely convergent reproduction holds for every element and every disc point. -/
theorem disk_reproducing (q : Disk) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    coefficient q z = ∫ ζ in Metric.ball (0 : ℂ) 1,
      (diskWeight ζ : ℂ) * coefficient q ζ * conj (diskQuadraticKernel z ζ) := by
  rw [disk_reproducing_pairing q hz, disk_pairing_eq_integral]
  exact setIntegral_congr_fun measurableSet_ball fun ζ hζ => by
    rw [diskKernelElement_coefficient hz hζ]

end LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman
