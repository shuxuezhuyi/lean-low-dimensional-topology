module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonCauchySquareComposition
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# The actual singular inner input is square integrable

The unchanged source input is the zero extension of a bounded upper-half-plane
coefficient times its cross-half-plane Cauchy square. The ordinary composition
at equal endpoints proves the square-kernel integral. The coefficient's own
L-infinity norm then proves L² membership and every punctured integral.
This does not yet assert convergence of the singular principal value.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped ComplexConjugate UpperHalfPlane ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open GammaMeasurableBeltrami LiZhongQC

private theorem square_kernel_integrable (z : ℍ) :
    IntegrableOn (fun η : ℂ => ‖cauchySquare η (conj (z : ℂ))‖ ^ 2) upperHalf := by
  have hi := (cauchySquare_composition z z).1.re
  refine hi.congr_fun (fun η _ => ?_) isOpen_upperHalf.measurableSet
  have hc : cauchySquare (conj η) z = conj (cauchySquare η (conj (z : ℂ))) := by
    simp only [cauchySquare, map_div₀, map_one, map_pow, map_sub, Complex.conj_conj]
  change (cauchySquare (conj η) z * cauchySquare η (conj (z : ℂ))).re =
    ‖cauchySquare η (conj (z : ℂ))‖ ^ 2
  rw [hc, mul_comm, Complex.mul_conj']
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

private theorem innerInput_eq_planeRepresentative (b : Ambient) (z : ℍ) :
    innerInput (fun η => b η) z =
      fun η => planeRepresentative b η * cauchySquare η (conj (z : ℂ)) := by
  funext η
  by_cases hη : 0 < η.im
  · simp only [innerInput, upperExtension, planeRepresentative, show η ∈ upperHalf from hη,
      hη, dite_true]
  · simp only [innerInput, upperExtension, planeRepresentative,
      show η ∉ upperHalf from hη, hη, dite_false, zero_mul]

/-- Every original L-infinity coefficient has its SAME source inner input in
actual planar L². No pointwise representative bound or smoothness is assumed. -/
theorem innerInput_memLp_two (b : Ambient) (z : ℍ) :
    MemLp (innerInput (fun η => b η) z) 2 (volume : Measure ℂ) := by
  have hb := planeRepresentative_isBeltramiCoeff b
  have hk : Measurable (fun η : ℂ => cauchySquare η (conj (z : ℂ))) := by
    unfold cauchySquare
    fun_prop
  have hm : AEStronglyMeasurable (innerInput (fun η => b η) z)
      (volume.restrict upperHalf) := by
    rw [innerInput_eq_planeRepresentative]
    exact hb.1.mul hk.aestronglyMeasurable
  have hs : AEStronglyMeasurable (fun η => ‖innerInput (fun w => b w) z η‖ ^ 2)
      (volume.restrict upperHalf) := by
    exact (hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable
  have hsq : IntegrableOn (fun η => ‖innerInput (fun w => b w) z η‖ ^ 2) upperHalf := by
    refine ((square_kernel_integrable z).const_mul (‖b‖ ^ 2)).mono' hs ?_
    filter_upwards [hb.2] with η hη
    rw [Real.norm_of_nonneg (sq_nonneg _), innerInput_eq_planeRepresentative,
      norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hη 2) (sq_nonneg _)
  have hlocal : MemLp (innerInput (fun η => b η) z) 2 (volume.restrict upperHalf) :=
    (memLp_two_iff_integrable_sq_norm hm).2 hsq
  have hglobal := (memLp_indicator_iff_restrict
    isOpen_upperHalf.measurableSet.nullMeasurableSet).2 hlocal
  have he : upperHalf.indicator (innerInput (fun η => b η) z) =
      innerInput (fun η => b η) z := by
    funext η
    by_cases hη : η ∈ upperHalf
    · exact indicator_of_mem hη _
    · simp only [indicator_of_notMem hη, innerInput, upperExtension,
        show ¬0 < η.im from hη, dite_false]
  simpa only [he] using hglobal

/-- The actual punctured inner integrals all converge absolutely. The PV
limit itself remains a separate analytic step. -/
theorem innerInput_truncated_integrable (b : Ambient) (z : ℍ) (ξ : ℂ)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun η => innerInput (fun w => b w) z η / (η - ξ) ^ 2)
      {η : ℂ | r < ‖η - ξ‖} (volume : Measure ℂ) := by
  apply integrableOn_truncated_kernel (p := 2) (by norm_num) ?_ ξ hr
  simpa using innerInput_memLp_two b z

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel
