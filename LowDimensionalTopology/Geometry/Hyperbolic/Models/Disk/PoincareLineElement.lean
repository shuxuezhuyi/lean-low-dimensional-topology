module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.PoincareDensity
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.RectifiableDistance
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The literal disk Poincaré line element

The coordinate tensor is an actual continuous real bilinear form. Its positive
definiteness on the disk and its induced speed are proved from the prescribed
density. Integrating its unit speed in the actual Euclidean variation parameter
gives exactly the existing full-rectifiable distance, including arbitrary pauses
and repeated traversal.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal InnerProductSpace Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The real coordinate tensor of the disk Poincaré metric. Only its values on
the open unit disk are used as a positive definite metric. -/
def discPoincareTensor (z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  poincareLengthDensity z ^ 2 • innerSL ℝ

/-- The imported disk scalar is exactly the common geometric length density. -/
theorem poincareDensityDisc_eq_poincareLengthDensity (z : ℂ) :
    LiZhongQC.poincareDensityDisc z = poincareLengthDensity z := rfl

/-- The existing coordinate tensor uses the square of the common length density. -/
theorem discPoincareTensor_eq_poincareLengthDensity (z : ℂ) :
    discPoincareTensor z = poincareLengthDensity z ^ 2 • innerSL ℝ := rfl

theorem discPoincareTensor_apply (z v w : ℂ) :
    discPoincareTensor z v w =
      LiZhongQC.poincareDensityDisc z ^ 2 * ⟪v, w⟫_ℝ := rfl

/-- The tensor is symmetric on the real tangent coordinate space. -/
theorem discPoincareTensor_symmetric (z v w : ℂ) :
    discPoincareTensor z v w = discPoincareTensor z w v := by
  rw [discPoincareTensor_apply, discPoincareTensor_apply, real_inner_comm v w]

/-- This is the literal coordinate expression `4 |dz|² / (1 - |z|²)²`. -/
theorem discPoincareTensor_self (z v : ℂ) :
    discPoincareTensor z v v = 4 * ‖v‖ ^ 2 / (1 - ‖z‖ ^ 2) ^ 2 := by
  rw [discPoincareTensor_apply, real_inner_self_eq_norm_sq,
    LiZhongQC.poincareDensityDisc, div_pow]
  norm_num
  ring

theorem discPoincareDensity_pos {z : ℂ} (hz : z ∈ LiZhongQC.unitDisc) :
    0 < LiZhongQC.poincareDensityDisc z := by
  have hnorm : ‖z‖ < 1 := by
    simpa only [LiZhongQC.unitDisc, Metric.mem_ball, dist_zero_right] using hz
  have hden : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  exact div_pos (by norm_num) hden

/-- Positive definiteness is derived, rather than added as a metric field. -/
theorem discPoincareTensor_pos {z : ℂ} (hz : z ∈ LiZhongQC.unitDisc)
    {v : ℂ} (hv : v ≠ 0) : 0 < discPoincareTensor z v v := by
  rw [discPoincareTensor_apply]
  exact mul_pos (sq_pos_of_pos (discPoincareDensity_pos hz))
    (real_inner_self_pos.mpr hv)

/-- The actual speed induced by the tensor equals the prescribed Poincaré
density times the ordinary Euclidean speed. -/
theorem discPoincareTensor_sqrt {z : ℂ} (hz : z ∈ LiZhongQC.unitDisc) (v : ℂ) :
    Real.sqrt (discPoincareTensor z v v) = LiZhongQC.poincareDensityDisc z * ‖v‖ := by
  have he : discPoincareTensor z v v =
      (LiZhongQC.poincareDensityDisc z * ‖v‖) ^ 2 := by
    rw [discPoincareTensor_apply, real_inner_self_eq_norm_sq]
    ring
  rw [he, Real.sqrt_sq (mul_nonneg (discPoincareDensity_pos hz).le (norm_nonneg v))]

/-- The arclength line integral of the actual tensor along a continuous
rectifiable curve, in its genuine Euclidean cumulative-variation parameter. -/
def discPoincareTensorLength (c : RectifiableCurve) : ℝ≥0∞ :=
  ∫⁻ t in Ioo 0 c.euclideanLength,
    ENNReal.ofReal (Real.sqrt (discPoincareTensor (c.arclengthFactor t) 1 1))

/-- Every disk curve has exactly the same length in the tensor and the literal
density definitions, without a Lipschitz assumption on its original parameter. -/
theorem discPoincareTensorLength_eq_weightedLength (c : RectifiableCurve)
    (hc : c.curve '' Icc c.a c.b ⊆ LiZhongQC.unitDisc) :
    discPoincareTensorLength c =
      c.weightedLength (fun z => ENNReal.ofReal (LiZhongQC.poincareDensityDisc z)) := by
  unfold discPoincareTensorLength RectifiableCurve.weightedLength
  apply lintegral_congr_ae
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro t ht
  have ht' : t ∈ Icc 0 c.euclideanLength := ⟨ht.1.le, ht.2.le⟩
  rw [← c.clock_spec.2.2.2.2] at ht'
  obtain ⟨u, hu, hut⟩ := ht'
  have he : c.arclengthFactor t = c.curve u := by
    rw [← hut]
    exact (c.arclengthFactor_spec.2.1 hu).symm
  have hz : c.arclengthFactor t ∈ LiZhongQC.unitDisc := he.symm ▸ hc ⟨u, hu, rfl⟩
  simp only [discPoincareTensor_sqrt hz, norm_one, mul_one]

/-- The existing distance is precisely the infimum of the actual tensor line
integrals over every continuous rectifiable joining curve. -/
theorem discRectifiableEDist_eq_tensor_infimum (z w : 𝔻) :
    discRectifiableEDist z w =
      ⨅ c ∈ {c : RectifiableCurve | c.IsPathIn LiZhongQC.unitDisc z w},
        discPoincareTensorLength c := by
  unfold discRectifiableEDist rectifiableMetricDist
  refine iInf_congr fun c => iInf_congr fun hc => ?_
  exact (discPoincareTensorLength_eq_weightedLength c hc.2.2).symm

end LowDimensionalTopology.Geometry.Hyperbolic
