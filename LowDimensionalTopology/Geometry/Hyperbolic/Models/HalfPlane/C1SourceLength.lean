module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.CurveLength
public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

/-! # Actual C1 half-plane pieces have the same literal source integral -/

public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Continuous velocities are bounded on the complete compact parameter interval. -/
theorem C1CurvePiece.exists_euclidean_lipschitz (c : C1CurvePiece) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun t => (c.curve t : ℂ)) (Icc c.a c.b) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image c.continuous_velocity.nnnorm
  refine ⟨K, (convex_Icc c.a c.b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    c.hasDerivWithin ?_⟩
  intro t ht
  exact hK ⟨t, ht, rfl⟩

theorem C1CurvePiece.exists_unit_lipschitz (c : C1CurvePiece)
    (ha : c.a = 0) (hb : c.b = 1) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun t => (c.curve t : ℂ)) (Icc 0 1) := by
  simpa only [ha, hb] using c.exists_euclidean_lipschitz

/-- The actual weighted derivative integral agrees with the native C1 integral.
Only the two endpoint derivatives are discarded, on a measure-zero set. -/
theorem C1CurvePiece.hypLength_eq_length (c : C1CurvePiece)
    (ha : c.a = 0) (hb : c.b = 1) :
    LiZhongQC.hypLength (fun t => (c.curve t : ℂ)) = ENNReal.ofReal c.length := by
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => (c.curve s : ℂ)) (c.velocity t) (Icc 0 1) t := by
    simpa only [ha, hb] using c.hasDerivWithin
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      deriv (fun s => (c.curve s : ℂ)) t = c.velocity t :=
    ((hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv
  have hspeed : ContinuousOn (weightedSpeed c.curve c.velocity) (Icc (0 : ℝ) 1) := by
    simpa only [ha, hb] using c.continuous_speed
  have hi : IntegrableOn (weightedSpeed c.curve c.velocity) (Ioo (0 : ℝ) 1) :=
    hspeed.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      weightedSpeed c.curve c.velocity :=
    Filter.Eventually.of_forall (weightedSpeed_nonneg c.curve c.velocity)
  calc
    LiZhongQC.hypLength (fun t => (c.curve t : ℂ)) =
        ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (weightedSpeed c.curve c.velocity t) := by
      unfold LiZhongQC.hypLength
      refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
      change ‖deriv (fun s => (c.curve s : ℂ)) t‖ₑ /
          ENNReal.ofReal (c.curve t).im =
        ENNReal.ofReal (‖c.velocity t‖ / (c.curve t).im)
      rw [hd t ht, ← ofReal_norm, ← ENNReal.ofReal_div_of_pos (c.curve t).im_pos]
    _ = ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, weightedSpeed c.curve c.velocity t) :=
      (ofReal_integral_eq_lintegral_ofReal hi hnonneg).symm
    _ = ENNReal.ofReal c.length := by
      rw [C1CurvePiece.length, ha, hb, intervalIntegral.integral_of_le zero_le_one,
        integral_Ioc_eq_integral_Ioo]

end LowDimensionalTopology.Geometry.Hyperbolic
