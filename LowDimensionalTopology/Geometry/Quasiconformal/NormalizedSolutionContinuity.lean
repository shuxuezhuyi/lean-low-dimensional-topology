/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.BeltramiParameterDerivative

/-!
# Locally uniform continuity of normalized solutions at the zero coefficient

The coefficients are actual measurable L-infinity classes. Their norm convergence
to zero implies locally uniform convergence of the canonical normalized maps to
the identity. The compact-disc estimate follows from the proved quadratic solution
remainder and the uniform norm bound for the actual first-variation integral.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
open LowDimensionalTopology.Geometry.Teichmuller

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Actual L-infinity convergence to the zero coefficient gives locally uniform
convergence of the canonical normalized plane solutions to the identity. -/
theorem normalizedSolution_tendstoLocallyUniformly_zero
    {ι : Type*} {l : Filter ι} (μ : ι → MeasurableBeltramiBall)
    (hμ : Tendsto (fun i => (μ i).val) l (𝓝 (0 : MeasurableBeltramiSpace))) :
    TendstoLocallyUniformly
      (fun i z => MeasurableBeltramiBall.normalizedSolution (μ i) z) (id : ℂ → ℂ) l := by
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨C, -, hquad⟩ := normalizedSolution_uniform_quadratic R hR
  obtain ⟨D, -, hlinear⟩ := firstVariation_uniform_norm_le R hR
  have hnorm : Tendsto (fun i => ‖(μ i).val‖) l (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using hμ.norm
  have hsmall : ∀ᶠ i in l, ‖(μ i).val‖ < 1 / 4 :=
    hnorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have herror : Tendsto (fun i => C * ‖(μ i).val‖ ^ 2 + D * ‖(μ i).val‖) l (𝓝 0) := by
    simpa using ((hnorm.pow 2).const_mul C).add (hnorm.const_mul D)
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [herror.eventually (gt_mem_nhds hη), hsmall] with i hiη hiμ
  intro z hz
  rw [dist_comm, dist_eq_norm, id_eq]
  calc
    ‖MeasurableBeltramiBall.normalizedSolution (μ i) z - z‖ =
        ‖(MeasurableBeltramiBall.normalizedSolution (μ i) z - z -
          firstVariation (μ i).val z) + firstVariation (μ i).val z‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖MeasurableBeltramiBall.normalizedSolution (μ i) z - z - firstVariation (μ i).val z‖ +
        ‖firstVariation (μ i).val z‖ := norm_add_le _ _
    _ ≤ C * ‖(μ i).val‖ ^ 2 + D * ‖(μ i).val‖ :=
      add_le_add (hquad (μ i) hiμ z (hKR z hz)) (hlinear (μ i).val z (hKR z hz))
    _ < η := hiη

end LowDimensionalTopology.Geometry.Quasiconformal
