module

public import LowDimensionalTopology.Geometry.Teichmuller.BookTeichmullerMetric
public import Mathlib.Topology.Sequences

/-!
# Coordinate parametrization with the actual full-log QC topology

The same source deformation map is retained. Its sequential convergence theorem
is converted to continuity in both directions for the explicit QC metric.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

universe u

/-- The source deformation parametrization is a homeomorphism for the actual
full-log QC metric, with its original initial-differential and radius clauses. -/
theorem sourceCoordinateHomeomorph
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [CompactSpace X]
    {g : ℕ} (hg : 1 < g) (hX : LiZhongQC.HasGenus X g)
    (e : (LiZhongQC.holQuadDiffSubmodule X).restrictScalars ℝ ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (6 * g - 6))) :
    let : MetricSpace (LiZhongQC.TeichSpace X) := QCBookMetric.metricSpace hg hX
    ∃ H : ↥(ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1) ≃ₜ
        LiZhongQC.TeichSpace X,
      (∀ v : ↥(ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1),
        ∃ q : (LiZhongQC.holQuadDiffSubmodule X).restrictScalars ℝ,
        ‖e q‖ = 1 ∧ LiZhongQC.IsDeformationPoint q ‖(v : EuclideanSpace ℝ
          (Fin (6 * g - 6)))‖ (H v) ∧
          ((v : EuclideanSpace ℝ (Fin (6 * g - 6))) ≠ 0 →
            ‖(v : EuclideanSpace ℝ (Fin (6 * g - 6)))‖ • e q = v)) ∧
      ∀ v : ↥(ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1),
        (v : EuclideanSpace ℝ (Fin (6 * g - 6))) = 0 →
        H v = LiZhongQC.TeichSpace.basePoint LiZhongQC.isQCRS_refl := by
  let : MetricSpace (LiZhongQC.TeichSpace X) := QCBookMetric.metricSpace hg hX
  obtain ⟨Φ, hinj, hsurj, _, hdef⟩ := LiZhongQC.s29_t1_param hg hX e
  let B := ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1
  have hbij : Function.Bijective (fun v : ↥B => Φ v.val) := by
    constructor
    · intro v w hvw
      apply Subtype.ext
      exact hinj v.property w.property hvw
    · intro p
      obtain ⟨v, hv, hΦv⟩ := hsurj p
      exact ⟨⟨v, hv⟩, hΦv⟩
  let E : ↥B ≃ LiZhongQC.TeichSpace X := Equiv.ofBijective _ hbij
  have hcont : Continuous (E : ↥B → LiZhongQC.TeichSpace X) := by
    refine continuous_iff_seqContinuous.2 fun {vn v} hvn => ?_
    apply tendsto_iff_dist_tendsto_zero.2
    change Tendsto (fun n => QCBookMetric.bookDistance (Φ (vn n).val) (Φ v.val))
      atTop (𝓝 0)
    apply (QCBookMetric.tendsto_bookDistance_zero_iff _ _).2
    exact (LiZhongQC.s29_t1_iff hg hX e hdef v.val (fun n => (vn n).val)
      v.property (fun n => (vn n).property)).1 (tendsto_subtype_rng.1 hvn)
  have hinv : Continuous (E.symm : LiZhongQC.TeichSpace X → ↥B) := by
    refine continuous_iff_seqContinuous.2 fun {pn p} hpn => ?_
    apply tendsto_subtype_rng.2
    apply (LiZhongQC.s29_t1_iff hg hX e hdef (E.symm p).val
      (fun n => (E.symm (pn n)).val) (E.symm p).property
      (fun n => (E.symm (pn n)).property)).2
    have hbook := tendsto_iff_dist_tendsto_zero.1 hpn
    change Tendsto (fun n => QCBookMetric.bookDistance (pn n) p) atTop (𝓝 0) at hbook
    have hhalf := (QCBookMetric.tendsto_bookDistance_zero_iff pn p).1 hbook
    refine hhalf.congr fun n => ?_
    change LiZhongQC.teichDistance (pn n) p =
      LiZhongQC.teichDistance (E (E.symm (pn n))) (E (E.symm p))
    rw [E.apply_symm_apply, E.apply_symm_apply]
  let H : ↥B ≃ₜ LiZhongQC.TeichSpace X :=
    { toEquiv := E, continuous_toFun := hcont, continuous_invFun := hinv }
  refine ⟨H, ?_, ?_⟩
  · intro v
    exact hdef v.val v.property
  · intro v hv
    apply (LiZhongQC.teichDistance_eq_of_eq_zero hg hX
      (LiZhongQC.TeichSpace.basePoint LiZhongQC.isQCRS_refl) (H v) ?_).symm
    change LiZhongQC.teichDistance
      (LiZhongQC.TeichSpace.basePoint LiZhongQC.isQCRS_refl) (Φ v.val) = 0
    simpa only [hv, norm_zero, add_zero, sub_zero, div_one, Real.log_one, mul_zero] using
      LiZhongQC.s29_t1_bound hg hX e LiZhongQC.isQCRS_refl hdef v.property

end LowDimensionalTopology.Geometry.Teichmuller
