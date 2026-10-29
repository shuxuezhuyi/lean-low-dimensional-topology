module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanEvaluation
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Completeness of the full weighted holomorphic half-plane space

The original weighted L² norm controls coefficient differences uniformly on every
actual compact subset of the upper half-plane. Ambient L² limits therefore have
holomorphic representatives, obtained as locally uniform limits and identified
by an almost-everywhere convergent subsequence. This proves closedness of the
original submodule and completeness of its unchanged inherited norm.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ComplexConjugate ENNReal NNReal Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman

open LiZhongQC

private theorem halfPlane_coefficients_uniformCauchyOn (u : ℕ → HalfPlane)
    (hu : CauchySeq (fun n => (u n).val)) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ upperHalf) :
    UniformCauchySeqOn (fun n => coefficient (u n)) atTop K := by
  obtain ⟨C, hC, hbound⟩ := halfPlane_evaluation_sub_bound_on_compact hK hKH
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  have hC1 : 0 < C + 1 := add_pos_of_nonneg_of_pos hC zero_lt_one
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / (C + 1)) (div_pos hε hC1)
  refine ⟨N, fun m hm n hn z hz => ?_⟩
  have hmn : ‖(u m).val - (u n).val‖ < ε / (C + 1) := by
    simpa only [dist_eq_norm_sub] using hN m hm n hn
  calc
    dist (coefficient (u m) z) (coefficient (u n) z) =
        ‖coefficient (u m) z - coefficient (u n) z‖ := dist_eq_norm_sub _ _
    _ ≤ C * ‖(u m).val - (u n).val‖ := hbound (u m) (u n) z hz
    _ ≤ (C + 1) * ‖(u m).val - (u n).val‖ :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
    _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left hmn hC1
    _ = ε := mul_div_cancel₀ ε hC1.ne'

private theorem halfPlane_coefficients_has_holomorphic_limit (u : ℕ → HalfPlane)
    (hu : CauchySeq (fun n => (u n).val)) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ upperHalf ∧
      TendstoLocallyUniformlyOn (fun n => coefficient (u n)) φ atTop upperHalf := by
  let φ : ℂ → ℂ := fun z => limUnder atTop (fun n => coefficient (u n) z)
  have hpoint : ∀ z ∈ upperHalf,
      Tendsto (fun n => coefficient (u n) z) atTop (𝓝 (φ z)) := by
    intro z hz
    have hs : ({z} : Set ℂ) ⊆ upperHalf := singleton_subset_iff.mpr hz
    have hc : CauchySeq (fun n => coefficient (u n) z) :=
      (halfPlane_coefficients_uniformCauchyOn u hu isCompact_singleton hs).cauchySeq (by simp)
    exact hc.tendsto_limUnder
  have hlocal : TendstoLocallyUniformlyOn
      (fun n => coefficient (u n)) φ atTop upperHalf := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_upperHalf).mpr
    intro K hKH hK
    have hc := halfPlane_coefficients_uniformCauchyOn u hu hK hKH
    exact hc.tendstoUniformlyOn_of_tendsto (fun z hz => hpoint z (hKH hz))
  exact ⟨φ, hlocal.differentiableOn
    (Eventually.of_forall fun n => coefficient_holomorphic (u n)) isOpen_upperHalf, hlocal⟩

private theorem halfPlaneMeasure_ae_mem :
    ∀ᵐ z ∂halfPlaneMeasure, z ∈ upperHalf := by
  change ∀ᵐ z ∂((volume.restrict upperHalf).withDensity
    (fun z => (halfPlaneWeight z : ℝ≥0∞))), z ∈ upperHalf
  exact (withDensity_absolutelyContinuous (volume.restrict upperHalf)
    (fun z => (halfPlaneWeight z : ℝ≥0∞))).ae_le
      (ae_restrict_mem isOpen_upperHalf.measurableSet)

private theorem halfPlane_mem_of_tendsto_of_holomorphic_limit
    {u : ℕ → Lp ℂ 2 halfPlaneMeasure} {v : Lp ℂ 2 halfPlaneMeasure}
    (hu : ∀ n, u n ∈ holomorphicL2Submodule upperHalf halfPlaneMeasure)
    (hlim : Tendsto u atTop (𝓝 v)) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ upperHalf)
    (hpoint : ∀ z ∈ upperHalf,
      Tendsto (fun n => coefficient (⟨u n, hu n⟩ : HalfPlane) z) atTop (𝓝 (φ z))) :
    v ∈ holomorphicL2Submodule upperHalf halfPlaneMeasure := by
  have hmeasure := tendstoInMeasure_of_tendsto_Lp hlim
  obtain ⟨ns, hns, hseq⟩ := hmeasure.exists_seq_tendsto_ae
  have hreps : ∀ᵐ z ∂halfPlaneMeasure, ∀ n : ℕ,
      u n z = coefficient (⟨u n, hu n⟩ : HalfPlane) z :=
    ae_all_iff.mpr (fun n => coefficient_ae (⟨u n, hu n⟩ : HalfPlane))
  change ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ upperHalf ∧ (v : ℂ → ℂ) =ᵐ[halfPlaneMeasure] ψ
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hseq, hreps, halfPlaneMeasure_ae_mem] with z hzseq hzrep hzH
  have hfun : (fun k : ℕ => u (ns k) z) =
      (fun k : ℕ => coefficient (⟨u (ns k), hu (ns k)⟩ : HalfPlane) z) :=
    funext fun k => hzrep (ns k)
  rw [hfun] at hzseq
  exact tendsto_nhds_unique hzseq ((hpoint z hzH).comp hns.tendsto_atTop)

/-- The original holomorphic half-plane carrier is closed in its original weighted L² space. -/
theorem halfPlane_holomorphicL2Submodule_isClosed :
    IsClosed (holomorphicL2Submodule upperHalf halfPlaneMeasure :
      Set (Lp ℂ 2 halfPlaneMeasure)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu hlim
  let U : ℕ → HalfPlane := fun n => ⟨u n, hu n⟩
  have hC : CauchySeq (fun n => (U n).val) := hlim.cauchySeq
  obtain ⟨φ, hφ, hlocal⟩ := halfPlane_coefficients_has_holomorphic_limit U hC
  exact halfPlane_mem_of_tendsto_of_holomorphic_limit hu hlim hφ
    (fun z hz => hlocal.tendsto_at hz)

/-- The full original half-plane space is complete for its unchanged weighted L² norm. -/
instance instCompleteSpaceHalfPlane : CompleteSpace HalfPlane := by
  have hS : IsComplete (holomorphicL2Submodule upperHalf halfPlaneMeasure :
      Set (Lp ℂ 2 halfPlaneMeasure)) := halfPlane_holomorphicL2Submodule_isClosed.isComplete
  exact hS.completeSpace_coe

end LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman
