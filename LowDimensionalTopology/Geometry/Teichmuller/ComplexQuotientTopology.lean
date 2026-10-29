module

public import LowDimensionalTopology.Geometry.Teichmuller.ComplexQuasiconformalSmoothing
public import LowDimensionalTopology.Geometry.Teichmuller.ComplexBeltramiMetricContinuity
public import LowDimensionalTopology.Geometry.Teichmuller.NativeTeichmullerMetric
public import Mathlib.Tactic.Linarith

/-!
# The actual coefficient quotient and the quasiconformal metric

Quantitative smoothing is used only to find close smooth coefficients in a
prescribed actual marked-surface class. The quotient universal property then
compares the two already defined topologies.
-/

@[expose] public section
noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The actual QC infimum can be tested using the two fixed native representatives. -/
theorem exists_quasiconformal_map_of_distance_lt
    (M N : MarkedRiemannSurface.{u, u} R) {δ : ℝ}
    (hδ : TeichmullerSpace.fromQCDistance R
      (TeichmullerSpace.mk M) (TeichmullerSpace.mk N) < δ) :
    ∃ (f : M.carrier ≃ₜ N.carrier) (K : ℝ), 1 ≤ K ∧
      (let := M.surface.toRiemannAtlas.toChartedSpace
       let := N.surface.toRiemannAtlas.toChartedSpace
       LiZhongQC.IsKQCRS f K) ∧ Real.log K < δ ∧
      ContinuousMap.Homotopic
        ((_root_.toContinuousMap f).comp M.markingMap) N.markingMap := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := M.surface.toRiemannAtlas.toChartedSpace
  let := N.surface.toRiemannAtlas.toChartedSpace
  let := M.surface.connectedSpace
  have hne := QCBookMetric.admissibleLogDilatations_nonempty
    (TeichmullerSpace.toSource R (TeichmullerSpace.mk M))
    (TeichmullerSpace.toSource R (TeichmullerSpace.mk N))
  obtain ⟨d, hd, hdδ⟩ := exists_lt_of_csInf_lt hne hδ
  obtain ⟨m₁, m₂, g, hm₁, hm₂, hg, hhom, rfl⟩ := hd
  change (Quot.mk _ m₁ : LiZhongQC.TeichSpace X) = Quot.mk _ M.toSource at hm₁
  change (Quot.mk _ m₂ : LiZhongQC.TeichSpace X) = Quot.mk _ N.toSource at hm₂
  obtain ⟨f, hf, hle, hfh⟩ := LiZhongQC.s29_m_transport
    (LiZhongQC.s29_m_equiv_of_eq hm₁) (LiZhongQC.s29_m_equiv_of_eq hm₂) hg hhom
  have hlog := LiZhongQC.s29_m_half_log_mono hf hg hle
  refine ⟨f, _, LiZhongQC.s29_m_one_le_toReal hf,
    LiZhongQC.s29_m_isKQCRS_maxDil hf, by linarith, ?_⟩
  exact hfh

/-- A sufficiently small actual QC metric displacement has a realized smooth
coefficient close to the original actual marking. -/
theorem exists_close_coefficient_of_distance_lt
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})
    (M : MarkedRiemannSurface.{u, u} R) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ q : TeichmullerSpace.{u, u} R,
      TeichmullerSpace.fromQCDistance R (TeichmullerSpace.mk M) q < δ →
        ∃ P : MarkedRiemannSurface.{u, u} R,
          TeichmullerSpace.mk P = q ∧
          ‖P.beltramiCoefficient - M.beltramiCoefficient‖ < ε := by
  let r : ℝ := min (1 / 4) (ε / 8)
  have hr : 0 < r := lt_min (by norm_num) (by linarith)
  have hrquarter : r ≤ 1 / 4 := min_le_left _ _
  have hreps : r ≤ ε / 8 := min_le_right _ _
  have hr1 : r < 1 := lt_of_le_of_lt hrquarter (by norm_num)
  let δ : ℝ := Real.log ((1 + r / 2) / (1 - r / 2))
  have hden : 0 < 1 - r / 2 := by linarith
  have hfrac : 1 < (1 + r / 2) / (1 - r / 2) := by
    rw [one_lt_div hden]
    linarith
  have hδ : 0 < δ := Real.log_pos hfrac
  refine ⟨δ, hδ, fun q => ?_⟩
  refine Quotient.inductionOn q (fun N hq => ?_)
  obtain ⟨f, K, hK, hf, hlog, hhom⟩ := exists_quasiconformal_map_of_distance_lt M N hq
  have hKfrac : K < (1 + r / 2) / (1 - r / 2) := by
    have h := (Real.log_lt_iff_lt_exp (lt_of_lt_of_le zero_lt_one hK)).1 hlog
    rwa [Real.exp_log (lt_trans zero_lt_one hfrac)] at h
  have hk : (K - 1) / (K + 1) < r / 2 := by
    have hc := (lt_div_iff₀ hden).1 hKfrac
    rw [div_lt_iff₀ (by linarith : 0 < K + 1)]
    nlinarith
  have hk0 : 0 ≤ (K - 1) / (K + 1) :=
    div_nonneg (sub_nonneg.mpr hK) (by linarith)
  have hs : (K - 1) / (K + 1) + r / 2 < r := by linarith
  obtain ⟨P, hP, hnorm⟩ := exists_close_marking_of_quasiconformal_smoothing
    hsmooth M N f hK hf hhom (by linarith : 0 < r / 2) (hs.trans hr1)
  refine ⟨P, hP, hnorm.trans_lt ?_⟩
  have hrat : 2 * ((K - 1) / (K + 1) + r / 2) /
      (1 - ((K - 1) / (K + 1) + r / 2)) ≤ 2 * r / (1 - r) := by
    rw [div_le_div_iff₀ (by linarith : 0 < 1 - ((K - 1) / (K + 1) + r / 2))
      (sub_pos.mpr hr1)]
    nlinarith
  refine hrat.trans_lt ?_
  rw [div_lt_iff₀ (sub_pos.mpr hr1)]
  nlinarith [mul_le_mul_of_nonneg_left hrquarter hε.le]

end MarkedRiemannSurface

namespace TeichmullerSpace

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- Quantitative global smoothing makes the identity from the actual QC metric
to the actual realized-coefficient quotient continuous. -/
theorem continuous_fromQC_to_beltrami_of_smoothing {g : ℕ} (hg : 1 < g)
    (hgenus : R.HasGenus g) (hPresentation : Unproved.HandleGroupPresentation g)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u}) :
    @Continuous (TeichmullerSpace.{u, u} R) (TeichmullerSpace.{u, u} R)
      (fromQCMetricSpace R hg hgenus hPresentation).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (beltramiTopology R) id := by
  let : MetricSpace (TeichmullerSpace.{u, u} R) :=
    fromQCMetricSpace R hg hgenus hPresentation
  apply continuous_def.2
  intro U hU
  apply Metric.isOpen_iff.2
  intro q hq
  obtain ⟨M, rfl⟩ := Quotient.exists_rep q
  have hpre : IsOpen ((RealizedBeltramiCoefficients.beta :
      RealizedBeltramiCoefficients.{u, u} R → TeichmullerSpace.{u, u} R) ⁻¹' U) :=
    hU.preimage RealizedBeltramiCoefficients.continuous_beta
  have hM : RealizedBeltramiCoefficients.ofMarked M ∈
      (RealizedBeltramiCoefficients.beta : RealizedBeltramiCoefficients.{u, u} R →
        TeichmullerSpace.{u, u} R) ⁻¹' U := by
    change RealizedBeltramiCoefficients.beta (RealizedBeltramiCoefficients.ofMarked M) ∈ U
    rw [RealizedBeltramiCoefficients.beta_ofMarked]
    change mk M ∈ U at hq
    exact hq
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hpre _ hM
  obtain ⟨δ, hδ, hrep⟩ :=
    MarkedRiemannSurface.exists_close_coefficient_of_distance_lt hsmooth M hε
  refine ⟨δ, hδ, fun p hp => ?_⟩
  have hp' : fromQCDistance R (mk M) p < δ := by
    change dist p (mk M) < δ at hp
    rw [dist_comm] at hp
    exact hp
  obtain ⟨P, hP, hnorm⟩ := hrep p hp'
  have hclose : RealizedBeltramiCoefficients.ofMarked P ∈
      Metric.ball (RealizedBeltramiCoefficients.ofMarked M) ε := by
    change dist P.beltramiCoefficient M.beltramiCoefficient < ε
    rwa [dist_eq_norm]
  have hin := hball hclose
  change RealizedBeltramiCoefficients.beta (RealizedBeltramiCoefficients.ofMarked P) ∈ U at hin
  rw [RealizedBeltramiCoefficients.beta_ofMarked, hP] at hin
  exact hin

/-- The unconditional quantitative coefficient estimate descends through the
actual coinduced quotient to the actual QC metric topology. -/
theorem continuous_beltrami_to_fromQC {g : ℕ} (hg : 1 < g)
    (hgenus : R.HasGenus g) (hPresentation : Unproved.HandleGroupPresentation g) :
    @Continuous (TeichmullerSpace.{u, u} R) (TeichmullerSpace.{u, u} R)
      (beltramiTopology R)
      (fromQCMetricSpace R hg hgenus hPresentation).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      id := by
  change @Continuous (TeichmullerSpace.{u, u} R) (TeichmullerSpace.{u, u} R)
    (TopologicalSpace.coinduced
      (RealizedBeltramiCoefficients.beta : RealizedBeltramiCoefficients.{u, u} R →
        TeichmullerSpace.{u, u} R) inferInstance)
    (fromQCMetricSpace R hg hgenus hPresentation).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    id
  rw [continuous_coinduced_dom]
  exact RealizedBeltramiCoefficients.continuous_beta_fromQCMetric hg hgenus hPresentation

/-- The two actual topologies agree under exactly the displayed quantitative
global QC smoothing theorem. Both continuity directions have full proof bodies. -/
theorem beltramiTopology_eq_fromQC_of_smoothing {g : ℕ} (hg : 1 < g)
    (hgenus : R.HasGenus g) (hPresentation : Unproved.HandleGroupPresentation g)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u}) :
    beltramiTopology R =
      (fromQCMetricSpace R hg hgenus hPresentation).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  apply le_antisymm
  · exact continuous_id_iff_le.mp
      (continuous_beltrami_to_fromQC R hg hgenus hPresentation)
  · exact continuous_id_iff_le.mp
      (continuous_fromQC_to_beltrami_of_smoothing R hg hgenus hPresentation hsmooth)

end TeichmullerSpace
end LowDimensionalTopology.Geometry.Teichmuller
