module

public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedTeichmuller
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# A complete full-log metric on actual QC-marked classes

The distance is the infimum of log K over the actual marking-compatible maps.
It is exactly twice the imported half-log distance. The metric and completeness
are proved on the same actual QC-marked quotient; no identification with another
pre-existing topology is asserted.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller.QCBookMetric

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

open LiZhongQC

/-- Actual log-dilatations of marking-compatible quasiconformal maps. -/
def admissibleLogDilatations (p q : TeichSpace X) : Set ℝ :=
  {d | ∃ (m₁ : MarkedRS X) (m₂ : MarkedRS X)
      (f : m₁.X.carrier ≃ₜ m₂.X.carrier),
    Quot.mk _ m₁ = p ∧ Quot.mk _ m₂ = q ∧ IsQCRS f ∧
      ContinuousMap.Homotopic
        ((m₁.marking.trans f : X ≃ₜ m₂.X.carrier) : C(X, m₂.X.carrier))
        (m₂.marking : C(X, m₂.X.carrier)) ∧
      d = Real.log (maxDilatationRS f).toReal}

/-- The infimum of the full log-dilatations, with no factor one half. -/
def bookDistance (p q : TeichSpace X) : ℝ := sInf (admissibleLogDilatations p q)

theorem admissibleLogDilatations_nonneg (p q : TeichSpace X) :
    ∀ d ∈ admissibleLogDilatations p q, 0 ≤ d := by
  rintro d ⟨m₁, m₂, f, hp, hq, hf, hhom, rfl⟩
  have h := s29_m_half_log_nonneg hf
  linarith

theorem admissibleLogDilatations_bddBelow (p q : TeichSpace X) :
    BddBelow (admissibleLogDilatations p q) :=
  ⟨0, admissibleLogDilatations_nonneg p q⟩

variable [IsManifold 𝓘(ℂ) ω X]

theorem admissibleLogDilatations_nonempty (p q : TeichSpace X) :
    (admissibleLogDilatations p q).Nonempty := by
  obtain ⟨d, m₁, m₂, f, hp, hq, hf, hhom, hd⟩ := s29_m_teichSet_nonempty p q
  exact ⟨_, m₁, m₂, f, hp, hq, hf, hhom, rfl⟩

/-- Scaling the actual infimum gives precisely twice the source distance. -/
theorem bookDistance_eq_two_mul (p q : TeichSpace X) :
    bookDistance p q = 2 * teichDistance p q := by
  have hs := s29_m_teichSet_bddBelow p q
  have ht := admissibleLogDilatations_bddBelow p q
  have hsne := s29_m_teichSet_nonempty p q
  have htne := admissibleLogDilatations_nonempty p q
  change sInf (admissibleLogDilatations p q) = 2 * sInf (s29_m_teichSet p q)
  apply le_antisymm
  · have h : sInf (admissibleLogDilatations p q) / 2 ≤ sInf (s29_m_teichSet p q) := by
      apply le_csInf hsne
      rintro d ⟨m₁, m₂, f, hp, hq, hf, hhom, rfl⟩
      have hmem : Real.log (maxDilatationRS f).toReal ∈ admissibleLogDilatations p q :=
        ⟨m₁, m₂, f, hp, hq, hf, hhom, rfl⟩
      have hle := csInf_le ht hmem
      linarith
    linarith
  · apply le_csInf htne
    rintro d ⟨m₁, m₂, f, hp, hq, hf, hhom, rfl⟩
    have hmem : (1 / 2 : ℝ) * Real.log (maxDilatationRS f).toReal ∈
        s29_m_teichSet p q := ⟨m₁, m₂, f, hp, hq, hf, hhom, rfl⟩
    have hle := csInf_le hs hmem
    linarith

/-- Factor two preserves convergence of the real-valued distances for every
filter. This does not identify any independently defined quotient topology. -/
theorem tendsto_bookDistance_zero_iff {ι : Type*} {l : Filter ι}
    (p : ι → TeichSpace X) (q : TeichSpace X) :
    Tendsto (fun i => bookDistance (p i) q) l (𝓝 0) ↔
      Tendsto (fun i => teichDistance (p i) q) l (𝓝 0) := by
  constructor
  · intro h
    simpa [bookDistance_eq_two_mul] using h.div_const (2 : ℝ)
  · intro h
    have h' : Tendsto (fun i => (2 : ℝ) * teichDistance (p i) q) l
        (𝓝 ((2 : ℝ) * 0)) := tendsto_const_nhds.mul h
    simpa only [bookDistance_eq_two_mul, mul_zero] using h'

variable [T2Space X] [ConnectedSpace X] [CompactSpace X]

/-- The actual QC-marked quotient with the complete full-log metric.
The genus here is explicitly the source fundamental-group genus. -/
@[instance_reducible] def metricSpace {g : ℕ} (hg : 1 < g) (hX : HasGenus X g) :
    MetricSpace (TeichSpace X) where
  dist := bookDistance
  dist_self p := by rw [bookDistance_eq_two_mul, s29_m_teichDistance_self, mul_zero]
  dist_comm p q := by rw [bookDistance_eq_two_mul, bookDistance_eq_two_mul,
    s29_m_teichDistance_symm]
  dist_triangle p q r := by
    simp only [bookDistance_eq_two_mul]
    have h := s29_m_teichDistance_triangle p r q
    rw [s29_m_teichDistance_symm r q] at h
    linarith
  eq_of_dist_eq_zero {p q} h := by
    change bookDistance p q = 0 at h
    rw [bookDistance_eq_two_mul] at h
    apply teichDistance_eq_of_eq_zero hg hX p q
    linarith

/-- Sequential completeness of the source proof is completeness for the
actual factor-two metric, using Mathlib's metric-space convergence API. -/
theorem completeSpace {g : ℕ} (hg : 1 < g) (hX : HasGenus X g) :
    let := metricSpace hg hX
    CompleteSpace (TeichSpace X) := by
  let := metricSpace hg hX
  apply Metric.complete_of_cauchySeq_tendsto
  intro p hp
  have hp' : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      teichDistance (p m) (p n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hp (2 * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn
    change bookDistance (p m) (p n) < 2 * ε at h
    rw [bookDistance_eq_two_mul] at h
    linarith
  obtain ⟨q, hq⟩ := thm29_2_complete hg hX p hp'
  refine ⟨q, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  change Tendsto (fun n => bookDistance (p n) q) atTop (𝓝 0)
  exact (tendsto_bookDistance_zero_iff p q).2 hq

end LowDimensionalTopology.Geometry.Teichmuller.QCBookMetric
