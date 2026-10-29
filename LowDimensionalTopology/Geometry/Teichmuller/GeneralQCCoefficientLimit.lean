/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCRecursiveComparisons

/-!
# Coefficient limits of original Cauchy sequences

A fast subsequence of an arbitrary original Cauchy sequence supplies the
recursively constructed actual markings. Their compatible coefficients have
a limit in the actual closed Banach subspace. The uniform subunit bound
keeps that limit inside the unit ball. The actual coefficient projection
then gives a limit for the same original classes and the whole sequence.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC
universe u

variable (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
  {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
  (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
    ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)

/-- An arbitrary Cauchy sequence of original common-universe marked classes
has a limit in that same original quotient. All coefficient controls and
representatives are constructed internally from its Cauchy property. -/
theorem commonCarrier_cauchySeq_tendsto (s : ℕ → Space.{u, u} R)
    (hs : letI := metricSpace.{u, u} R hp hfixed; CauchySeq s) :
    letI := distanceTopology.{u, u} R
    ∃ a : Space.{u, u} R, Tendsto s atTop (𝓝 a) := by
  let := metricSpace.{u, u} R hp hfixed
  obtain ⟨φ, hφ, hbound⟩ := Metric.exists_subseq_bounded_of_cauchySeq s hs
    (fun j => (1 / 2 : ℝ) ^ j) (fun _ => by positivity)
  have hfast (j : ℕ) : distance (s (φ j)) (s (φ (j + 1))) < (1 / 2 : ℝ) ^ j := by
    rw [distance_symm]
    exact hbound j (φ (j + 1)) (hφ (Nat.lt_succ_self j)).le
  obtain ⟨g, hg, k, hk₀, hk, hnorm, hC⟩ :=
    exists_cauchy_marking_coefficients R hp (s ∘ φ) hfast
  obtain ⟨ν, hν⟩ := cauchySeq_tendsto_of_complete hC
  have hνnorm : ‖ν‖ ≤ k := le_of_tendsto hν.norm (Eventually.of_forall hnorm)
  let b : GammaMeasurableBeltrami.Ball Γ := ⟨ν, by
    rw [Metric.mem_ball, dist_zero_right]
    exact hνnorm.trans_lt hk⟩
  have hball : Tendsto (fun j => markingBall R hp (g j)) atTop (𝓝 b) :=
    tendsto_subtype_rng.2 hν
  have hprojected := coefficientProjection_tendsto R hp hball
  have hsub : Tendsto (s ∘ φ) atTop (𝓝 (coefficientProjection R hp b)) := by
    apply hprojected.congr
    intro j
    exact (coefficientProjection_eq_mk R hp hfixed (g j)).trans (hg j)
  exact ⟨coefficientProjection R hp b,
    tendsto_nhds_of_cauchySeq_of_subseq hs hφ.tendsto_atTop hsub⟩

/-- The original full-log metric is complete for targets on the original
reference universe. No compactness, genus or finite-type premise is used. -/
theorem commonCarrier_completeSpace :
    letI := metricSpace.{u, u} R hp hfixed
    CompleteSpace (Space.{u, u} R) := by
  let := metricSpace.{u, u} R hp hfixed
  exact Metric.complete_of_cauchySeq_tendsto
    (commonCarrier_cauchySeq_tendsto R hp hfixed)

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
