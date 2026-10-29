module

public import LowDimensionalTopology.Geometry.Quasiconformal.SmoothBeltramiSolution
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Topology.Algebra.Support

/-!
# A smooth local solution for the original local Beltrami coefficient

A coefficient smooth only on an open plane domain is multiplied by a real
smooth bump whose entire closed support lies inside that domain. The resulting
actual compact coefficient agrees with the original one on an inner open set
and has a strict uniform bound. Smoothness off the original domain follows
from local equality to zero, without a global smoothness assumption.
The explicit regularity input then supplies a genuine plane homeomorphism
whose original-coefficient equation holds pointwise on that inner open set.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Localize an actual coefficient that is smooth only on an open set, preserving
it on an open neighborhood of the given point and controlling its norm everywhere.
The bound is strictly below one by the original bound at that point. -/
theorem exists_smooth_compact_beltrami_cutoff
    {μ : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ} (hU : IsOpen U) (hz₀ : z₀ ∈ U)
    (hμ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ U) (hsmall : ‖μ z₀‖ < 1) :
    ∃ (V : Set ℂ) (ν : ℂ → ℂ),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν ∧
      HasCompactSupport ν ∧ tsupport ν ⊆ U ∧ EqOn ν μ V ∧
      ∀ z, ‖ν z‖ ≤ (1 + ‖μ z₀‖) / 2 := by
  let k : ℝ := (1 + ‖μ z₀‖) / 2
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hμk : ‖μ z₀‖ < k := by dsimp [k]; linarith
  have hcont : ContinuousAt μ z₀ := (hμ.contDiffAt (hU.mem_nhds hz₀)).continuousAt
  have hN : U ∩ {z : ℂ | ‖μ z‖ < k} ∈ 𝓝 z₀ :=
    inter_mem (hU.mem_nhds hz₀) (hcont.norm (Iio_mem_nhds hμk))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 hN
  let χ : ContDiffBump z₀ :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let ν : ℂ → ℂ := fun z => χ z • μ z
  have hχS : tsupport (χ : ℂ → ℝ) ⊆ U ∩ {z : ℂ | ‖μ z‖ < k} := by
    rw [χ.tsupport_eq]
    change Metric.closedBall z₀ (ε / 2) ⊆ U ∩ {z : ℂ | ‖μ z‖ < k}
    exact (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεsub
  have hνs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν := by
    apply contDiff_iff_contDiffAt.2
    intro z
    by_cases hz : z ∈ tsupport (χ : ℂ → ℝ)
    · have hμz := hμ.contDiffAt (hU.mem_nhds (hχS hz).1)
      exact (χ.contDiffAt (n := ⊤)).smul hμz
    · have hzero : ν =ᶠ[𝓝 z] (0 : ℂ → ℂ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hz] with y hy
        change χ y • μ y = 0
        rw [show χ y = 0 from hy, zero_smul]
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hzero
  have hνc : HasCompactSupport ν := χ.hasCompactSupport.smul_right
  have hνU : tsupport ν ⊆ U :=
    (tsupport_smul_subset_left (χ : ℂ → ℝ) μ).trans fun z hz => (hχS hz).1
  have hVU : Metric.ball z₀ (ε / 4) ⊆ U := by
    intro z hz
    exact (hεsub (Metric.ball_subset_ball (by linarith) hz)).1
  have hEq : EqOn ν μ (Metric.ball z₀ (ε / 4)) := by
    intro z hz
    have hχ1 : χ z = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
    change χ z • μ z = μ z
    rw [hχ1, one_smul]
  have hνbound : ∀ z, ‖ν z‖ ≤ k := by
    intro z
    by_cases hz : z ∈ tsupport (χ : ℂ → ℝ)
    · calc
        ‖ν z‖ = χ z * ‖μ z‖ := by
          simp only [ν, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (χ.nonneg (x := z))]
        _ ≤ 1 * ‖μ z‖ :=
          mul_le_mul_of_nonneg_right (χ.le_one (x := z)) (norm_nonneg _)
        _ = ‖μ z‖ := one_mul _
        _ ≤ k := (hχS hz).2.le
    · have hχ0 : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp only [ν, hχ0, zero_smul, norm_zero]
      exact hk0
  exact ⟨Metric.ball z₀ (ε / 4), ν, Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), hVU, hνs, hνc, hνU, hEq, hνbound⟩

/-- Under the explicit elliptic regularity input, an actual coefficient smooth
only on its open domain has a genuine smooth plane homeomorphism solving its
original equation throughout an open neighborhood of the given point.
The same homeomorphism has a smooth inverse and positive Jacobian everywhere. -/
theorem exists_smooth_local_beltrami_homeomorph_of_regularity
    (hreg : LowDimensionalTopology.Unproved.Quasiconformal.SmoothCompactBeltramiRegularity)
    {μ : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ} (hU : IsOpen U) (hz₀ : z₀ ∈ U)
    (hμ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ U) (hsmall : ‖μ z₀‖ < 1) :
    ∃ (V : Set ℂ) (e : ℂ ≃ₜ ℂ),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e : ℂ → ℂ) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e.symm : ℂ → ℂ) ∧
      (∀ z ∈ V, dzbar (e : ℂ → ℂ) z = μ z * dz (e : ℂ → ℂ) z) ∧
      ∀ z, 0 < jacobian (e : ℂ → ℂ) z := by
  obtain ⟨V, ν, hV, hzV, hVU, hνs, hνc, _hνU, hνeq, hνbound⟩ :=
    exists_smooth_compact_beltrami_cutoff hU hz₀ hμ hsmall
  have hk : (1 + ‖μ z₀‖) / 2 < 1 := by linarith
  obtain ⟨e, he, hei, hPDE, hJ⟩ :=
    exists_smooth_beltrami_homeomorph_of_regularity hreg hk hνs hνc hνbound
  refine ⟨V, e, hV, hzV, hVU, he, hei, ?_, hJ⟩
  intro z hz
  simpa only [hνeq hz] using hPDE z

end LowDimensionalTopology.Geometry.Quasiconformal
