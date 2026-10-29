/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S27_TeichmullerExistence
public import LowDimensionalTopology.Geometry.Mobius.Classification.MobiusTypes
public import Mathlib.Analysis.SpecificLimits.Basic

public section

open Set Filter
open scoped Topology OnePoint

namespace LowDimensionalTopology.Geometry.Surfaces

noncomputable section

/-- A fixed hyperbolic displacement controls Euclidean distance to every finite ideal point. -/
private theorem smul_distance_real_le (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (z : UpperHalfPlane) (x : ℝ) :
    dist ((g • z : UpperHalfPlane) : ℂ) (x : ℂ) ≤
      Real.exp (dist z UpperHalfPlane.I) *
        dist ((g • UpperHalfPlane.I : UpperHalfPlane) : ℂ) (x : ℂ) := by
  let w := g • UpperHalfPlane.I
  have him : w.im ≤ dist (w : ℂ) (x : ℂ) := by
    have h := Complex.abs_im_le_norm ((w : ℂ) - (x : ℂ))
    simpa [dist_eq_norm, abs_of_pos w.im_pos] using h
  have he : 0 ≤ Real.exp (dist z UpperHalfPlane.I) - 1 := by
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr dist_nonneg)
  have hd := UpperHalfPlane.dist_coe_le (g • z) w
  have hs : dist (g • z) w = dist z UpperHalfPlane.I := by
    exact dist_smul g z UpperHalfPlane.I
  rw [hs] at hd
  calc
    dist ((g • z : UpperHalfPlane) : ℂ) (x : ℂ) ≤
        dist ((g • z : UpperHalfPlane) : ℂ) (w : ℂ) + dist (w : ℂ) (x : ℂ) :=
      dist_triangle _ _ _
    _ ≤ w.im * (Real.exp (dist z UpperHalfPlane.I) - 1) + dist (w : ℂ) (x : ℂ) :=
      add_le_add hd le_rfl
    _ ≤ dist (w : ℂ) (x : ℂ) * (Real.exp (dist z UpperHalfPlane.I) - 1) +
        dist (w : ℂ) (x : ℂ) := add_le_add (mul_le_mul_of_nonneg_right him he) le_rfl
    _ = _ := by dsimp only [w]; ring

/-- One sequence in a compact uniformizing group converges to a prescribed real ideal point
for every starting point of the upper half-plane. -/
theorem exists_uniformizing_sequence_tendsto_real
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hp : LiZhongQC.IsUniformization Γ p) (x : ℝ) :
    ∃ g : ℕ → Γ, ∀ z : UpperHalfPlane,
      Tendsto (fun n => (((g n : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z : UpperHalfPlane) : ℂ))
        atTop (𝓝 (x : ℂ)) := by
  have hnear : ∀ n : ℕ, ∃ g : Γ,
      dist ((g.val • UpperHalfPlane.I : UpperHalfPlane) : ℂ) (x : ℂ) <
        1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨g, hg, h⟩ := LiZhongQC.s27g_orbit_near hp x (ε := 1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨⟨g, hg⟩, by simpa only [dist_eq_norm] using h⟩
  choose g hg using hnear
  refine ⟨g, fun z => ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht : Tendsto (fun n : ℕ => Real.exp (dist z UpperHalfPlane.I) *
      (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  exact (smul_distance_real_le (g n) z x).trans_lt
    ((mul_lt_mul_of_pos_left (hg n) (Real.exp_pos _)).trans hn)

/-- A compact uniformizing group has a single sequence escaping to infinity at every starting
point; the convergence is in the actual one-point compactification. -/
theorem exists_uniformizing_sequence_tendsto_infty
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hp : LiZhongQC.IsUniformization Γ p) :
    ∃ g : ℕ → Γ, ∀ z : UpperHalfPlane,
      Tendsto (fun n => ((((g n : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z : UpperHalfPlane) : ℂ) :
        Mobius.ExtendedComplex)) atTop (𝓝 ∞) := by
  have hnear : ∀ n : ℕ, ∃ g : Γ,
      dist ((g.val • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ((n : ℝ) : ℂ) <
        1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨g, hg, h⟩ := LiZhongQC.s27g_orbit_near hp (n : ℝ)
      (ε := 1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨⟨g, hg⟩, by simpa only [dist_eq_norm] using h⟩
  choose g hg using hnear
  refine ⟨g, fun z => Mobius.tendsto_complex_coe_infty_of_norm ?_⟩
  have hbound : ∀ n : ℕ, (n : ℝ) - Real.exp (dist z UpperHalfPlane.I) ≤
      ‖(((g n).val • z : UpperHalfPlane) : ℂ)‖ := by
    intro n
    have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 := by
      exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hd : dist (((g n).val • z : UpperHalfPlane) : ℂ) ((n : ℝ) : ℂ) ≤
        Real.exp (dist z UpperHalfPlane.I) := by
      exact (smul_distance_real_le (g n) z (n : ℝ)).trans
        (mul_le_of_le_one_right (Real.exp_pos _).le ((hg n).le.trans hfrac))
    have hn := norm_le_norm_add_norm_sub' ((n : ℝ) : ℂ)
      (((g n).val • z : UpperHalfPlane) : ℂ)
    rw [Complex.norm_real, Real.norm_natCast, ← dist_eq_norm, dist_comm] at hn
    linarith
  apply tendsto_atTop_mono hbound
  simpa only [sub_eq_add_neg] using
    (tendsto_atTop_add_const_right atTop (-Real.exp (dist z UpperHalfPlane.I))
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))

/-- Every extended-real ideal point is the pointwise limit of one sequence of the original
compact uniformizing group, simultaneously for all upper-half-plane starting points. -/
theorem exists_uniformizing_sequence_tendsto_boundary
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hp : LiZhongQC.IsUniformization Γ p) (ξ : Mobius.ExtendedComplex)
    (hξ : ξ = ∞ ∨ ∃ x : ℝ, ξ = ((x : ℂ) : Mobius.ExtendedComplex)) :
    ∃ g : ℕ → Γ, ∀ z : UpperHalfPlane,
      Tendsto (fun n => ((((g n : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z : UpperHalfPlane) : ℂ) :
        Mobius.ExtendedComplex)) atTop (𝓝 ξ) := by
  rcases hξ with rfl | ⟨x, rfl⟩
  · exact exists_uniformizing_sequence_tendsto_infty hp
  · obtain ⟨g, hg⟩ := exists_uniformizing_sequence_tendsto_real hp x
    exact ⟨g, fun z => OnePoint.continuous_coe.continuousAt.tendsto.comp (hg z)⟩

end

end LowDimensionalTopology.Geometry.Surfaces
