/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.IdealTriangleIsometries
public import Mathlib.Topology.Order.IntermediateValue
/-!
# Analytic radius balance

This module proves the scalar closing equation used in a prescribed-angle construction.
The construction of an actual polygon is a separate geometric obligation.
-/

@[expose] public section
open Set Filter
open scoped Topology
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- The actual scalar balance governing the tangential prescribed-angle construction. -/
def polygonAngleBalance {n : ℕ} (θ : Fin n → ℝ) (d : ℝ) : ℝ :=
  ∑ i,Real.arcsin (Real.cos (θ i / 2) / Real.cosh d)

theorem polygonAngleBalance_continuous {n : ℕ} (θ : Fin n → ℝ) : Continuous (polygonAngleBalance θ) := by
  apply continuous_finsetSum
  intro i _
  exact Real.continuous_arcsin.comp (continuous_const.div Real.continuous_cosh (fun d => (Real.cosh_pos d).ne'))

theorem polygonAngleBalance_zero {n : ℕ} (θ : Fin n → ℝ) (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) :
    polygonAngleBalance θ 0 = ((n : ℝ) * Real.pi - ∑ i,θ i) / 2 := by
  unfold polygonAngleBalance
  simp only [Real.cosh_zero,div_one]
  calc
    ∑ i,Real.arcsin (Real.cos (θ i / 2)) = ∑ i,(Real.pi / 2 - θ i / 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.arcsin_eq_pi_div_two_sub_arccos,Real.arccos_cos (by linarith only [(hθ i).1])
        (by linarith only [(hθ i).2,Real.pi_pos])]
    _ = _ := by simp only [Finset.sum_sub_distrib,← Finset.sum_div,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

/-- The hyperbolic denominator diverges with its radius. -/
theorem polygonBalance_cosh_tendsto : Tendsto Real.cosh atTop atTop := by
  have he : Tendsto (fun d : ℝ => Real.exp d / 2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num) Real.tendsto_exp_atTop
  apply tendsto_atTop_mono _ he
  intro d
  rw [Real.cosh_eq]
  linarith only [Real.exp_pos (-d)]

theorem polygonAngleBalance_tendsto_zero {n : ℕ} (θ : Fin n → ℝ) :
    Tendsto (polygonAngleBalance θ) atTop (𝓝 0) := by
  have ht (i : Fin n) : Tendsto (fun d : ℝ => Real.arcsin (Real.cos (θ i / 2) / Real.cosh d)) atTop (𝓝 0) := by
    have he := (Real.continuous_arcsin.tendsto 0).comp
      (polygonBalance_cosh_tendsto.const_div_atTop (Real.cos (θ i / 2)))
    simpa only [Function.comp_def,Real.arcsin_zero] using he
  change Tendsto (fun d : ℝ => ∑ i,Real.arcsin (Real.cos (θ i / 2) / Real.cosh d)) atTop (𝓝 0)
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => ht i)

theorem polygonAngleBalance_strictAntiOn {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) : StrictAntiOn (polygonAngleBalance θ) (Ici 0) := by
  intro x hx y hy hxy
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  apply Finset.sum_lt_sum_of_nonempty hne
  intro i _
  have hc : 0 < Real.cos (θ i / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [(hθ i).1,Real.pi_pos],by linarith only [(hθ i).2]⟩
  apply Real.arcsin_lt_arcsin
  · exact (by norm_num : (-1 : ℝ) ≤ 0).trans (div_pos hc (Real.cosh_pos y)).le
  · exact div_lt_div_of_pos_left hc (Real.cosh_pos x) (Real.cosh_strictMonoOn hx hy hxy)
  · exact (div_le_one (Real.cosh_pos x)).mpr ((Real.cos_le_one _).trans (Real.one_le_cosh x))

/-- The angle-sum condition supplies a genuine positive solution of the analytic closing equation. -/
theorem polygonAngleBalance_exists_positive {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi)
    (hsum : ∑ i,θ i < ((n : ℝ)-2)*Real.pi) :
    ∃ d : ℝ,0 < d ∧ polygonAngleBalance θ d = Real.pi := by
  have h0 : Real.pi < polygonAngleBalance θ 0 := by rw [polygonAngleBalance_zero θ hθ]; nlinarith only [hsum]
  have hlim := polygonAngleBalance_tendsto_zero θ
  have hev : ∀ᶠ d in atTop,polygonAngleBalance θ d < Real.pi := (tendsto_order.mp hlim).2 _ Real.pi_pos
  obtain ⟨R,hR0,hR⟩ := ((eventually_gt_atTop (0 : ℝ)).and hev).exists
  obtain ⟨d,hd,he⟩ := intermediate_value_Icc' hR0.le (polygonAngleBalance_continuous θ).continuousOn ⟨hR.le,h0.le⟩
  refine ⟨d,?_,he⟩
  apply lt_of_le_of_ne hd.1
  intro hz
  rw [← hz] at he
  rw [he] at h0
  exact (lt_irrefl Real.pi) h0

/-- The radius solving the prescribed-angle balance is unique. -/
theorem polygonAngleBalance_existsUnique_positive {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi)
    (hsum : ∑ i,θ i < ((n : ℝ)-2)*Real.pi) :
    ∃! d : ℝ,0 < d ∧ polygonAngleBalance θ d = Real.pi := by
  obtain ⟨d,hd,he⟩ := polygonAngleBalance_exists_positive θ hθ hsum
  refine ⟨d,⟨hd,he⟩,?_⟩
  intro r hr
  exact (polygonAngleBalance_strictAntiOn hn θ hθ).injOn hr.1.le hd.le (hr.2.trans he.symm)

end
end LowDimensionalTopology.Geometry.Polygon
