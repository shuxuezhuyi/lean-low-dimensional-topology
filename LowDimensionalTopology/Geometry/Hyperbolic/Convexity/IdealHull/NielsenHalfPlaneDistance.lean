/- Actual half-plane distance for the Nielsen consumer, 2026-10-20. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PointLineFormulas
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.IsometryClassification
public import Mathlib.Topology.Order.LocalExtr
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Set Filter
open scoped UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic

/-- On the opposite side of an actual complete boundary line, distance to
any set containing that line and lying behind it is exactly line distance. -/
theorem nielsen_infDist_eq_vertical_pointDist (C : Set ℍ)
    (haxis : (HalfPlaneLine.vertical 0).carrier ⊆ C)
    (hleft : C ⊆ {y : ℍ | y.re ≤ 0}) (x : ℍ) (hx : 0 < x.re) :
    Metric.infDist x C = (HalfPlaneLine.vertical 0).pointDist x := by
  apply le_antisymm
  · exact Metric.infDist_le_infDist_of_subset haxis ⟨UpperHalfPlane.I, rfl⟩
  · apply (Metric.le_infDist ⟨UpperHalfPlane.I, haxis rfl⟩).mpr
    intro y hy
    let p := metricProbe 0 y.im y.im_pos
    have hp : p ∈ (HalfPlaneLine.vertical 0).carrier := rfl
    have hc : Real.cosh (dist x p) ≤ Real.cosh (dist x y) := by
      rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist']
      change ((x.re - 0) ^ 2 + x.im ^ 2 + y.im ^ 2) / (2 * x.im * y.im) ≤ _
      apply div_le_div_of_nonneg_right ?_ (by positivity)
      have hyre : y.re ≤ 0 := hleft hy
      nlinarith [sq_nonneg y.re, mul_nonpos_of_nonneg_of_nonpos hx.le hyre]
    have hd : dist x p ≤ dist x y := by
      simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hc
    exact (Metric.infDist_le_dist_of_mem hp).trans hd

/-- Moving horizontally away from the actual boundary line strictly raises
distance, so no exterior point is a local maximum. Closedness is unnecessary. -/
theorem nielsen_infDist_not_isLocalMax_of_right (C : Set ℍ)
    (haxis : (HalfPlaneLine.vertical 0).carrier ⊆ C)
    (hleft : C ⊆ {y : ℍ | y.re ≤ 0}) (x : ℍ) (hx : 0 < x.re) :
    ¬ IsLocalMax (fun z : ℍ => Metric.infDist z C) x := by
  intro hmax
  let γ : ℝ → ℍ := fun u => metricProbe (x.re + u) x.im x.im_pos
  have hγ : Continuous γ := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun u : ℝ => (⟨x.re + u, x.im⟩ : ℂ))
    have he : (fun u : ℝ => (⟨x.re + u, x.im⟩ : ℂ)) =
        (fun u : ℝ => ((x.re + u : ℝ) : ℂ) + (x.im : ℂ) * Complex.I) := by
      funext u
      apply Complex.ext <;> simp
    rw [he]
    fun_prop
  have hγ0 : γ 0 = x := by
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [γ, metricProbe]
  have hev : ∀ᶠ u : ℝ in 𝓝 0, Metric.infDist (γ u) C ≤ Metric.infDist x C := by
    have ht : ContinuousAt γ 0 := hγ.continuousAt
    have he : ∀ᶠ z : ℍ in 𝓝 (γ 0), Metric.infDist z C ≤ Metric.infDist x C := by
      rw [hγ0]
      exact hmax
    exact ht.tendsto.eventually he
  obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp hev
  have hu : 0 < ε / 2 := half_pos hε
  have hnear : dist (ε / 2) (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hu]
    linarith
  have hle := hbound hnear
  have hright : 0 < (γ (ε / 2)).re := by
    change 0 < x.re + ε / 2
    linarith
  rw [nielsen_infDist_eq_vertical_pointDist C haxis hleft _ hright,
    nielsen_infDist_eq_vertical_pointDist C haxis hleft x hx] at hle
  have hs := Real.sinh_le_sinh.mpr hle
  rw [verticalLine_pointDist_sinh, verticalLine_pointDist_sinh, sub_zero, sub_zero,
    abs_of_pos hright, abs_of_pos hx] at hs
  change (x.re + ε / 2) / x.im ≤ x.re / x.im at hs
  have hh := (div_le_div_iff_of_pos_right x.im_pos).mp hs
  linarith

end LowDimensionalTopology.Geometry.Hyperbolic
