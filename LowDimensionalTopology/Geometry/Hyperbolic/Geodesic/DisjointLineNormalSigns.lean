module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HalfPlaneLorentzReflections
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FunProp

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The existing native signed normal coordinate is continuous. -/
theorem HalfPlaneLine.normalTimeAt_continuous (L : HalfPlaneLine) :
    Continuous L.normalTimeAt := by
  cases L with
  | vertical a =>
    change Continuous (fun z : ℍ => (HalfPlaneLine.vertical a).normalTimeAt z)
    simp_rw [HalfPlaneLine.normalTimeAt_vertical]
    exact (continuous_const.sub UpperHalfPlane.continuous_re).div
      UpperHalfPlane.continuous_im (fun z => z.im_ne_zero)
  | circle c r hr =>
    change Continuous (fun z : ℍ => (HalfPlaneLine.circle c r hr).normalTimeAt z)
    simp_rw [HalfPlaneLine.normalTimeAt_circle]
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro z
      exact mul_ne_zero (mul_ne_zero (by norm_num) hr.ne') z.im_ne_zero

/-- An entire disjoint native line lies strictly on one signed side. -/
theorem HalfPlaneLine.normalTimeAt_mul_pos_of_disjoint (L M : HalfPlaneLine)
    (hLM : Disjoint L.carrier M.carrier) {p q : ℍ}
    (hp : p ∈ M.carrier) (hq : q ∈ M.carrier) :
    0 < L.normalTimeAt p * L.normalTimeAt q := by
  obtain ⟨γ, hγ, hrange⟩ := M.exists_isometric_param
  obtain ⟨a, rfl⟩ : p ∈ range γ := by rw [hrange]; exact hp
  obtain ⟨b, rfl⟩ : q ∈ range γ := by rw [hrange]; exact hq
  let f : ℝ → ℝ := fun t => L.normalTimeAt (γ t)
  have hn (t : ℝ) : f t ≠ 0 := by
    intro ht
    exact disjoint_left.mp hLM ((L.normalTimeAt_eq_zero_iff (γ t)).mp ht)
      (hrange ▸ mem_range_self t)
  have hf : Continuous f := L.normalTimeAt_continuous.comp hγ.continuous
  change 0 < f a * f b
  by_contra hab
  have hle : f a * f b ≤ 0 := le_of_not_gt hab
  have hpos : 0 < f a * f a := mul_self_pos.mpr (hn a)
  have hzero : (0 : ℝ) ∈ range (fun t => f a * f t) :=
    intermediate_value_univ b a (continuous_const.mul hf) ⟨hle, hpos.le⟩
  obtain ⟨t, ht⟩ := hzero
  exact mul_ne_zero (hn a) (hn t) ht

end LowDimensionalTopology.Geometry.Hyperbolic
