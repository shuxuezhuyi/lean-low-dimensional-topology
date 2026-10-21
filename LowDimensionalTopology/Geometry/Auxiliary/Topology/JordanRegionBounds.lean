module
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Tactic.Linarith
@[expose] public section
noncomputable section
open Set Topology
namespace LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- A bounded complementary component of a set contained in a genuine closed
ball lies strictly inside that ball. The proof uses an actual outward radial
ray, and requires no Jordan or finite-boundary hypothesis. -/
theorem norm_lt_of_bounded_complement_component
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {r : ℝ} (hr : 0 < r) (hC : C ⊆ Metric.closedBall (0:E) r)
    {z : E} (hzC : z ∉ C) (hbounded : Bornology.IsBounded (connectedComponentIn Cᶜ z)) :
    ‖z‖ < r := by
  by_contra hlt
  have hrz : r ≤ ‖z‖ := le_of_not_gt hlt
  have hn : 0 < ‖z‖ := hr.trans_le hrz
  let A : Set E := (fun t : ℝ => t • z) '' Ici (1:ℝ)
  have hA : IsPreconnected A :=
    isPreconnected_Ici.image _ (continuous_id.smul continuous_const).continuousOn
  have hzA : z ∈ A := ⟨1,le_rfl,one_smul ℝ z⟩
  have hAC : A ⊆ Cᶜ := by
    rintro x ⟨t,ht,rfl⟩ htC
    have ht' : 1 ≤ t := mem_Ici.mp ht
    by_cases he : t = 1
    · exact hzC (by simpa only [he,one_smul] using htC)
    · have ht1 : 1 < t := lt_of_le_of_ne ht' (Ne.symm he)
      have hnorm : ‖t • z‖ ≤ r := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using hC htC
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans ht1)] at hnorm
      nlinarith
  have hAcc : A ⊆ connectedComponentIn Cᶜ z := hA.subset_connectedComponentIn hzA hAC
  obtain ⟨M,hM⟩ := (isBounded_iff_forall_norm_le.mp (hbounded.subset hAcc))
  let t := max 1 ((M+1)/‖z‖)
  have ht1 : 1 ≤ t := le_max_left _ _
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hlarge : M+1 ≤ t*‖z‖ := (div_le_iff₀ hn).mp (le_max_right _ _)
  have hsmall := hM (t • z) ⟨t,ht1,rfl⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht0] at hsmall
  linarith

/-- The union of all bounded actual complementary components is strictly inside
every positive closed ball containing the original set. -/
theorem bounded_complement_regions_subset_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} {r : ℝ} (hr : 0 < r) (hC : C ⊆ Metric.closedBall (0:E) r) :
    {z | z ∉ C ∧ Bornology.IsBounded (connectedComponentIn Cᶜ z)} ⊆ Metric.ball (0:E) r := by
  intro z hz
  change dist z 0 < r
  rw [dist_zero_right]
  exact norm_lt_of_bounded_complement_component hr hC hz.1 hz.2

end LowDimensionalTopology.Geometry.Auxiliary.Topology
