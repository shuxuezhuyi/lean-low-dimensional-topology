module
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Radial coordinates for the Klein ball.

The Poincaré–Klein radial maps are continuous and inverse on the closed unit ball. Their
restrictions give homeomorphisms of both the open and the closed ball.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace LowDimensionalTopology.Geometry.Hyperbolic

def kleinRadialMap (x : E) : E := (2 / (1 + ‖x‖ ^ 2) : ℝ) • x

def inverseKleinRadialMap (x : E) : E := (1 / (1 + Real.sqrt (1 - ‖x‖ ^ 2)) : ℝ) • x

theorem kleinRadialMap_norm (x : E) : ‖kleinRadialMap x‖ = 2 * ‖x‖ / (1 + ‖x‖ ^ 2) := by
  rw [kleinRadialMap,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2 : ℝ) / (1 + ‖x‖ ^ 2))]
  ring

theorem inverseKleinRadialMap_norm (x : E) :
    ‖inverseKleinRadialMap x‖ = ‖x‖ / (1 + Real.sqrt (1 - ‖x‖ ^ 2)) := by
  rw [inverseKleinRadialMap,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity :
    0 < (1 : ℝ) / (1 + Real.sqrt (1 - ‖x‖ ^ 2)))]
  ring

theorem continuous_kleinRadialMap : Continuous (kleinRadialMap : E → E) := by
  change Continuous (fun x : E => (2 / (1 + ‖x‖ ^ 2) : ℝ) • x)
  exact (continuous_const.div (continuous_const.add (continuous_norm.pow 2))
    (fun x => ne_of_gt (by positivity : 0 < (1 : ℝ) + ‖x‖ ^ 2))).smul continuous_id

theorem continuous_inverseKleinRadialMap : Continuous (inverseKleinRadialMap : E → E) := by
  change Continuous (fun x : E => (1 / (1 + Real.sqrt (1 - ‖x‖ ^ 2)) : ℝ) • x)
  exact (continuous_const.div (continuous_const.add ((continuous_const.sub (continuous_norm.pow 2)).sqrt))
    (fun x => ne_of_gt (by positivity : 0 < (1 : ℝ) + Real.sqrt (1 - ‖x‖ ^ 2)))).smul continuous_id

theorem kleinRadialMap_mem_closedBall (x : E) :
    kleinRadialMap x ∈ Metric.closedBall (0 : E) 1 := by
  rw [mem_closedBall_zero_iff,kleinRadialMap_norm]
  apply (div_le_one (by positivity : 0 < 1 + ‖x‖ ^ 2)).mpr
  nlinarith [sq_nonneg (1 - ‖x‖)]

theorem inverseKleinRadialMap_mem_closedBall {x : E} (hx : x ∈ Metric.closedBall (0 : E) 1) :
    inverseKleinRadialMap x ∈ Metric.closedBall (0 : E) 1 := by
  rw [mem_closedBall_zero_iff,inverseKleinRadialMap_norm]
  apply (div_le_one (by positivity : 0 < 1 + Real.sqrt (1 - ‖x‖ ^ 2))).mpr
  have hh := mem_closedBall_zero_iff.mp hx
  linarith [Real.sqrt_nonneg (1 - ‖x‖ ^ 2)]

theorem kleinRadialMap_inverseKleinRadialMap {x : E} (hx : x ∈ Metric.closedBall (0 : E) 1) :
    kleinRadialMap (inverseKleinRadialMap x) = x := by
  have hn := mem_closedBall_zero_iff.mp hx
  have hs : Real.sqrt (1 - ‖x‖ ^ 2) ^ 2 = 1 - ‖x‖ ^ 2 :=
    Real.sq_sqrt (by nlinarith [norm_nonneg x])
  have hden : 1 + Real.sqrt (1 - ‖x‖ ^ 2) ≠ 0 := by positivity
  rw [kleinRadialMap,inverseKleinRadialMap_norm,inverseKleinRadialMap,smul_smul]
  have he : 2 / (1 + (‖x‖ / (1 + Real.sqrt (1 - ‖x‖ ^ 2))) ^ 2) *
      (1 / (1 + Real.sqrt (1 - ‖x‖ ^ 2))) = 1 := by
    apply (div_mul_eq_mul_div _ _ _).trans ?_
    apply (div_eq_one_iff_eq (by positivity)).mpr
    field_simp
    nlinarith
  rw [he,one_smul]

theorem kleinRadialMap_mem_ball {x : E} (hx : x ∈ Metric.ball (0 : E) 1) :
    kleinRadialMap x ∈ Metric.ball (0 : E) 1 := by
  rw [mem_ball_zero_iff,kleinRadialMap_norm]
  apply (div_lt_one (by positivity : 0 < 1 + ‖x‖ ^ 2)).mpr
  have hh := mem_ball_zero_iff.mp hx
  nlinarith [sq_pos_of_pos (sub_pos.mpr hh)]

theorem inverseKleinRadialMap_mem_ball {x : E} (hx : x ∈ Metric.ball (0 : E) 1) :
    inverseKleinRadialMap x ∈ Metric.ball (0 : E) 1 := by
  rw [mem_ball_zero_iff,inverseKleinRadialMap_norm]
  apply (div_lt_one (by positivity : 0 < 1 + Real.sqrt (1 - ‖x‖ ^ 2))).mpr
  have hh := mem_ball_zero_iff.mp hx
  linarith [Real.sqrt_nonneg (1 - ‖x‖ ^ 2)]

theorem kleinRadial_sqrt_identity {x : E} (hx : x ∈ Metric.closedBall (0 : E) 1) :
    Real.sqrt (1 - ‖kleinRadialMap x‖ ^ 2) = (1 - ‖x‖ ^ 2) / (1 + ‖x‖ ^ 2) := by
  have hn := mem_closedBall_zero_iff.mp hx
  have hF := mem_closedBall_zero_iff.mp (kleinRadialMap_mem_closedBall x)
  have hrad : 0 ≤ 1 - ‖kleinRadialMap x‖ ^ 2 := by nlinarith [norm_nonneg (kleinRadialMap x)]
  have hnum : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt hrad,kleinRadialMap_norm]
  field_simp
  ring

theorem inverseKleinRadialMap_kleinRadialMap {x : E} (hx : x ∈ Metric.closedBall (0 : E) 1) :
    inverseKleinRadialMap (kleinRadialMap x) = x := by
  rw [inverseKleinRadialMap,kleinRadial_sqrt_identity hx,kleinRadialMap,smul_smul]
  have he : 1 / (1 + (1 - ‖x‖ ^ 2) / (1 + ‖x‖ ^ 2)) * (2 / (1 + ‖x‖ ^ 2)) = 1 := by
    field_simp
    ring
  rw [he,one_smul]

def kleinClosedBallHomeomorph (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ↥(Metric.closedBall (0 : E) 1) ≃ₜ ↥(Metric.closedBall (0 : E) 1) where
  toFun x := ⟨kleinRadialMap x.val,kleinRadialMap_mem_closedBall x.val⟩
  invFun x := ⟨inverseKleinRadialMap x.val,inverseKleinRadialMap_mem_closedBall x.property⟩
  left_inv x := Subtype.ext (inverseKleinRadialMap_kleinRadialMap x.property)
  right_inv x := Subtype.ext (kleinRadialMap_inverseKleinRadialMap x.property)
  continuous_toFun := (continuous_kleinRadialMap.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_inverseKleinRadialMap.comp continuous_subtype_val).subtype_mk _

def kleinOpenBallHomeomorph (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ↥(Metric.ball (0 : E) 1) ≃ₜ ↥(Metric.ball (0 : E) 1) where
  toFun x := ⟨kleinRadialMap x.val,kleinRadialMap_mem_ball x.property⟩
  invFun x := ⟨inverseKleinRadialMap x.val,inverseKleinRadialMap_mem_ball x.property⟩
  left_inv x := Subtype.ext (inverseKleinRadialMap_kleinRadialMap (Metric.ball_subset_closedBall x.property))
  right_inv x := Subtype.ext (kleinRadialMap_inverseKleinRadialMap (Metric.ball_subset_closedBall x.property))
  continuous_toFun := (continuous_kleinRadialMap.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_inverseKleinRadialMap.comp continuous_subtype_val).subtype_mk _

end LowDimensionalTopology.Geometry.Hyperbolic
