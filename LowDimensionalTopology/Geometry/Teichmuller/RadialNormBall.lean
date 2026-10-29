module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# A radius-preserving change of norm coordinates

A continuous real linear equivalence induces a homeomorphism that preserves
norms and positive rays. Restriction gives the actual open-unit-ball
homeomorphism used to transport the book L1 quadratic-differential parameters.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open Filter Metric Set
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Normalize the coordinate image while retaining the original radius. -/
def radialNormMap (e : E ≃L[ℝ] F) (x : E) : F :=
  (‖x‖ / ‖e x‖) • e x

@[simp] theorem radialNormMap_zero (e : E ≃L[ℝ] F) : radialNormMap e 0 = 0 := by
  simp [radialNormMap]

/-- The coordinate radius is the original norm, exactly. -/
@[simp] theorem norm_radialNormMap (e : E ≃L[ℝ] F) (x : E) :
    ‖radialNormMap e x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hex : e x ≠ 0 := fun h => hx ((e.map_eq_zero_iff).mp h)
  rw [radialNormMap, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hex)

/-- A nonzero input gives a strictly positive rescaling of its linear image. -/
theorem radialNormMap_factor_pos (e : E ≃L[ℝ] F) {x : E} (hx : x ≠ 0) :
    0 < ‖x‖ / ‖e x‖ :=
  div_pos (norm_pos_iff.mpr hx)
    (norm_pos_iff.mpr (fun h => hx ((e.map_eq_zero_iff).mp h)))

/-- Continuity at the origin follows from the exact preserved norm. -/
theorem continuous_radialNormMap (e : E ≃L[ℝ] F) : Continuous (radialNormMap e) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x = 0
  · subst x
    change Tendsto (radialNormMap e) (𝓝 (0 : E)) (𝓝 (radialNormMap e 0))
    rw [radialNormMap_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_radialNormMap, norm_zero] using
      (continuous_norm.tendsto (0 : E))
  · have hex : e x ≠ 0 := fun h => hx ((e.map_eq_zero_iff).mp h)
    exact ((continuous_norm.continuousAt : ContinuousAt (norm : E → ℝ) x).div
      e.continuous.continuousAt.norm (norm_ne_zero_iff.mpr hex)).smul
        e.continuous.continuousAt

/-- Applying the inverse coordinate normalization recovers the same input. -/
theorem radialNormMap_symm_apply (e : E ≃L[ℝ] F) (x : E) :
    radialNormMap e.symm (radialNormMap e x) = x := by
  by_cases hx : x = 0
  · simp [hx]
  let a : ℝ := ‖x‖ / ‖e x‖
  have ha : 0 < a := radialNormMap_factor_pos e hx
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have he : e.symm (radialNormMap e x) = a • x := by
    change e.symm (a • e x) = a • x
    rw [map_smul, e.symm_apply_apply]
  change (‖radialNormMap e x‖ / ‖e.symm (radialNormMap e x)‖) •
    e.symm (radialNormMap e x) = x
  rw [norm_radialNormMap, he, norm_smul, Real.norm_eq_abs, abs_of_pos ha, smul_smul]
  have hc : (‖x‖ / (a * ‖x‖)) * a = 1 := by
    field_simp [ha.ne', hn]
  rw [hc, one_smul]

/-- The actual continuous change of norm coordinates, preserving every radius. -/
def radialNormHomeomorph (e : E ≃L[ℝ] F) : E ≃ₜ F where
  toFun := radialNormMap e
  invFun := radialNormMap e.symm
  left_inv := radialNormMap_symm_apply e
  right_inv := radialNormMap_symm_apply e.symm
  continuous_toFun := continuous_radialNormMap e
  continuous_invFun := continuous_radialNormMap e.symm

/-- The literal open unit balls are homeomorphic by the radius-preserving map. -/
def radialUnitBallHomeomorph (e : E ≃L[ℝ] F) :
    ↥(ball (0 : E) 1) ≃ₜ ↥(ball (0 : F) 1) :=
  (radialNormHomeomorph e).subtype fun x => by
    change x ∈ ball (0 : E) 1 ↔ radialNormMap e x ∈ ball (0 : F) 1
    simp only [mem_ball_zero_iff, norm_radialNormMap]

end LowDimensionalTopology.Geometry.Teichmuller
