module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The Poincaré length density on a normed unit ball

The same scalar factor is used for the complex disk and the real Euclidean
ball of every dimension. Its formula is retained on the whole ambient space;
positivity is asserted only inside the open unit ball. Squaring this length
factor gives the planar area coefficient and the Riemannian tensor coefficient.
No metric, norm or Riemannian-bundle instance is introduced here.
-/

@[expose] public section
noncomputable section

open Set Metric

namespace LowDimensionalTopology.Geometry.Hyperbolic

variable {E : Type*} [NormedAddCommGroup E]

/-- The scalar length factor of the Poincaré unit-ball model. -/
def poincareLengthDensity (x : E) : ℝ := 2 / (1 - ‖x‖ ^ 2)

theorem poincareLengthDensity_pos {x : E} (hx : ‖x‖ < 1) :
    0 < poincareLengthDensity x := by
  unfold poincareLengthDensity
  exact div_pos (by norm_num) (by nlinarith [norm_nonneg x])

theorem continuousOn_poincareLengthDensity :
    ContinuousOn (poincareLengthDensity : E → ℝ) (Metric.ball 0 1) := by
  unfold poincareLengthDensity
  apply continuousOn_const.div
    (continuousOn_const.sub (continuous_norm.continuousOn.pow 2))
  intro x hx
  have hnorm : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  have hden : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  exact hden.ne'

/-- Multiplying the common scalar by a Euclidean speed gives the usual line element. -/
theorem poincareLengthDensity_mul_norm (x v : E) :
    poincareLengthDensity x * ‖v‖ = 2 * ‖v‖ / (1 - ‖x‖ ^ 2) := by
  unfold poincareLengthDensity
  ring

/-- In two real dimensions the area coefficient is the square of the length factor. -/
theorem poincareLengthDensity_sq (x : E) :
    poincareLengthDensity x ^ 2 = 4 / (1 - ‖x‖ ^ 2) ^ 2 := by
  rw [poincareLengthDensity, div_pow]
  norm_num

theorem poincareLengthDensity_eq_of_norm_eq
    {F : Type*} [NormedAddCommGroup F] {x : E} {y : F} (h : ‖x‖ = ‖y‖) :
    poincareLengthDensity x = poincareLengthDensity y := by
  simp only [poincareLengthDensity, h]

end LowDimensionalTopology.Geometry.Hyperbolic
