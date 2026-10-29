module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.UnitInterval

/-!
# The full-turn homeomorphism of the standard closed annulus

The genuine unit-circle coordinate turns once across the closed unit interval.
The two boundary circles are fixed pointwise. An ambient surface extension and
orientation statement are separate constructions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

/-- One full positive twist of the actual standard closed annulus. -/
def dehnAnnulusHomeomorph : Circle × unitInterval ≃ₜ Circle × unitInterval where
  toFun p := (p.1 * Circle.exp (2 * Real.pi * (p.2 : ℝ)), p.2)
  invFun p := (p.1 * Circle.exp (-(2 * Real.pi * (p.2 : ℝ))), p.2)
  left_inv p := by
    apply Prod.ext
    · simp [Circle.exp_neg, mul_assoc]
    · rfl
  right_inv p := by
    apply Prod.ext
    · simp [Circle.exp_neg, mul_assoc]
    · rfl
  continuous_toFun :=
    (continuous_fst.mul (Circle.exp.continuous.comp
      (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))).prodMk
      continuous_snd
  continuous_invFun :=
    (continuous_fst.mul (Circle.exp.continuous.comp
      (continuous_const.mul (continuous_subtype_val.comp continuous_snd)).neg)).prodMk
      continuous_snd

/-- The forward formula in the genuine circle and interval coordinates. -/
@[simp] theorem dehnAnnulusHomeomorph_apply (s : Circle) (t : unitInterval) :
    dehnAnnulusHomeomorph (s, t) =
      (s * Circle.exp (2 * Real.pi * (t : ℝ)), t) := rfl

/-- The inverse makes the same full turn in the opposite direction. -/
@[simp] theorem dehnAnnulusHomeomorph_symm_apply (s : Circle) (t : unitInterval) :
    dehnAnnulusHomeomorph.symm (s, t) =
      (s * Circle.exp (-(2 * Real.pi * (t : ℝ))), t) := rfl

/-- The lower boundary circle is fixed pointwise. -/
@[simp] theorem dehnAnnulusHomeomorph_apply_zero (s : Circle) :
    dehnAnnulusHomeomorph (s, (0 : unitInterval)) = (s, (0 : unitInterval)) := by
  simp

/-- The upper boundary circle is fixed pointwise after the full turn. -/
@[simp] theorem dehnAnnulusHomeomorph_apply_one (s : Circle) :
    dehnAnnulusHomeomorph (s, (1 : unitInterval)) = (s, (1 : unitInterval)) := by
  simp

end LowDimensionalTopology.Geometry.Surfaces
