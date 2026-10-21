module

public import LowDimensionalTopology.Geometry.Inversive.Inversions
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The hyperboloid and its tangent spaces

Lorentz vectors consist of one time coordinate and a Euclidean spatial vector.
The hyperboloid is the positive-time sheet on which the Lorentz form is one.
Its tangent vectors are Lorentz-orthogonal to the base point; the negative
Lorentz form is positive on every nonzero tangent vector.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace LowDimensionalTopology.Geometry.Hyperbolic

variable {n : ℕ}

/-- A vector with one time coordinate and `n` Euclidean spatial coordinates. -/
abbrev LorentzVector (n : ℕ) := ℝ × Inversive.Euclidean n

/-- The Lorentz form with positive time direction. -/
def lorentzForm (x y : LorentzVector n) : ℝ := x.1 * y.1 - inner ℝ x.2 y.2

/-- The positive-time sheet of the unit Lorentz quadric. -/
def hyperboloidSet (n : ℕ) : Set (LorentzVector n) :=
  {x | lorentzForm x x = 1 ∧ 0 < x.1}

/-- The Lorentz square is the time square minus the spatial norm square. -/
theorem lorentzForm_self (x : LorentzVector n) :
    lorentzForm x x = x.1 ^ 2 - ‖x.2‖ ^ 2 := by
  simp [lorentzForm, pow_two]

/-- Points on the positive-time sheet of the unit Lorentz quadric. -/
abbrev Hyperboloid (n : ℕ) := hyperboloidSet n

/-- The time square of a hyperboloid point is its spatial norm square plus one. -/
theorem hyperboloid_time_sq (x : Hyperboloid n) : x.val.1 ^ 2 = ‖x.val.2‖ ^ 2 + 1 := by
  have h := x.property.1
  rw [lorentzForm_self] at h
  linarith

/-- Tangent vectors are Lorentz-orthogonal to their hyperboloid base point. -/
def HyperboloidTangent (x : Hyperboloid n) (v : LorentzVector n) : Prop :=
  lorentzForm x.val v = 0

/-- Every point on the positive-time hyperboloid has time coordinate at least one. -/
theorem hyperboloid_time_ge_one (x : Hyperboloid n) : 1 ≤ x.val.1 := by
  have h := hyperboloid_time_sq x
  have hp := x.property.2
  nlinarith [sq_nonneg ‖x.val.2‖]

/-- The negative Lorentz form is positive on nonzero hyperboloid tangent vectors. -/
theorem hyperboloid_tangent_positive (x : Hyperboloid n) (v : LorentzVector n)
    (hv : HyperboloidTangent x v) (hv0 : v ≠ 0) : 0 < -lorentzForm v v := by
  have hxt : 0 < x.val.1 := x.property.2
  have horth : x.val.1 * v.1 = inner ℝ x.val.2 v.2 := by
    have h := hv
    unfold HyperboloidTangent lorentzForm at h
    linarith
  have hvsp : v.2 ≠ 0 := by
    intro hz
    have hvtime : v.1 = 0 := by simpa [hz, hxt.ne'] using horth
    apply hv0
    exact Prod.ext hvtime hz
  have hpos : 0 < ‖v.2‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hvsp)
  have hcs : (inner ℝ x.val.2 v.2) ^ 2 ≤ ‖x.val.2‖ ^ 2 * ‖v.2‖ ^ 2 := by
    have h := abs_real_inner_le_norm x.val.2 v.2
    calc
      _ = |inner ℝ x.val.2 v.2| ^ 2 := (sq_abs _).symm
      _ ≤ (‖x.val.2‖ * ‖v.2‖) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h
      _ = _ := by ring
  have hsq : (x.val.1 * v.1) ^ 2 = (inner ℝ x.val.2 v.2) ^ 2 :=
    congrArg (fun t : ℝ => t ^ 2) horth
  have htime := hyperboloid_time_sq x
  have hineq : ‖v.2‖ ^ 2 ≤ (‖v.2‖ ^ 2 - v.1 ^ 2) * x.val.1 ^ 2 := by
    nlinarith only [hcs, hsq, htime]
  rw [lorentzForm_self]
  by_contra! hn
  have hnonpos : (‖v.2‖ ^ 2 - v.1 ^ 2) * x.val.1 ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  linarith

end LowDimensionalTopology.Geometry.Hyperbolic
