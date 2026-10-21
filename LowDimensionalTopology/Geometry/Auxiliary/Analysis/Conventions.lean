/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Order.Filter.Cofinite


/-!
# Norms, standard domains and elementary analytic notation

Euclidean coordinates give the standard balls, spheres and upper half-spaces.
The remaining definitions expose function composition, intersection nonemptiness
and cofinite eventuality through Mathlib’s corresponding public interfaces.
-/

@[expose] public section

open scoped BigOperators

namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis

universe u v w


abbrev EuclideanCoordinates (n : ℕ) := EuclideanSpace ℝ (Fin n)


noncomputable def euclideanNorm {n : ℕ} (x : EuclideanCoordinates n) : ℝ := ‖x‖


theorem euclideanNorm_eq_sqrt_sum {n : ℕ} (x : EuclideanCoordinates n) :
    euclideanNorm x = Real.sqrt (∑ i, (x i) ^ 2) := by
  simp only [euclideanNorm, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]


noncomputable def positiveSquareRoot (y : ℝ) : ℝ := Real.sqrt y


theorem positiveSquareRoot_pos {y : ℝ} (hy : 0 < y) : 0 < positiveSquareRoot y :=
  Real.sqrt_pos.mpr hy


theorem positiveSquareRoot_sq {y : ℝ} (hy : 0 < y) : positiveSquareRoot y ^ 2 = y :=
  Real.sq_sqrt hy.le


noncomputable def standardBasis (n : ℕ) :
    OrthonormalBasis (Fin n) ℝ (EuclideanCoordinates n) :=
  EuclideanSpace.basisFun (Fin n) ℝ


theorem standardBasis_apply (n : ℕ) (i j : Fin n) :
    standardBasis n i j = if j = i then 1 else 0 := by
  simp [standardBasis, EuclideanSpace.basisFun_apply, PiLp.single_apply]


def openUnitBall (n : ℕ) : Set (EuclideanCoordinates n) := {x | euclideanNorm x < 1}


theorem mem_openUnitBall {n : ℕ} {x : EuclideanCoordinates n} :
    x ∈ openUnitBall n ↔ ‖x‖ < 1 := Iff.rfl


theorem openUnitBall_eq_ball (n : ℕ) :
    openUnitBall n = Metric.ball (0 : EuclideanCoordinates n) 1 := by
  ext x
  simp [openUnitBall, euclideanNorm, Metric.mem_ball, dist_zero_right]

/-- With ambient dimension `n + 1`. -/
def upperHalfSpace (n : ℕ) : Set (EuclideanCoordinates (n + 1)) :=
  {x | 0 < x (Fin.last n)}


theorem mem_upperHalfSpace {n : ℕ} {x : EuclideanCoordinates (n + 1)} :
    x ∈ upperHalfSpace n ↔ 0 < x (Fin.last n) := Iff.rfl

/-- With ambient dimension `n`. -/
def unitSphere (n : ℕ) : Set (EuclideanCoordinates n) := {x | euclideanNorm x = 1}


theorem mem_unitSphere {n : ℕ} {x : EuclideanCoordinates n} :
    x ∈ unitSphere n ↔ ‖x‖ = 1 := Iff.rfl


theorem unitSphere_eq_sphere (n : ℕ) :
    unitSphere n = Metric.sphere (0 : EuclideanCoordinates n) 1 := by
  ext x
  simp [unitSphere, euclideanNorm]


def complexUnitDisc : Set ℂ := {z | ‖z‖ < 1}


theorem mem_complexUnitDisc {z : ℂ} : z ∈ complexUnitDisc ↔ ‖z‖ < 1 := Iff.rfl


theorem complexUnitDisc_eq_ball : complexUnitDisc = Metric.ball (0 : ℂ) 1 := by
  ext z
  simp [complexUnitDisc, Metric.mem_ball, dist_zero_right]


def complexUnitCircle : Set ℂ := {z | ‖z‖ = 1}


theorem mem_complexUnitCircle {z : ℂ} : z ∈ complexUnitCircle ↔ ‖z‖ = 1 := Iff.rfl


theorem complexUnitCircle_eq_sphere : complexUnitCircle = Metric.sphere (0 : ℂ) 1 := by
  ext z
  simp [complexUnitCircle]


theorem frontier_complexUnitDisc :
    frontier complexUnitDisc = complexUnitCircle := by
  rw [complexUnitDisc_eq_ball, complexUnitCircle_eq_sphere]
  exact frontier_ball (0 : ℂ) one_ne_zero


def functionComposition {X : Type u} {Y : Type v} {Z : Type w}
    (f : Y → Z) (g : X → Y) : X → Z := f ∘ g


theorem functionComposition_apply {X : Type u} {Y : Type v} {Z : Type w}
    (f : Y → Z) (g : X → Y) (x : X) : functionComposition f g x = f (g x) := rfl


def setsMeet {X : Type u} (A B : Set X) : Prop := (A ∩ B).Nonempty


theorem setsMeet_iff {X : Type u} {A B : Set X} :
    setsMeet A B ↔ A ∩ B ≠ ∅ := Set.nonempty_iff_ne_empty


def almostAll (p : ℕ → Prop) : Prop := ∀ᶠ n in Filter.cofinite, p n


theorem almostAll_iff_finite_exceptions {p : ℕ → Prop} :
    almostAll p ↔ {n | ¬ p n}.Finite := Filter.eventually_cofinite


theorem almostAll_iff_atTop {p : ℕ → Prop} :
    almostAll p ↔ ∀ᶠ n in Filter.atTop, p n := by
  simp only [almostAll, Nat.cofinite_eq_atTop]

end LowDimensionalTopology.Geometry.Auxiliary.Analysis
