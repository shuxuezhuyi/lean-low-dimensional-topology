module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticNaturalCoordinate
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Natural-coordinate sectors on the original surface

The retained coordinate has a concrete open strip as target. Its inverse
parametrization lands on the original surface, and exponential projection gives
the flat primitive while keeping the unwrapped angle separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

/-- The shifted slit chart has the usual exponential as its forward function. -/
theorem quadraticSlitExponential_apply (u : ℂ) :
    quadraticSlitExponential u = Complex.exp u := by
  change (-1 : ℂ) * Complex.exp (-((Real.pi : ℂ) * Complex.I) + u) = Complex.exp u
  rw [Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- The slit exponential retains angles strictly between zero and a full turn. -/
theorem quadraticSlitExponential_mem_source (u : ℂ) :
    u ∈ quadraticSlitExponential.source ↔ 0 < u.im ∧ u.im < 2 * Real.pi := by
  change (u ∈ (univ : Set ℂ) ∧
    (-((Real.pi : ℂ) * Complex.I) + u).im ∈ Ioo (-Real.pi) Real.pi) ↔ _
  simp only [mem_univ, true_and, mem_Ioo, Complex.add_im, Complex.neg_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private theorem exp_mem_ball_iff {r : ℝ} (hr : 0 < r) (u : ℂ) :
    Complex.exp u ∈ Metric.ball (0 : ℂ) r ↔ u.re < Real.log r := by
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
  calc
    Real.exp u.re < r ↔ Real.exp u.re < Real.exp (Real.log r) := by
      rw [Real.exp_log hr]
    _ ↔ u.re < Real.log r := Real.exp_lt_exp

namespace QuadraticNaturalCoordinateData

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X}
    {q : HolomorphicQuadraticDifferential R.toRiemannAtlas} {p : X}
    (D : QuadraticNaturalCoordinateData R q p)

/-- The ordinary neighborhood is centred at the original point and has the
chosen ordinary disk as its exact target. -/
theorem ordinaryNeighborhood_data :
    p ∈ D.ordinaryNeighborhood.source ∧ D.ordinaryNeighborhood p = 0 ∧
      D.ordinaryNeighborhood.target = Metric.ball (0 : ℂ) D.radius := by
  let := R.toRiemannAtlas.toChartedSpace
  let A : OpenPartialHomeomorph X ℂ := (chartAt ℂ p).trans D.ordinaryChart
  have hball : Metric.ball (0 : ℂ) D.radius ⊆ A.target := by
    intro w hw
    change w ∈ D.ordinaryChart.target ∧
      D.ordinaryChart.symm w ∈ (chartAt ℂ p).target
    exact ⟨D.disk_target hw,
      D.normal.source_sub (D.ordinaryChart.map_target (D.disk_target hw))⟩
  have hp : p ∈ A.source := by
    change p ∈ (chartAt ℂ p).source ∧ chartAt ℂ p p ∈ D.ordinaryChart.source
    exact ⟨mem_chart_source ℂ p, D.normal.center⟩
  have h0 : A p = 0 := D.normal.natural.2.1
  refine ⟨?_, ?_, ?_⟩
  · change p ∈ A.source ∧ A p ∈ interior (Metric.ball (0 : ℂ) D.radius)
    refine ⟨hp, ?_⟩
    rw [Metric.isOpen_ball.interior_eq, h0]
    exact Metric.mem_ball_self D.radius_pos
  · change A p = 0
    exact h0
  · ext w
    change (w ∈ A.target ∧ w ∈ interior (Metric.ball (0 : ℂ) D.radius)) ↔ _
    rw [Metric.isOpen_ball.interior_eq]
    exact ⟨And.right, fun hw => ⟨hball hw, hw⟩⟩

/-- At a positive-order zero the retained target is the unwrapped sector, and
the explicit logarithmic parametrization has the stated original-surface values. -/
theorem zeroSector_coordinates (hm : 0 < D.order) :
    D.retainedCoordinate.target = D.spreadTarget ∧
      ∀ u : D.sourceLogStrip,
        D.sourceLogProjection u ∈ D.retainedCoordinate.source ∧
          D.retainedCoordinate (D.sourceLogProjection u) =
            (D.exponent : ℂ) * (u : ℂ) ∧
          D.projectedCoordinate (D.sourceLogProjection u) =
            Complex.exp ((D.exponent : ℂ) * (u : ℂ)) := by
  let A := D.ordinaryNeighborhood
  let c : ℂ := ((D.order + 2 : ℕ) : ℂ) / 2
  have hc : c ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (D.order + 1))) two_ne_zero
  let M := Homeomorph.mulLeft₀ c hc
  let B := (A.trans quadraticSlitExponential.symm).transHomeomorph M
  have hB : D.retainedCoordinate = B := by
    change (if D.order = 0 then A else B) = B
    exact ite_eq_right (Nat.ne_of_gt hm)
  have htarget : A.target = Metric.ball (0 : ℂ) D.radius :=
    (ordinaryNeighborhood_data D).2.2
  have hpos : 0 < D.exponent := by
    dsimp [exponent]
    positivity
  have hcast : c = (D.exponent : ℂ) := by
    simp only [c, exponent, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  have hre (v : ℂ) : (c⁻¹ * v).re = v.re / D.exponent := by
    rw [hcast, ← Complex.ofReal_inv]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    simpa only [div_eq_mul_inv] using mul_comm (D.exponent)⁻¹ v.re
  have him (v : ℂ) : (c⁻¹ * v).im = v.im / D.exponent := by
    rw [hcast, ← Complex.ofReal_inv]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    simpa only [div_eq_mul_inv] using mul_comm (D.exponent)⁻¹ v.im
  have hangle : ((D.order + 2 : ℕ) : ℝ) * Real.pi = 2 * Real.pi * D.exponent := by
    dsimp [exponent]
    ring
  constructor
  · rw [hB]
    ext v
    change (c⁻¹ * v ∈ quadraticSlitExponential.source ∧
      quadraticSlitExponential (c⁻¹ * v) ∈ A.target) ↔ v ∈ D.spreadTarget
    rw [quadraticSlitExponential_mem_source, quadraticSlitExponential_apply, htarget,
      exp_mem_ball_iff D.radius_pos, hre, him]
    change ((0 < v.im / D.exponent ∧ v.im / D.exponent < 2 * Real.pi) ∧
      v.re / D.exponent < Real.log D.radius) ↔
        v.re < D.exponent * Real.log D.radius ∧
          0 < v.im ∧ v.im < ((D.order + 2 : ℕ) : ℝ) * Real.pi
    rw [div_pos_iff_of_pos_right hpos, div_lt_iff₀ hpos, div_lt_iff₀' hpos, hangle]
    constructor
    · rintro ⟨⟨hi, ha⟩, hr⟩
      exact ⟨hr, hi, ha⟩
    · rintro ⟨hr, hi, ha⟩
      exact ⟨⟨hi, ha⟩, hr⟩
  · intro u
    have hu : (u : ℂ).re < Real.log D.radius ∧
        0 < (u : ℂ).im ∧ (u : ℂ).im < 2 * Real.pi := u.property
    have huE : (u : ℂ) ∈ quadraticSlitExponential.source :=
      (quadraticSlitExponential_mem_source u).2 hu.2
    have hexp : Complex.exp (u : ℂ) ∈ A.target := by
      rw [htarget]
      exact (exp_mem_ball_iff D.radius_pos u).2 hu.1
    have hP : D.sourceLogProjection u = A.symm (Complex.exp (u : ℂ)) := rfl
    have hAu : A (D.sourceLogProjection u) = Complex.exp (u : ℂ) := by
      rw [hP]
      exact A.right_inv hexp
    have hE : quadraticSlitExponential.symm (Complex.exp (u : ℂ)) = (u : ℂ) := by
      rw [← quadraticSlitExponential_apply u]
      exact quadraticSlitExponential.left_inv huE
    have hmem : D.sourceLogProjection u ∈ D.retainedCoordinate.source := by
      rw [hB]
      change D.sourceLogProjection u ∈ A.source ∧
        A (D.sourceLogProjection u) ∈ quadraticSlitExponential.target
      refine ⟨?_, ?_⟩
      · rw [hP]
        exact A.map_target hexp
      · rw [hAu, ← quadraticSlitExponential_apply u]
        exact quadraticSlitExponential.map_source huE
    have hret : D.retainedCoordinate (D.sourceLogProjection u) =
        (D.exponent : ℂ) * (u : ℂ) := by
      rw [hB]
      change c * quadraticSlitExponential.symm (A (D.sourceLogProjection u)) = _
      rw [hAu, hE, hcast]
    refine ⟨hmem, hret, ?_⟩
    change D.targetProjection (D.retainedCoordinate (D.sourceLogProjection u)) = _
    rw [targetProjection, ite_eq_right (Nat.ne_of_gt hm), hret]

end QuadraticNaturalCoordinateData
end LowDimensionalTopology.Geometry.Teichmuller
