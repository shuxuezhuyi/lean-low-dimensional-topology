/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.CurveLength
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Tactic

/-!
# The equality case for vertical minimizing curves

A continuous piecewise C¹ parametrization may pause while remaining minimizing.
The velocity criterion therefore uses a nonnegative imaginary component. Pieces
with equal parameter endpoints contribute no length and impose no velocity
condition on their singleton parameter sets.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped UpperHalfPlane Topology

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

/-- Equality in the imaginary-component lower bound includes stationary vectors. -/
theorem norm_eq_im_iff (v : ℂ) : ‖v‖ = v.im ↔ v.re = 0 ∧ 0 ≤ v.im := by
  have hsq : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  constructor
  · intro h
    have hn : 0 ≤ v.im := h ▸ norm_nonneg v
    exact ⟨by rw [h] at hsq; nlinarith [sq_nonneg v.re], hn⟩
  · rintro ⟨hr, hi⟩
    rw [hr] at hsq
    nlinarith [norm_nonneg v]

/-- The derivative of the imaginary coordinate is the imaginary velocity. -/
theorem C1CurvePiece.hasDerivWithin_im (c : C1CurvePiece) (t : ℝ) (ht : t ∈ Icc c.a c.b) :
    HasDerivWithinAt (fun s => (c.curve s).im) (c.velocity t).im (Icc c.a c.b) t := by
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t (c.hasDerivWithin t ht)

/-- The derivative of the real coordinate is the real velocity. -/
theorem C1CurvePiece.hasDerivWithin_re (c : C1CurvePiece) (t : ℝ) (ht : t ∈ Icc c.a c.b) :
    HasDerivWithinAt (fun s => (c.curve s).re) (c.velocity t).re (Icc c.a c.b) t := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t (c.hasDerivWithin t ht)

/-- The signed logarithmic height change of a piece. -/
def C1CurvePiece.logHeightChange (c : C1CurvePiece) : ℝ :=
  Real.log (c.curve c.b).im - Real.log (c.curve c.a).im

theorem C1CurvePiece.continuous_logHeightDerivative (c : C1CurvePiece) :
    ContinuousOn (fun t => (c.velocity t).im / (c.curve t).im) (Icc c.a c.b) :=
  (Complex.continuous_im.comp_continuousOn c.continuous_velocity).div
    (UpperHalfPlane.continuous_im.comp_continuousOn c.continuous_curve)
    (fun t _ => (c.curve t).im_ne_zero)

/-- The exact integral of the signed logarithmic height derivative. -/
theorem C1CurvePiece.integral_logHeightDerivative (c : C1CurvePiece) :
    (∫ t in c.a..c.b, (c.velocity t).im / (c.curve t).im) = c.logHeightChange := by
  change _ = Real.log (c.curve c.b).im - Real.log (c.curve c.a).im
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (f := fun t => Real.log (c.curve t).im)
    (f' := fun t => (c.velocity t).im / (c.curve t).im) c.ordered
  · exact (UpperHalfPlane.continuous_im.comp_continuousOn c.continuous_curve).log
      (fun t _ => (c.curve t).im_ne_zero)
  · intro t ht
    exact (((c.hasDerivWithin_im t ⟨ht.1.le, ht.2.le⟩).log (c.curve t).im_ne_zero).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt
  · exact c.continuous_logHeightDerivative.intervalIntegrable_of_Icc c.ordered

/-- Signed logarithmic height change is a lower bound for every piece's genuine length. -/
theorem C1CurvePiece.logHeightChange_le_length (c : C1CurvePiece) :
    c.logHeightChange ≤ c.length := by
  rw [← c.integral_logHeightDerivative, C1CurvePiece.length]
  apply intervalIntegral.integral_mono_on c.ordered
    (c.continuous_logHeightDerivative.intervalIntegrable_of_Icc c.ordered)
    (c.continuous_speed.intervalIntegrable_of_Icc c.ordered)
  intro t _
  exact div_le_div_of_nonneg_right (Complex.im_le_norm (c.velocity t)) (c.curve t).im_pos.le

/-- The corrected velocity condition for an upward vertical piece, including possible pauses. -/
def C1CurvePiece.ForwardVertical (c : C1CurvePiece) : Prop :=
  c.a = c.b ∨ ∀ t ∈ Icc c.a c.b, (c.velocity t).re = 0 ∧ 0 ≤ (c.velocity t).im

/-- Equality of length and signed height change forces, and follows from, vertical forward velocity. -/
theorem C1CurvePiece.length_eq_logHeightChange_iff (c : C1CurvePiece) :
    c.length = c.logHeightChange ↔ c.ForwardVertical := by
  by_cases hab : c.a = c.b
  · simp [C1CurvePiece.length, C1CurvePiece.logHeightChange, C1CurvePiece.ForwardVertical, hab]
  have hab' : c.a < c.b := lt_of_le_of_ne c.ordered hab
  constructor
  · intro heq
    right
    intro t ht
    apply (norm_eq_im_iff (c.velocity t)).mp
    have hle : (c.velocity t).im / (c.curve t).im ≤ weightedSpeed c.curve c.velocity t :=
      div_le_div_of_nonneg_right (Complex.im_le_norm _) (c.curve t).im_pos.le
    have he : (c.velocity t).im / (c.curve t).im = weightedSpeed c.curve c.velocity t := by
      by_contra hne
      have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab'
        c.continuous_logHeightDerivative c.continuous_speed
        (fun s _ => div_le_div_of_nonneg_right (Complex.im_le_norm _) (c.curve s).im_pos.le)
        ⟨t, ht, lt_of_le_of_ne hle hne⟩
      rw [c.integral_logHeightDerivative] at hlt
      change c.logHeightChange < c.length at hlt
      linarith
    have hm := congrArg (fun r : ℝ => r * (c.curve t).im) he.symm
    simpa only [weightedSpeed, div_mul_cancel₀ _ (c.curve t).im_ne_zero] using hm
  · rintro (h | h)
    · exact (hab h).elim
    · rw [← c.integral_logHeightDerivative, C1CurvePiece.length]
      apply intervalIntegral.integral_congr
      intro t ht
      have hn := (norm_eq_im_iff (c.velocity t)).mpr (h t (by simpa [uIcc_of_le c.ordered] using ht))
      exact congrArg (fun r : ℝ => r / (c.curve t).im) hn

/-- The pointwise geometry of every forward piece: one vertical line and no downward motion. -/
theorem C1CurvePiece.ForwardVertical.geometry {c : C1CurvePiece} (h : c.ForwardVertical) :
    (∀ t ∈ Icc c.a c.b, (c.curve t).re = (c.curve c.a).re) ∧
      MonotoneOn (fun t => (c.curve t).im) (Icc c.a c.b) := by
  rcases h with heq | hv
  · have hsingle (t : ℝ) (ht : t ∈ Icc c.a c.b) : t = c.a := by
      have h₁ := ht.1
      have h₂ := ht.2
      linarith
    constructor
    · intro t ht
      rw [hsingle t ht]
    · intro t ht u hu _
      rw [hsingle t ht, hsingle u hu]
  · constructor
    · apply constant_of_has_deriv_right_zero
        (UpperHalfPlane.continuous_re.comp_continuousOn c.continuous_curve)
      intro t ht
      have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t
        (hasDerivWithinAt_right_of_Icc (c.hasDerivWithin t ⟨ht.1, ht.2.le⟩) ht)
      change HasDerivWithinAt (fun s => (c.curve s).re) (c.velocity t).re (Ici t) t at hd
      rw [(hv t ⟨ht.1, ht.2.le⟩).1] at hd
      exact hd
    · apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc c.a c.b)
        (UpperHalfPlane.continuous_im.comp_continuousOn c.continuous_curve)
      · intro t ht
        exact (c.hasDerivWithin_im t (interior_subset ht)).mono interior_subset
      · intro t ht
        exact (hv t (interior_subset ht)).2

/-- A vertical curve with nondecreasing height has exactly the corrected forward velocity. -/
theorem C1CurvePiece.forwardVertical_of_geometry (c : C1CurvePiece)
    (hr : ∀ t ∈ Icc c.a c.b, (c.curve t).re = (c.curve c.a).re)
    (hi : MonotoneOn (fun t => (c.curve t).im) (Icc c.a c.b)) : c.ForwardVertical := by
  by_cases hab : c.a = c.b
  · exact Or.inl hab
  · right
    intro t ht
    have hu := uniqueDiffOn_Icc (lt_of_le_of_ne c.ordered hab) t ht
    have hd₀ : HasDerivWithinAt (fun s => (c.curve s).re) 0 (Icc c.a c.b) t :=
      (hasDerivWithinAt_const t (Icc c.a c.b) (c.curve c.a).re).congr_of_mem hr ht
    constructor
    · exact ((c.hasDerivWithin_re t ht).derivWithin hu).symm.trans (hd₀.derivWithin hu)
    · rw [← (c.hasDerivWithin_im t ht).derivWithin hu]
      exact hi.derivWithin_nonneg

/-- The corrected velocity and geometric criteria are equivalent, including degenerate pieces. -/
theorem C1CurvePiece.forwardVertical_iff_geometry (c : C1CurvePiece) :
    c.ForwardVertical ↔ (∀ t ∈ Icc c.a c.b, (c.curve t).re = (c.curve c.a).re) ∧
      MonotoneOn (fun t => (c.curve t).im) (Icc c.a c.b) :=
  ⟨C1CurvePiece.ForwardVertical.geometry, fun h => c.forwardVertical_of_geometry h.1 h.2⟩

/-- Forward vertical velocity on every nondegenerate piece of a finite concatenation. -/
def PiecewiseC1Curve.ForwardVertical {z w : ℍ} : PiecewiseC1Curve z w → Prop
  | .nil _ => True
  | .cons c tail => c.ForwardVertical ∧ tail.ForwardVertical

/-- The signed height lower bound telescopes across every finite C¹ partition. -/
theorem PiecewiseC1Curve.logHeightChange_le_length {z w : ℍ} (c : PiecewiseC1Curve z w) :
    Real.log w.im - Real.log z.im ≤ c.length := by
  induction c with
  | nil z => simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.length]
  | @cons p w tail ih =>
    have hp := p.logHeightChange_le_length
    change _ ≤ p.length + tail.length
    dsimp [C1CurvePiece.logHeightChange] at hp
    linarith

/-- Equality is characterized for every finite number of smooth pieces, including degenerate ones. -/
theorem PiecewiseC1Curve.length_eq_logHeightChange_iff {z w : ℍ} (c : PiecewiseC1Curve z w) :
    c.length = Real.log w.im - Real.log z.im ↔ c.ForwardVertical := by
  induction c with
  | nil z => simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.length,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.ForwardVertical]
  | @cons p w tail ih =>
    have hp := p.logHeightChange_le_length
    have ht := tail.logHeightChange_le_length
    change p.length + tail.length = _ ↔ p.ForwardVertical ∧ tail.ForwardVertical
    constructor
    · intro heq
      have hpe : p.length = p.logHeightChange := by
        dsimp [C1CurvePiece.logHeightChange] at *
        linarith
      have hte : tail.length = Real.log w.im - Real.log (p.curve p.b).im := by
        dsimp [C1CurvePiece.logHeightChange] at *
        linarith
      exact ⟨p.length_eq_logHeightChange_iff.mp hpe, ih.mp hte⟩
    · rintro ⟨hpf, htf⟩
      rw [p.length_eq_logHeightChange_iff.mpr hpf, ih.mpr htf]
      dsimp [C1CurvePiece.logHeightChange]
      ring

/-- For vertically aligned endpoints in increasing height order, actual distance is signed height change. -/
theorem metric_vertical_distance_of_im_le {z w : ℍ} (hr : z.re = w.re) (hi : z.im ≤ w.im) :
    dist z w = Real.log w.im - Real.log z.im := by
  rw [UpperHalfPlane.dist_of_re_eq hr, Real.dist_eq, abs_of_nonpos]
  · ring
  · exact sub_nonpos.mpr (Real.log_le_log z.im_pos hi)

/-- The corrected minimizing criterion applies to the full piecewise-C¹ class used to define distance. -/
theorem PiecewiseC1Curve.length_eq_dist_iff_forwardVertical {z w : ℍ}
    (c : PiecewiseC1Curve z w) (hr : z.re = w.re) (hi : z.im ≤ w.im) :
    c.length = dist z w ↔ c.ForwardVertical := by
  rw [metric_vertical_distance_of_im_le hr hi]
  exact c.length_eq_logHeightChange_iff

/-- The single-piece version of the corrected minimizing criterion. -/
theorem C1CurvePiece.length_eq_dist_iff_forwardVertical (c : C1CurvePiece)
    (hr : (c.curve c.a).re = (c.curve c.b).re) (hi : (c.curve c.a).im ≤ (c.curve c.b).im) :
    c.length = dist (c.curve c.a) (c.curve c.b) ↔ c.ForwardVertical := by
  rw [metric_vertical_distance_of_im_le hr hi]
  exact c.length_eq_logHeightChange_iff

/-- The geometric description uses a common vertical line and nondecreasing height on each piece. -/
def PiecewiseC1Curve.VerticalNondecreasing {z w : ℍ} (x : ℝ) : PiecewiseC1Curve z w → Prop
  | .nil _ => True
  | .cons c tail => (∀ t ∈ Icc c.a c.b, (c.curve t).re = x) ∧
      MonotoneOn (fun t => (c.curve t).im) (Icc c.a c.b) ∧ tail.VerticalNondecreasing x

theorem PiecewiseC1Curve.ForwardVertical.verticalNondecreasing {z w : ℍ}
    {c : PiecewiseC1Curve z w} (h : c.ForwardVertical) : c.VerticalNondecreasing z.re := by
  induction c with
  | nil z => trivial
  | @cons p w tail ih =>
    rcases h with ⟨hp, ht⟩
    have hg := hp.geometry
    change _ ∧ _ ∧ tail.VerticalNondecreasing (p.curve p.a).re
    refine ⟨hg.1, hg.2, ?_⟩
    have hend := hg.1 p.b (right_mem_Icc.mpr p.ordered)
    simpa only [hend] using ih ht

theorem PiecewiseC1Curve.forwardVertical_of_verticalNondecreasing {z w : ℍ}
    (c : PiecewiseC1Curve z w) (x : ℝ) (h : c.VerticalNondecreasing x) : c.ForwardVertical := by
  induction c with
  | nil z => trivial
  | @cons p w tail ih =>
    rcases h with ⟨hr, hi, ht⟩
    refine ⟨p.forwardVertical_of_geometry ?_ hi, ih ht⟩
    intro t ht
    rw [hr t ht, hr p.a (left_mem_Icc.mpr p.ordered)]

/-- All minimizing vertical paths, across finitely many C¹ pieces, stay vertical and never reverse height. -/
theorem PiecewiseC1Curve.length_eq_dist_iff_verticalNondecreasing {z w : ℍ}
    (c : PiecewiseC1Curve z w) (hr : z.re = w.re) (hi : z.im ≤ w.im) :
    c.length = dist z w ↔ c.VerticalNondecreasing z.re := by
  rw [c.length_eq_dist_iff_forwardVertical hr hi]
  exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.ForwardVertical.verticalNondecreasing,
    c.forwardVertical_of_verticalNondecreasing z.re⟩

theorem PiecewiseC1Curve.append_forwardVertical_iff {x y z : ℍ}
    (c : PiecewiseC1Curve x y) (d : PiecewiseC1Curve y z) :
    (c.append d).ForwardVertical ↔ c.ForwardVertical ∧ d.ForwardVertical := by
  induction c with
  | nil _ => simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.append,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.ForwardVertical]
  | cons p tail ih =>
    change p.ForwardVertical ∧ (tail.append d).ForwardVertical ↔
      (p.ForwardVertical ∧ tail.ForwardVertical) ∧ d.ForwardVertical
    rw [ih d, and_assoc]

/-- The finite-partition adapter retains every piece's equality condition. -/
theorem PartitionedC1Curve.prefix_forwardVertical_iff (c : PartitionedC1Curve)
    (k : ℕ) (hk : k ≤ c.n) :
    (c.prefix k hk).ForwardVertical ↔ ∀ i (hi : i < k),
      (c.piece i (Nat.lt_of_lt_of_le hi hk)).ForwardVertical := by
  induction k with
  | zero => simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PartitionedC1Curve.prefix,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.ForwardVertical]
  | succ k ih =>
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PartitionedC1Curve.prefix]
    erw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve.append_forwardVertical_iff]
    rw [ih (Nat.le_trans (Nat.le_succ k) hk)]
    change (∀ i (hi : i < k), _) ∧ ((c.piece k _).ForwardVertical ∧ True) ↔ _
    constructor
    · rintro ⟨h, hkf, _⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hik | rfl
      · exact h i hik
      · exact hkf
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h k (Nat.lt_succ_self k), trivial⟩

/-- The geometric integral sum, for one global curve with a finite C¹ partition, satisfies the same iff. -/
theorem PartitionedC1Curve.integral_sum_eq_dist_iff_forwardVertical (c : PartitionedC1Curve)
    (hr : (c.curve (c.times 0)).re = (c.curve (c.times c.n)).re)
    (hi : (c.curve (c.times 0)).im ≤ (c.curve (c.times c.n)).im) :
    (∑ i ∈ Finset.range c.n, ∫ t in c.times i..c.times (i + 1),
      weightedSpeed c.curve (c.velocity i) t) =
        dist (c.curve (c.times 0)) (c.curve (c.times c.n)) ↔
      ∀ i (hi : i < c.n), (c.piece i hi).ForwardVertical := by
  rw [← c.prefix_length c.n le_rfl,
    (c.prefix c.n le_rfl).length_eq_dist_iff_forwardVertical hr hi,
    c.prefix_forwardVertical_iff c.n le_rfl]

/-- A genuine smooth vertical curve with a stationary parameter in the interior. -/
def pausedVerticalPiece : C1CurvePiece where
  a := -1
  b := 1
  ordered := by norm_num
  curve t := UpperHalfPlane.mk ((Real.exp (t ^ 3) : ℂ) * Complex.I)
    (by simpa only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, zero_add, add_zero] using Real.exp_pos (t ^ 3))
  velocity t := ((Real.exp (t ^ 3) * (3 * t ^ 2) : ℝ) : ℂ) * Complex.I
  continuous_curve := by
    apply Continuous.continuousOn
    apply Continuous.upperHalfPlaneMk
    fun_prop
  continuous_velocity := by fun_prop
  hasDerivWithin t _ := by
    have hp : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
      convert! (hasDerivAt_id t).pow 3 using 1
      norm_num
    simpa only [UpperHalfPlane.coe_mk] using
      ((hp.exp.ofReal_comp).mul_const Complex.I).hasDerivWithinAt

theorem pausedVerticalPiece_forwardVertical : pausedVerticalPiece.ForwardVertical := by
  right
  intro t _
  simp only [pausedVerticalPiece, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, true_and]
  positivity

theorem pausedVerticalPiece_zero_velocity : pausedVerticalPiece.velocity 0 = 0 := by
  simp [pausedVerticalPiece]

theorem pausedVerticalPiece_minimizing :
    pausedVerticalPiece.length = dist (pausedVerticalPiece.curve pausedVerticalPiece.a)
      (pausedVerticalPiece.curve pausedVerticalPiece.b) := by
  have hr := (pausedVerticalPiece_forwardVertical.geometry.1 pausedVerticalPiece.b
    (right_mem_Icc.mpr pausedVerticalPiece.ordered)).symm
  have hi := pausedVerticalPiece_forwardVertical.geometry.2
    (left_mem_Icc.mpr pausedVerticalPiece.ordered)
    (right_mem_Icc.mpr pausedVerticalPiece.ordered) pausedVerticalPiece.ordered
  exact (pausedVerticalPiece.length_eq_dist_iff_forwardVertical hr hi).mpr
    pausedVerticalPiece_forwardVertical

/-- The source's strict-positivity condition fails even at an interior parameter of a smooth minimizer. -/
theorem exists_minimizing_vertical_piece_with_interior_zero_velocity :
    ∃ c : C1CurvePiece, c.a < 0 ∧ 0 < c.b ∧
      (c.curve c.a).im < (c.curve c.b).im ∧
      c.length = dist (c.curve c.a) (c.curve c.b) ∧ c.velocity 0 = 0 := by
  refine ⟨pausedVerticalPiece, by norm_num [pausedVerticalPiece],
    by norm_num [pausedVerticalPiece], ?_, pausedVerticalPiece_minimizing,
    pausedVerticalPiece_zero_velocity⟩
  simp only [pausedVerticalPiece, UpperHalfPlane.mk_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
  exact Real.exp_lt_exp.mpr (by norm_num)

end

end LowDimensionalTopology.Geometry.Hyperbolic
