module
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Complex.Angle
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Short angular arcs and positive cones.

The angular circle of period `2 * Real.pi` measures angles between unit complex vectors.
A short closed arc is exactly the nonnegative real span of its two endpoint directions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric InnerProductGeometry
open scoped Topology Classical NNReal ComplexConjugate
local notation "𝔸" => AddCircle (2 * Real.pi)

namespace LowDimensionalTopology.Geometry.Euclidean

instance polygonPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The genuine closed angular arc in the original unit direction circle. -/
def polygonClosedDirectionArc (a : AddCircle (2 * Real.pi)) (r : ℝ) : Set Circle :=
  AddCircle.homeomorphCircle' '' Metric.closedBall a r

theorem circle_exp_endpoint_angle (a : ℝ) {r : ℝ} (hr : 0 ≤ r) (hrπ : r ≤ Real.pi / 2) :
    InnerProductGeometry.angle (Circle.exp (a - r) : ℂ) (Circle.exp (a + r) : ℂ) = 2 * r := by
  rw [InnerProductGeometry.angle, Circle.norm_coe, Circle.norm_coe, one_mul, div_one, Complex.inner]
  have hm : (Circle.exp (a + r) : ℂ) * conj (Circle.exp (a - r) : ℂ) = (Circle.exp (2 * r) : ℂ) := by
    rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← div_eq_mul_inv, ← Circle.exp_sub]
    congr 2
    ring
  rw [hm, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  exact Real.arccos_cos (by positivity) (by linarith)

theorem angularCircle_norm_coe_min {x : ℝ} (hx : |x| ≤ 2 * Real.pi) :
    ‖(x : 𝔸)‖ = min |x| (2 * Real.pi - |x|) := by
  have hp : 0 < 2 * Real.pi := by positivity
  by_cases hshort : |x| ≤ Real.pi
  · have hn : ‖(x : 𝔸)‖ = |x| :=
      (AddCircle.norm_coe_eq_abs_iff _ hp.ne').mpr (by
        rw [abs_of_pos hp]
        linarith)
    rw [hn, min_eq_left (by linarith)]
  · have hlong : Real.pi < |x| := lt_of_not_ge hshort
    rcases le_total 0 x with hx0 | hx0
    · have he : ((x - 2 * Real.pi : ℝ) : 𝔸) = (x : 𝔸) := by
        rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
      have hxl : x ≤ 2 * Real.pi := by rwa [abs_of_nonneg hx0] at hx
      have hxp : Real.pi < x := by rwa [abs_of_nonneg hx0] at hlong
      have hn : ‖((x - 2 * Real.pi : ℝ) : 𝔸)‖ = |x - 2 * Real.pi| :=
        (AddCircle.norm_coe_eq_abs_iff _ hp.ne').mpr (by
          rw [abs_of_pos hp, abs_of_nonpos (by linarith)]
          linarith)
      rw [← he, hn, abs_of_nonpos (by linarith), abs_of_nonneg hx0,
        min_eq_right (by linarith)]
      ring
    · have he : ((x + 2 * Real.pi : ℝ) : 𝔸) = (x : 𝔸) :=
        AddCircle.coe_add_period _ _
      have hxl : -(2 * Real.pi) ≤ x := by
        rw [abs_of_nonpos hx0] at hx
        linarith
      have hxp : x < -Real.pi := by
        rw [abs_of_nonpos hx0] at hlong
        linarith
      have hn : ‖((x + 2 * Real.pi : ℝ) : 𝔸)‖ = |x + 2 * Real.pi| :=
        (AddCircle.norm_coe_eq_abs_iff _ hp.ne').mpr (by
          rw [abs_of_pos hp, abs_of_nonneg (by linarith)]
          linarith)
      rw [← he, hn, abs_of_nonneg (by linarith), abs_of_nonpos hx0,
        min_eq_right (by linarith)]
      ring

theorem circle_angle_eq_angular_dist (x y : Circle) :
    angle (x : ℂ) (y : ℂ) =
      dist (AddCircle.homeomorphCircle'.symm x) (AddCircle.homeomorphCircle'.symm y) := by
  rw [Complex.angle_eq_abs_arg x.coe_ne_zero y.coe_ne_zero, dist_eq_norm]
  change |Complex.arg ((x : ℂ) / (y : ℂ))| =
    ‖((Complex.arg (x : ℂ) : ℝ) : 𝔸) - ((Complex.arg (y : ℂ) : ℝ) : 𝔸)‖
  have harg : ((Complex.arg ((x : ℂ) / (y : ℂ)) : ℝ) : 𝔸) =
      ((Complex.arg (x : ℂ) : ℝ) : 𝔸) - ((Complex.arg (y : ℂ) : ℝ) : 𝔸) :=
    Complex.arg_div_coe_angle x.coe_ne_zero y.coe_ne_zero
  have hn : ‖((Complex.arg ((x : ℂ) / (y : ℂ)) : ℝ) : 𝔸)‖ =
      |Complex.arg ((x : ℂ) / (y : ℂ))| := by
    apply (AddCircle.norm_coe_eq_abs_iff _ (by positivity : 2 * Real.pi ≠ 0)).mpr
    rw [abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    convert Complex.abs_arg_le_pi ((x : ℂ) / (y : ℂ)) using 1; ring
  exact hn.symm.trans (congrArg norm harg)

theorem positiveCone_span_smul_mem_iff {u v x : ℂ} (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    x ∈ Submodule.span ℝ≥0 {a • u, b • v} ↔ x ∈ Submodule.span ℝ≥0 {u, v} := by
  rw [Submodule.mem_span_pair, Submodule.mem_span_pair]
  constructor
  · rintro ⟨r, s, he⟩
    refine ⟨r * ⟨a, ha.le⟩, s * ⟨b, hb.le⟩, ?_⟩
    change ((r : ℝ) * a) • u + ((s : ℝ) * b) • v = x
    rw [mul_smul, mul_smul]
    exact he
  · rintro ⟨r, s, he⟩
    refine ⟨r / ⟨a, ha.le⟩, s / ⟨b, hb.le⟩, ?_⟩
    change ((r : ℝ) / a) • (a • u) + ((s : ℝ) / b) • (b • v) = x
    rw [smul_smul, smul_smul, div_mul_cancel₀ _ ha.ne', div_mul_cancel₀ _ hb.ne']
    exact he

theorem angularCircle_short_arc_geodesic {r : ℝ} (hr : 0 ≤ r)
    (hrπ : r < Real.pi / 2) (x : 𝔸) :
    dist (-(r : 𝔸)) x + dist x (r : 𝔸) = 2 * r ↔ dist x 0 ≤ r := by
  let t : ℝ := Real.Angle.toReal x
  have htx : (t : 𝔸) = x := Real.Angle.coe_toReal x
  have ht : |t| ≤ Real.pi := Real.Angle.abs_toReal_le_pi x
  rw [← htx]
  have hleft : dist (-(r : 𝔸)) (t : 𝔸) = ‖((t + r : ℝ) : 𝔸)‖ := by
    rw [dist_comm, dist_eq_norm, sub_neg_eq_add, ← AddCircle.coe_add]
  rw [hleft, dist_eq_norm, ← AddCircle.coe_sub, dist_zero_right]
  rw [(AddCircle.norm_coe_eq_abs_iff (x := t) _ (by positivity : 2 * Real.pi ≠ 0)).mpr
    (by rw [abs_of_pos (by positivity : 0 < 2 * Real.pi)]; linarith)]
  rw [angularCircle_norm_coe_min (x := t + r) (by
      have := abs_add_le t r
      rw [abs_of_nonneg hr] at this
      linarith),
    angularCircle_norm_coe_min (x := t - r) (by
      have := abs_sub t r
      rw [abs_of_nonneg hr] at this
      linarith)]
  rcases le_total 0 t with ht0 | ht0 <;>
    rcases le_total 0 (t + r) with htp | htp <;>
    rcases le_total 0 (t - r) with htm | htm <;>
    simp_all only [abs_of_nonneg, abs_of_nonpos, min_def] <;>
    split_ifs <;> constructor <;> intro h <;> linarith [Real.pi_pos]

/-- Every proper pair of genuine unit directions is the boundary pair of a true short arc. -/
theorem circle_exists_short_arc_endpoints (u v : Circle)
    (hangle : angle (u : ℂ) (v : ℂ) < Real.pi) :
    ∃ a r : ℝ, 0 ≤ r ∧ r < Real.pi / 2 ∧
      ((u = Circle.exp (a - r) ∧ v = Circle.exp (a + r)) ∨
       (v = Circle.exp (a - r) ∧ u = Circle.exp (a + r))) := by
  have small (x y : Circle) (hxy : angle (x : ℂ) (y : ℂ) < Real.pi)
      (hδ : Circle.angleDiff x y ≤ Real.pi) :
      ∃ a r : ℝ, 0 ≤ r ∧ r < Real.pi / 2 ∧
        x = Circle.exp (a - r) ∧ y = Circle.exp (a + r) := by
    let δ := Circle.angleDiff x y
    let r := δ / 2
    let a := Complex.arg (x : ℂ) + r
    have hr : 0 ≤ r := div_nonneg (Circle.angleDiff_nonneg x y) (by norm_num)
    have hrπ : r ≤ Real.pi / 2 := by dsimp [r, δ]; linarith
    have hx : Circle.exp (a - r) = x := by
      convert Circle.exp_arg x using 1
      congr 1
      dsimp [a]
      ring
    have hy : Circle.exp (a + r) = y := by
      calc
        Circle.exp (a + r) = Circle.exp δ * x := by
          rw [← Circle.exp_arg x, ← Circle.exp_add]
          congr 1
          dsimp [a, r]
          ring
        _ = y := Circle.exp_angleDiff_mul
    have hθ : angle (x : ℂ) (y : ℂ) = 2 * r := by
      rw [← hx, ← hy]
      exact circle_exp_endpoint_angle a hr hrπ
    exact ⟨a, r, hr, by linarith, hx.symm, hy.symm⟩
  by_cases hδ : Circle.angleDiff u v ≤ Real.pi
  · obtain ⟨a, r, hr, hrπ, hu, hv⟩ := small u v hangle hδ
    exact ⟨a, r, hr, hrπ, Or.inl ⟨hu, hv⟩⟩
  · have huv : u ≠ v := by
      intro he
      subst v
      simp [Circle.angleDiff] at hδ
      linarith [Real.pi_pos]
    have hsum := Circle.angleDiff_add_angleDiff huv
    have hδ' : Circle.angleDiff v u ≤ Real.pi := by linarith
    obtain ⟨a, r, hr, hrπ, hv, hu⟩ := small v u (by rwa [angle_comm]) hδ'
    exact ⟨a, r, hr, hrπ, Or.inr ⟨hv, hu⟩⟩

theorem angularCircle_short_arc_centered {r : ℝ} (hr : 0 ≤ r)
    (hrπ : r < Real.pi / 2) (a x : 𝔸) :
    dist (a - (r : 𝔸)) x + dist x (a + (r : 𝔸)) = 2 * r ↔ dist x a ≤ r := by
  have h := angularCircle_short_arc_geodesic hr hrπ (x - a)
  have hL : dist (-(r : 𝔸)) (x - a) = dist (a - (r : 𝔸)) x := by
    simp only [dist_eq_norm]
    congr 1
    abel
  have hR : dist (x - a) (r : 𝔸) = dist x (a + (r : 𝔸)) := by
    simp only [dist_eq_norm]
    congr 1
    abel
  simpa only [hL, hR, dist_zero_right, dist_eq_norm, sub_zero] using h

/-- A true short angular arc consists exactly of the nonnegative span of its boundary rays. -/
theorem circle_mem_positiveCone_endpoints (a : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hrπ : r < Real.pi / 2) (x : Circle) :
    (x : ℂ) ∈ Submodule.span ℝ≥0
      {(Circle.exp (a - r) : ℂ), (Circle.exp (a + r) : ℂ)} ↔
      x ∈ polygonClosedDirectionArc (a : 𝔸) r := by
  have hangle : angle (Circle.exp (a - r) : ℂ) (Circle.exp (a + r) : ℂ) = 2 * r :=
    circle_exp_endpoint_angle a hr hrπ.le
  have he := angle_eq_angle_add_angle_iff
    (x := (Circle.exp (a - r) : ℂ)) (z := (Circle.exp (a + r) : ℂ)) x.coe_ne_zero
  rw [hangle] at he
  have hne : 2 * r ≠ Real.pi := by linarith
  simp only [hne, false_or] at he
  rw [← he, circle_angle_eq_angular_dist, circle_angle_eq_angular_dist]
  have hU : AddCircle.homeomorphCircle'.symm (Circle.exp (a - r)) = ((a - r : ℝ) : 𝔸) :=
    AddCircle.homeomorphCircle'.symm_apply_apply ((a - r : ℝ) : 𝔸)
  have hV : AddCircle.homeomorphCircle'.symm (Circle.exp (a + r)) = ((a + r : ℝ) : 𝔸) :=
    AddCircle.homeomorphCircle'.symm_apply_apply ((a + r : ℝ) : 𝔸)
  rw [hU, hV]
  have hArc : x ∈ polygonClosedDirectionArc (a : 𝔸) r ↔
      dist (AddCircle.homeomorphCircle'.symm x) (a : 𝔸) ≤ r := by
    constructor
    · rintro ⟨y, hy, he⟩
      have hyx : y = AddCircle.homeomorphCircle'.symm x := by
        exact (congrArg AddCircle.homeomorphCircle'.symm he).symm.trans
          (AddCircle.homeomorphCircle'.symm_apply_apply y) |>.symm
      exact hyx ▸ hy
    · intro hx
      exact ⟨AddCircle.homeomorphCircle'.symm x, hx,
        AddCircle.homeomorphCircle'.apply_symm_apply x⟩
  rw [hArc]
  change 2 * r = dist ((a - r : ℝ) : 𝔸) (AddCircle.homeomorphCircle'.symm x) +
      dist (AddCircle.homeomorphCircle'.symm x) ((a + r : ℝ) : 𝔸) ↔
    dist (AddCircle.homeomorphCircle'.symm x) (a : 𝔸) ≤ r
  rw [AddCircle.coe_sub, AddCircle.coe_add, eq_comm]
  exact angularCircle_short_arc_centered hr hrπ _ _

end LowDimensionalTopology.Geometry.Euclidean
